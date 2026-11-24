import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

/-! Constructive coordinates for kernels of finite systems of field equations.
The recursion uses only equality tests and field arithmetic; it does not select
a basis by classical choice. -/
namespace GroupWL.CoordinateElimination

variable {F : Type*} [Field F] [DecidableEq F]

def tailMap (n : ℕ) : (Fin (n+1) → F) →ₗ[F] (Fin n → F) :=
  LinearMap.pi (fun i => LinearMap.proj i.succ)

@[simp] theorem tailMap_apply (n : ℕ) (x : Fin (n+1) → F) : tailMap n x = Fin.tail x := rfl

def consMap {U : Type*} [AddCommGroup U] [Module F U] {n : ℕ}
    (f : U →ₗ[F] F) (g : U →ₗ[F] (Fin n → F)) : U →ₗ[F] (Fin (n+1) → F) where
  toFun x := Fin.cons (f x) (g x)
  map_add' x y := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' a x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

@[simp] theorem consMap_apply {U : Type*} [AddCommGroup U] [Module F U] {n : ℕ}
    (f : U →ₗ[F] F) (g : U →ₗ[F] (Fin n → F)) (x : U) :
    consMap f g x = Fin.cons (f x) (g x) := rfl

def zeroCons (n : ℕ) : (Fin n → F) →ₗ[F] (Fin (n+1) → F) := consMap 0 LinearMap.id

theorem apply_cons {n : ℕ} (f : (Fin (n+1) → F) →ₗ[F] F) (a : F) (x : Fin n → F) :
    f (Fin.cons a x) = a * f (Fin.cons 1 0) + f (Fin.cons 0 x) := by
  have h : Fin.cons a x = a • Fin.cons (1 : F) (0 : Fin n → F) + Fin.cons 0 x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  rw [h,map_add,map_smul]
  rfl

/-- An injective coordinate parametrization, with its explicit left inverse. -/
structure Chart (n : ℕ) (P : Submodule F (Fin n → F)) where
  width : ℕ
  width_le : width ≤ n
  lift : (Fin width → F) →ₗ[F] (Fin n → F)
  lower : (Fin n → F) →ₗ[F] (Fin width → F)
  lower_lift : ∀ x, lower (lift x) = x
  lift_lower : ∀ x, x ∈ P → lift (lower x) = x
  lift_mem : ∀ x, lift x ∈ P

def Chart.equiv {n : ℕ} {P : Submodule F (Fin n → F)} (D : Chart n P) :
    P ≃ₗ[F] (Fin D.width → F) where
  toFun x := D.lower x
  invFun x := ⟨D.lift x,D.lift_mem x⟩
  left_inv x := Subtype.ext (D.lift_lower x x.property)
  right_inv := D.lower_lift
  map_add' x y := D.lower.map_add x y
  map_smul' a x := D.lower.map_smul a x

/-- Eliminate one equation, scanning its coefficients from left to right. -/
def rowChart : (n : ℕ) → (f : (Fin n → F) →ₗ[F] F) → Chart n (LinearMap.ker f)
  | 0, f =>
      { width := 0
        width_le := le_rfl
        lift := LinearMap.id
        lower := LinearMap.id
        lower_lift := fun _ => rfl
        lift_lower := fun _ _ => rfl
        lift_mem := by
          intro x
          change f x = 0
          have hx : x = 0 := Subsingleton.elim _ _
          rw [hx,f.map_zero] }
  | n+1, f =>
      let a := f (Fin.cons 1 0)
      let g := f.comp (zeroCons n)
      if ha : a = 0 then
        let D := rowChart n g
        { width := D.width+1
          width_le := Nat.succ_le_succ D.width_le
          lift := consMap (LinearMap.proj 0) (D.lift.comp (tailMap D.width))
          lower := consMap (LinearMap.proj 0) (D.lower.comp (tailMap n))
          lower_lift := by
            intro x
            change Fin.cons (x 0) (D.lower (D.lift (Fin.tail x))) = x
            rw [D.lower_lift,Fin.cons_self_tail]
          lift_lower := by
            intro x hx
            change Fin.cons (x 0) (D.lift (D.lower (Fin.tail x))) = x
            have hg : Fin.tail x ∈ LinearMap.ker g := by
              change g (Fin.tail x) = 0
              have hx' : f x = 0 := hx
              rw [← Fin.cons_self_tail x,apply_cons] at hx'
              simpa [a,g,zeroCons,ha] using hx'
            rw [D.lift_lower _ hg,Fin.cons_self_tail]
          lift_mem := by
            intro x
            change f (Fin.cons (x 0) (D.lift (Fin.tail x))) = 0
            rw [apply_cons]
            have hg : g (D.lift (Fin.tail x)) = 0 := D.lift_mem _
            simpa [a,g,zeroCons,ha] using hg }
      else
        { width := n
          width_le := Nat.le_succ n
          lift := consMap ((-a⁻¹) • g) LinearMap.id
          lower := tailMap n
          lower_lift := by intro x; funext i; rfl
          lift_lower := by
            intro x hx
            change Fin.cons (-a⁻¹ * g (Fin.tail x)) (Fin.tail x) = x
            have hx' : f x = 0 := hx
            rw [← Fin.cons_self_tail x,apply_cons] at hx'
            have hfirst : -a⁻¹ * g (Fin.tail x) = x 0 := by
              change x 0 * a + g (Fin.tail x) = 0 at hx'
              field_simp
              linear_combination -hx'
            rw [hfirst,Fin.cons_self_tail]
          lift_mem := by
            intro x
            change f (Fin.cons (-a⁻¹ * g x) x) = 0
            rw [apply_cons]
            change (-a⁻¹ * g x) * a + g x = 0
            field_simp
            ring }

/-- Repeated elimination gives coordinates for an arbitrary finite linear
system, including rank-deficient and zero-dimensional systems. -/
def kernelChart : (m n : ℕ) →
    (f : (Fin n → F) →ₗ[F] (Fin m → F)) → Chart n (LinearMap.ker f)
  | 0, n, f =>
      { width := n
        width_le := le_rfl
        lift := LinearMap.id
        lower := LinearMap.id
        lower_lift := fun _ => rfl
        lift_lower := fun _ _ => rfl
        lift_mem := by intro x; exact Subsingleton.elim _ _ }
  | m+1, n, f =>
      let g := (tailMap m).comp f
      let D := kernelChart m n g
      let h := (LinearMap.proj 0).comp (f.comp D.lift)
      let R := rowChart D.width h
      { width := R.width
        width_le := R.width_le.trans D.width_le
        lift := D.lift.comp R.lift
        lower := R.lower.comp D.lower
        lower_lift := by
          intro x
          change R.lower (D.lower (D.lift (R.lift x))) = x
          rw [D.lower_lift,R.lower_lift]
        lift_lower := by
          intro x hx
          have hg : x ∈ LinearMap.ker g := by
            change (tailMap m) (f x) = 0
            change f x = 0 at hx
            rw [hx,map_zero]
          have hh : D.lower x ∈ LinearMap.ker h := by
            change f (D.lift (D.lower x)) 0 = 0
            rw [D.lift_lower x hg]
            change f x = 0 at hx
            rw [hx]; rfl
          change D.lift (R.lift (R.lower (D.lower x))) = x
          rw [R.lift_lower _ hh,D.lift_lower x hg]
        lift_mem := by
          intro x
          change f (D.lift (R.lift x)) = 0
          funext i
          refine Fin.cases ?_ (fun j => ?_) i
          · exact R.lift_mem x
          · have hg : g (D.lift (R.lift x)) = 0 := D.lift_mem (R.lift x)
            exact congrFun hg j }

/-- The computed coordinate count is exactly nullity, not just a spanning set. -/
theorem Chart.width_eq_finrank {n : ℕ} {P : Submodule F (Fin n → F)} (D : Chart n P) :
    D.width = Module.finrank F P := by
  have h := D.equiv.finrank_eq
  simpa only [Module.finrank_pi,Fintype.card_fin] using h.symm

/-- A basis with explicit computable forward and inverse coordinate maps. -/
def kernelCoordinates {m n : ℕ} (f : (Fin n → F) →ₗ[F] (Fin m → F)) :
    LinearMap.ker f ≃ₗ[F] (Fin (kernelChart m n f).width → F) :=
  (kernelChart m n f).equiv

theorem kernelCoordinates_width_le {m n : ℕ} (f : (Fin n → F) →ₗ[F] (Fin m → F)) :
    (kernelChart m n f).width ≤ n := (kernelChart m n f).width_le

end GroupWL.CoordinateElimination
