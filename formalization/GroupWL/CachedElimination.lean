import GroupWL.CoordinateElimination
import Mathlib.Data.Vector.Basic

/-! Kernel coordinates with materialized coefficient arrays at every stage.
The recursive maps capture finite arrays rather than repeatedly evaluating
the chain of earlier coordinate substitutions. -/
namespace GroupWL.CachedElimination

open CoordinateElimination
open scoped BigOperators

variable {F : Type*} [Field F] [DecidableEq F]

abbrev MatrixData (m n : ℕ) := Vector (Vector F n) m

def toLinear {m n : ℕ} (A : MatrixData (F := F) m n) :
    (Fin n → F) →ₗ[F] (Fin m → F) where
  toFun x i := ∑ j, A[i][j] * x j
  map_add' x y := by funext i; simp [mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring

def ofLinear {m n : ℕ} (f : (Fin n → F) →ₗ[F] (Fin m → F)) : MatrixData (F := F) m n :=
  Vector.ofFn (fun i => Vector.ofFn (fun j => f (Pi.single j 1) i))

@[simp] theorem ofLinear_entry {m n : ℕ} (f : (Fin n → F) →ₗ[F] (Fin m → F))
    (i : Fin m) (j : Fin n) : (ofLinear f)[i][j] = f (Pi.single j 1) i := by
  simp [ofLinear]

@[simp] theorem toLinear_ofLinear {m n : ℕ} (f : (Fin n → F) →ₗ[F] (Fin m → F)) :
    toLinear (ofLinear f) = f := by
  apply LinearMap.ext
  intro x
  have hx : x = ∑ j, x j • Pi.single j (1 : F) := by
    funext i
    simp [Pi.single_apply]
  funext i
  change (∑ j, (ofLinear f)[i][j] * x j) = f x i
  conv_rhs => rw [hx]
  simp [ofLinear, map_sum, map_smul, mul_comm]

/-- Retain exactly the same chart, replacing its executable maps by finite arrays. -/
def materialize {n : ℕ} {P : Submodule F (Fin n → F)} (D : Chart n P) : Chart n P where
  width := D.width
  width_le := D.width_le
  lift := toLinear (ofLinear D.lift)
  lower := toLinear (ofLinear D.lower)
  lower_lift x := by simpa using D.lower_lift x
  lift_lower x hx := by simpa using D.lift_lower x hx
  lift_mem x := by simpa using D.lift_mem x

@[simp] theorem materialize_width {n : ℕ} {P : Submodule F (Fin n → F)} (D : Chart n P) :
    (materialize D).width = D.width := rfl

@[simp] theorem materialize_lift {n : ℕ} {P : Submodule F (Fin n → F)} (D : Chart n P) :
    (materialize D).lift = D.lift := toLinear_ofLinear D.lift

@[simp] theorem materialize_lower {n : ℕ} {P : Submodule F (Fin n → F)} (D : Chart n P) :
    (materialize D).lower = D.lower := toLinear_ofLinear D.lower

/-- Every recursive result is cached before it is used to eliminate the next row. -/
def kernelChart : (m n : ℕ) →
    (f : (Fin n → F) →ₗ[F] (Fin m → F)) → Chart n (LinearMap.ker f)
  | 0, n, f => materialize
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
      let R := materialize (rowChart D.width h)
      materialize
        { width := R.width
          width_le := R.width_le.trans D.width_le
          lift := D.lift.comp R.lift
          lower := R.lower.comp D.lower
          lower_lift := by
            intro x
            change R.lower (D.lower (D.lift (R.lift x))) = x
            rw [D.lower_lift, R.lower_lift]
          lift_lower := by
            intro x hx
            have hg : x ∈ LinearMap.ker g := by
              change (tailMap m) (f x) = 0
              change f x = 0 at hx
              rw [hx, map_zero]
            have hh : D.lower x ∈ LinearMap.ker h := by
              change f (D.lift (D.lower x)) 0 = 0
              rw [D.lift_lower x hg]
              change f x = 0 at hx
              rw [hx]; rfl
            change D.lift (R.lift (R.lower (D.lower x))) = x
            rw [R.lift_lower _ hh, D.lift_lower x hg]
          lift_mem := by
            intro x
            change f (D.lift (R.lift x)) = 0
            funext i
            refine Fin.cases ?_ (fun j => ?_) i
            · exact R.lift_mem x
            · exact congrFun (D.lift_mem (R.lift x)) j }

def kernelCoordinates {m n : ℕ} (f : (Fin n → F) →ₗ[F] (Fin m → F)) :
    LinearMap.ker f ≃ₗ[F] (Fin (kernelChart m n f).width → F) := (kernelChart m n f).equiv

theorem kernelCoordinates_width_le {m n : ℕ} (f : (Fin n → F) →ₗ[F] (Fin m → F)) :
    (kernelChart m n f).width ≤ n := (kernelChart m n f).width_le

/-- Matrix input version evaluates no external coefficient function during elimination. -/
def matrixKernelChart {m n : ℕ} (A : MatrixData (F := F) m n) : Chart n (LinearMap.ker (toLinear A)) :=
  kernelChart m n (toLinear A)

end GroupWL.CachedElimination
