import GroupWL.CoordinateElimination
import Mathlib.Data.List.FinRange

/-! Explicit pivot-and-swap coordinates for one linear equation. The zero
row keeps all coordinates; a nonzero row removes exactly one coordinate. -/
namespace GroupWL.PivotCoordinates

open CoordinateElimination

variable {F : Type*} [Field F] [DecidableEq F]

def swapCoordinates {n : ℕ} (j : Fin (n+1)) :
    (Fin (n+1) → F) ≃ₗ[F] (Fin (n+1) → F) :=
  LinearEquiv.funCongrLeft F F (Equiv.swap 0 j)

@[simp] theorem swapCoordinates_apply {n : ℕ} (j : Fin (n+1)) (x : Fin (n+1) → F)
    (i : Fin (n+1)) : swapCoordinates j x i = x (Equiv.swap 0 j i) := rfl

@[simp] theorem swapCoordinates_single_zero {n : ℕ} (j : Fin (n+1)) :
    swapCoordinates (F:=F) j (Fin.cons 1 0) = Pi.single j 1 := by
  funext i
  by_cases hi : i=j
  · subst i; simp [swapCoordinates_apply]
  · have hs : Equiv.swap 0 j i ≠ 0 := by
      intro h
      have := congrArg (Equiv.swap 0 j) h
      exact hi (by simpa using this)
    have hzero : (Fin.cons (1:F) (0 : Fin n → F) : Fin (n+1) → F) (Equiv.swap 0 j i) = 0 := by
      generalize hy : Equiv.swap 0 j i = y at hs ⊢
      revert hs
      refine Fin.cases ?_ (fun _ _ => rfl) y
      intro hs
      exact False.elim (hs rfl)
    simp [swapCoordinates_apply,hzero,Pi.single_apply,hi]

def transportChart {n : ℕ} (f : (Fin n → F) →ₗ[F] F)
    (e : (Fin n → F) ≃ₗ[F] (Fin n → F)) (D : Chart n (LinearMap.ker (f.comp e.toLinearMap))) :
    Chart n (LinearMap.ker f) where
  width := D.width
  width_le := D.width_le
  lift := e.toLinearMap.comp D.lift
  lower := D.lower.comp e.symm.toLinearMap
  lower_lift x := by simp [D.lower_lift]
  lift_lower x hx := by
    have h : e.symm x ∈ LinearMap.ker (f.comp e.toLinearMap) := by
      simpa only [LinearMap.mem_ker,LinearMap.comp_apply,LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply] using hx
    simpa only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply] using
      congrArg e (D.lift_lower _ h)
  lift_mem x := D.lift_mem x

def pivotChart {n : ℕ} (f : (Fin (n+1) → F) →ₗ[F] F) (j : Fin (n+1)) :
    Chart (n+1) (LinearMap.ker f) :=
  transportChart f (swapCoordinates j) (rowChart (n+1) (f.comp (swapCoordinates j).toLinearMap))

theorem pivotChart_width {n : ℕ} (f : (Fin (n+1) → F) →ₗ[F] F) (j : Fin (n+1))
    (hj : f (Pi.single j 1) ≠ 0) : (pivotChart f j).width = n := by
  simp [pivotChart,transportChart,rowChart,hj]

def findPivot {n : ℕ} (f : (Fin n → F) →ₗ[F] F) : Option (Fin n) :=
  (List.finRange n).find? (fun j => decide (f (Pi.single j 1) ≠ 0))

theorem findPivot_some {n : ℕ} (f : (Fin n → F) →ₗ[F] F) (j : Fin n)
    (h : findPivot f = some j) : f (Pi.single j 1) ≠ 0 := by
  have hj : (fun k => decide (f (Pi.single k 1) ≠ 0)) j = true :=
    List.find?_some (p := fun k => decide (f (Pi.single k 1) ≠ 0)) h
  exact of_decide_eq_true hj

theorem findPivot_none {n : ℕ} (f : (Fin n → F) →ₗ[F] F)
    (h : findPivot f = none) : f=0 := by
  have he : ∀ j : Fin n, f (Pi.single j 1)=0 := by
    intro j
    have hj := List.find?_eq_none.mp h j (List.mem_finRange j)
    simpa using hj
  apply LinearMap.ext
  intro x
  rw [LinearMap.pi_apply_eq_sum_univ]
  simp only [LinearMap.zero_apply]
  apply Finset.sum_eq_zero
  intro i hi
  have hs : (fun j : Fin n => if i=j then (1:F) else 0) = Pi.single i 1 := by
    funext j
    simp [Pi.single_apply,eq_comm]
  rw [hs,he,smul_zero]

def zeroChart (n : ℕ) (f : (Fin n → F) →ₗ[F] F) (h : f=0) : Chart n (LinearMap.ker f) where
  width := n
  width_le := le_rfl
  lift := LinearMap.id
  lower := LinearMap.id
  lower_lift _ := rfl
  lift_lower _ _ := rfl
  lift_mem x := by simp [h]

/-- The search is over a finite coefficient array. No basis is chosen by
classical choice or by enumeration of field vectors. -/
def rowCoordinates : (n : ℕ) → (f : (Fin n → F) →ₗ[F] F) → Chart n (LinearMap.ker f)
  | 0,f => zeroChart 0 f (Subsingleton.elim f 0)
  | n+1,f =>
      match h : findPivot f with
      | none => zeroChart (n+1) f (findPivot_none f h)
      | some j => pivotChart f j

def nonzeroHeadChart {n : ℕ} (f : (Fin (n+1) → F) →ₗ[F] F)
    (ha : f (Fin.cons 1 0) ≠ 0) : Chart (n+1) (LinearMap.ker f) where
  width := n
  width_le := Nat.le_succ n
  lift := consMap ((-(f (Fin.cons 1 0))⁻¹) • (f.comp (zeroCons n))) LinearMap.id
  lower := tailMap n
  lower_lift _ := rfl
  lift_lower x hx := by
    change Fin.cons (-(f (Fin.cons 1 0))⁻¹ * f (Fin.cons 0 (Fin.tail x))) (Fin.tail x) = x
    have h : f x=0 := hx
    rw [←Fin.cons_self_tail x,apply_cons] at h
    have first : -(f (Fin.cons 1 0))⁻¹ * f (Fin.cons 0 (Fin.tail x)) = x 0 := by
      field_simp
      linear_combination -h
    rw [first,Fin.cons_self_tail]
  lift_mem x := by
    change f (Fin.cons (-(f (Fin.cons 1 0))⁻¹ * f (Fin.cons 0 x)) x)=0
    rw [apply_cons]
    field_simp
    ring

/-- A pivot chart whose output dimension is definitionally n. -/
def nonzeroPivotChart {n : ℕ} (f : (Fin (n+1) → F) →ₗ[F] F) (j : Fin (n+1))
    (hj : f (Pi.single j 1) ≠ 0) : Chart (n+1) (LinearMap.ker f) :=
  transportChart f (swapCoordinates j)
    (nonzeroHeadChart (f.comp (swapCoordinates j).toLinearMap) (by simpa using hj))

@[simp] theorem nonzeroPivotChart_width {n : ℕ} (f : (Fin (n+1) → F) →ₗ[F] F)
    (j : Fin (n+1)) (hj : f (Pi.single j 1) ≠ 0) : (nonzeroPivotChart f j hj).width=n := rfl

theorem swapCoordinates_single {n : ℕ} (j i : Fin (n+1)) :
    swapCoordinates (F:=F) j (Pi.single i 1) = Pi.single (Equiv.swap 0 j i) 1 := by
  funext k
  have he : Equiv.swap 0 j k=i ↔ k=Equiv.swap 0 j i := by
    constructor
    · intro h
      have := congrArg (Equiv.swap 0 j) h
      simpa using this
    · intro h
      rw [h,Equiv.swap_apply_self]
  simp only [swapCoordinates_apply,Pi.single_apply,he]

theorem zeroCons_single {n : ℕ} (i : Fin n) :
    zeroCons (F:=F) n (Pi.single i 1) = Pi.single i.succ 1 := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j <;> simp [zeroCons,consMap,Pi.single_apply]

theorem nonzeroPivot_lower_entry {n : ℕ} (f : (Fin (n+1) → F) →ₗ[F] F)
    (j : Fin (n+1)) (hj : f (Pi.single j 1) ≠ 0) (i : Fin n) (k : Fin (n+1)) :
    (nonzeroPivotChart f j hj).lower (Pi.single k 1) i =
      if Equiv.swap 0 j i.succ=k then 1 else 0 := by
  change (Pi.single k (1:F) : Fin (n+1) → F) (Equiv.swap 0 j i.succ) = _
  simp [Pi.single_apply]

theorem nonzeroPivot_lift_entry {n : ℕ} (f : (Fin (n+1) → F) →ₗ[F] F)
    (j : Fin (n+1)) (hj : f (Pi.single j 1) ≠ 0) (i : Fin (n+1)) (k : Fin n) :
    (nonzeroPivotChart f j hj).lift (Pi.single k 1) i =
      if i=j then -(f (Pi.single j 1))⁻¹*f (Pi.single (Equiv.swap 0 j k.succ) 1)
      else if Equiv.swap 0 j i=k.succ then 1 else 0 := by
  change (Fin.cons (-(f (swapCoordinates j (Fin.cons 1 0)))⁻¹ *
    f (swapCoordinates j (zeroCons n (Pi.single k 1)))) (Pi.single k 1) : Fin (n+1) → F)
      (Equiv.swap 0 j i) = _
  rw [swapCoordinates_single_zero,zeroCons_single,swapCoordinates_single]
  by_cases hi : i=j
  · subst i; simp
  · have he : Equiv.swap 0 j i ≠ 0 := by
      intro h
      have := congrArg (Equiv.swap 0 j) h
      exact hi (by simpa using this)
    simp only [hi,if_false]
    generalize hswap : Equiv.swap 0 j i = s at he ⊢
    revert he
    refine Fin.cases ?_ (fun l hl => ?_) s
    · intro hz; exact False.elim (hz rfl)
    · simp [Pi.single_apply]

end GroupWL.PivotCoordinates
