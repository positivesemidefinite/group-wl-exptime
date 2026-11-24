import GroupWL.CachedElimination
import GroupWL.PivotCoordinates
import GroupWL.MachinePrograms.PivotSearch

/-! Materialized kernel recursion matching the operational last-row-first
elimination and its first-nonzero pivot scan. -/
namespace GroupWL.PivotElimination
open CoordinateElimination PivotCoordinates CachedElimination
open MachinePrograms.PivotSearch
variable {F : Type*} [Field F] [DecidableEq F]

def supportWord {n : ℕ} (f : (Fin n → F) →ₗ[F] F) : List ℕ :=
  List.ofFn (fun i => if f (Pi.single i 1)=0 then 0 else 1)

@[simp] theorem supportWord_length {n : ℕ} (f : (Fin n → F) →ₗ[F] F) :
    (supportWord f).length=n := List.length_ofFn

@[simp] theorem supportWord_read {n : ℕ} (f : (Fin n → F) →ₗ[F] F) (i : Fin n) :
    ((supportWord f)[i.val]?).getD 0=if f (Pi.single i 1)=0 then 0 else 1 := by simp [supportWord]

theorem first_congr (xs ys : List ℕ) (n : ℕ)
    (h : ∀i<n,(xs[i]?.getD 0=0 ↔ ys[i]?.getD 0=0)) : first xs n=first ys n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have he := ih (fun i hi => h i (by omega))
    simp only [first,he]
    cases hx : first ys n with
    | some j => rfl
    | none => simp only [h n (by omega)]

theorem first_none_zero {n : ℕ} (f : (Fin n → F) →ₗ[F] F)
    (h : first (supportWord f) n=none) : f=0 := by
  have hz := (first_none_iff (supportWord f) n).mp h
  have hb (i : Fin n) : f (Pi.single i 1)=0 := by
    have hi := hz i.val i.isLt
    rw [supportWord_read] at hi
    split_ifs at hi with hf
    exact hf
  apply LinearMap.ext
  intro x
  rw [LinearMap.pi_apply_eq_sum_univ]
  change _=0
  apply Finset.sum_eq_zero
  intro i _
  have he : (fun j : Fin n => if i=j then (1:F) else 0) = Pi.single i 1 := by
    funext j
    simp [Pi.single_apply,eq_comm]
  rw [he,hb,smul_zero]

theorem first_some_nonzero {n : ℕ} (f : (Fin n → F) →ₗ[F] F) (j : ℕ)
    (h : first (supportWord f) n=some j) :
    ∃hj : j<n,f (Pi.single ⟨j,hj⟩ 1)≠0 := by
  obtain ⟨hj,hne⟩ := first_some (supportWord f) n j h
  refine ⟨hj,?_⟩
  have he := supportWord_read f ⟨j,hj⟩
  simp only [Fin.val_mk] at he
  rw [he] at hne
  intro hz
  simp [hz] at hne

def rowCoordinates : (n : ℕ) → (f : (Fin n → F) →ₗ[F] F) → Chart n (LinearMap.ker f)
  | 0,f => zeroChart 0 f (Subsingleton.elim f 0)
  | n+1,f =>
      match h : first (supportWord f) (n+1) with
      | none => zeroChart (n+1) f (first_none_zero f h)
      | some j => nonzeroPivotChart f ⟨j,(first_some_nonzero f j h).choose⟩
          (first_some_nonzero f j h).choose_spec

theorem rowCoordinates_none {n : ℕ} (f : (Fin n → F) →ₗ[F] F)
    (h : first (supportWord f) n=none) :
    rowCoordinates n f=zeroChart n f (first_none_zero f h) := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [rowCoordinates]
    split
    · rfl
    · rename_i j h'
      rw [h] at h'
      contradiction

theorem rowCoordinates_some {n : ℕ} (f : (Fin (n+1) → F) →ₗ[F] F) (j : Fin (n+1))
    (h : first (supportWord f) (n+1)=some j.val)
    (hj : f (Pi.single j 1)≠0) :
    rowCoordinates (n+1) f=nonzeroPivotChart f j hj := by
  simp only [rowCoordinates]
  split
  · rename_i h'
    rw [h] at h'
    contradiction
  · rename_i k h'
    have he : k=j.val := Option.some.inj (h'.symm.trans h)
    subst k
    rfl

/-- Every recursion stage materializes its resulting coefficient maps. -/
def kernelChart : (m n : ℕ) →
    (f : (Fin n → F) →ₗ[F] (Fin m → F)) → Chart n (LinearMap.ker f)
  | 0,n,f => materialize
      { width := n
        width_le := le_rfl
        lift := LinearMap.id
        lower := LinearMap.id
        lower_lift := fun _ => rfl
        lift_lower := fun _ _ => rfl
        lift_mem := by intro x; exact Subsingleton.elim _ _ }
  | m+1,n,f =>
      let g := (tailMap m).comp f
      let D := kernelChart m n g
      let h := (LinearMap.proj 0).comp (f.comp D.lift)
      let R := materialize (rowCoordinates D.width h)
      materialize
        { width := R.width
          width_le := R.width_le.trans D.width_le
          lift := D.lift.comp R.lift
          lower := R.lower.comp D.lower
          lower_lift := by
            intro x
            change R.lower (D.lower (D.lift (R.lift x)))=x
            rw [D.lower_lift,R.lower_lift]
          lift_lower := by
            intro x hx
            have hg : x∈LinearMap.ker g := by
              change (tailMap m) (f x)=0
              change f x=0 at hx
              rw [hx,map_zero]
            have hh : D.lower x∈LinearMap.ker h := by
              change f (D.lift (D.lower x)) 0=0
              rw [D.lift_lower x hg]
              change f x=0 at hx
              rw [hx]; rfl
            change D.lift (R.lift (R.lower (D.lower x)))=x
            rw [R.lift_lower _ hh,D.lift_lower x hg]
          lift_mem := by
            intro x
            change f (D.lift (R.lift x))=0
            funext i
            refine Fin.cases ?_ (fun j => ?_) i
            · exact R.lift_mem x
            · exact congrFun (D.lift_mem (R.lift x)) j }

def kernelCoordinates {m n : ℕ} (f : (Fin n → F) →ₗ[F] (Fin m → F)) :
    LinearMap.ker f ≃ₗ[F] (Fin (kernelChart m n f).width → F) := (kernelChart m n f).equiv

theorem kernelCoordinates_width_le {m n : ℕ} (f : (Fin n → F) →ₗ[F] (Fin m → F)) :
    (kernelChart m n f).width≤n := (kernelChart m n f).width_le

def matrixKernelChart {m n : ℕ} (A : MatrixData (F:=F) m n) : Chart n (LinearMap.ker (toLinear A)) :=
  kernelChart m n (toLinear A)

end GroupWL.PivotElimination
