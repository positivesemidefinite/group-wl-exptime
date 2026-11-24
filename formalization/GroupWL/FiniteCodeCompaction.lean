import GroupWL.FiniteCodeValues
import GroupWL.MachinePrograms.SelectArraySemantics

/-! A rank-preserving stable compaction is exactly the canonical finite-code enumeration. -/
namespace GroupWL.FiniteCode
open MachinePrograms

variable {α : Type*} [FiniteCode α]

theorem selectedPrefix_eq_ofFn (flags values : List ℕ) (n : ℕ) (key : α → ℕ) (f : α → ℕ)
    (binary : ∀x∈flags,x≤1) (total : FilterRanks.count flags n=size α)
    (bound : ∀a,key a<n) (chosen : ∀a,flags[key a]?.getD 0=1)
    (rank : ∀a,FilterRanks.count flags (key a)=(equiv a).val)
    (read : ∀a,values[key a]?.getD 0=f a) :
    SelectArray.selectedPrefix flags values n=List.ofFn (fun i : Fin (size α) => f (equiv.symm i)) := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i<size α
  · let a : α := equiv.symm ⟨i,hi⟩
    have h := SelectArray.selectedPrefix_read flags values binary n (key a) (bound a) (chosen a)
    rw [rank a,read a] at h
    simpa [a,hi] using h
  · have hl := SelectArray.selectedPrefix_length flags values binary n
    rw [total] at hl
    rw [List.getElem?_eq_none (by omega),List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hi)]

end GroupWL.FiniteCode
