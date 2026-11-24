import GroupWL.InternalWedgeCompaction
import GroupWL.IncidenceWedgeForms

namespace GroupWL.ConstructiveIncidence
open IncidenceTensor ConstructiveCoordinates MachinePrograms
variable {F I J : Type} [Field F] [DecidableEq F]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [FiniteCode I] [FiniteCode J]
variable {V : J → Type} [∀j,AddCommGroup (V j)] [∀j,Module F (V j)]
variable (A : AffineSystem F I J V) (R : ∀j,Coordinates F (ReadoutRadical A j)) (q cap : ℕ)

def descriptorValue (f : InternalWedgeDescriptors.Field) (z : OldOutputIndex A R q) : ℕ :=
  match f with
  | .u0 => (FiniteCode.equiv (formU0 A R q z)).val
  | .v0 => (FiniteCode.equiv (formV0 A R q z)).val
  | .u1 => (FiniteCode.equiv (formU1 A R q z)).val
  | .v1 => (FiniteCode.equiv (formV1 A R q z)).val
  | .second => if formSecond A R q z then 1 else 0
  | .keep => 1

theorem internalValue_form (bound : ∀v,ringDimension A R v≤cap)
    (v : I⊕J) (ab : Pair q) (c : Option (RadicalIndex A R v)) (f : InternalWedgeDescriptors.Field) :
    InternalWedgeDescriptors.value (internalData A R q cap) f (internalKey A R q cap v ab c)=
      descriptorValue A R q f (.inl ⟨v,ab,c⟩) := by
  rw [internalValue A R q cap bound]
  cases f <;> simp only [descriptorValue,formU0,formV0,formU1,formV1,formSecond,
    FiniteCode.sum_inl_val,inputIndex_val,FiniteCode.option_none_val,Nat.add_zero]
  cases c <;> simp [FiniteCode.option_none_val,FiniteCode.option_some_val]

theorem internal_compaction_form (bound : ∀v,ringDimension A R v≤cap)
    (f : InternalWedgeDescriptors.Field) :
    SelectArray.selectedPrefix (internalRaw A R q cap .keep) (internalRaw A R q cap f)
      (internalRaw A R q cap .keep).length=
      List.ofFn (fun i : Fin (FiniteCode.size (InternalIndex A R q)) =>
        descriptorValue A R q f (.inl (FiniteCode.equiv.symm i))) := by
  rw [internal_compaction A R q cap bound f]
  apply congrArg List.ofFn
  funext i
  exact internalValue_form A R q cap bound _ _ _ f

end GroupWL.ConstructiveIncidence
