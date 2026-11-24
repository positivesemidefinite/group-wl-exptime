import GroupWL.IncidenceWedgeForms

/-! Numeric coefficients of coordinate and readout-endpoint forms. -/
namespace GroupWL.ConstructiveIncidence
open IncidenceTensor ConstructiveCoordinates
open scoped BigOperators
variable {F I J : Type} [Field F] [DecidableEq F]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [FiniteCode I] [FiniteCode J]
variable {V : J → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module F (V j)]
variable (A : AffineSystem F I J V) (R : ∀ j, Coordinates F (ReadoutRadical A j)) (q : ℕ)

def endpointStart (e : Incidence A) (b : Fin q) :=
  inputOffset A R q (.inr e.val.2)+b.val*((R e.val.2).dimension+1)

theorem form_unit_input (a : OldInputIndex A R q)
    (i : Fin (FiniteCode.size (OldInputIndex A R q))) :
    numericFormMap A R q (Pi.single i 1) (FiniteCode.equiv (.inl a : FormIndex A R q))=
      if i.val=(FiniteCode.equiv a).val then 1 else 0 := by
  rw [numericFormMap_apply]
  simp [formValue,Pi.single_apply,Fin.ext_iff,eq_comm]

theorem form_unit_scalar (e : Incidence A) (b : Fin q)
    (i : Fin (FiniteCode.size (OldInputIndex A R q))) :
    numericFormMap A R q (Pi.single i 1) (FiniteCode.equiv (.inr (e,b,none) : FormIndex A R q))=
      if i.val=endpointStart A R q e b then 1 else 0 := by
  rw [numericFormMap_apply]
  change (Pi.single i (1:F) : Fin (FiniteCode.size (OldInputIndex A R q)) → F) (FiniteCode.equiv ⟨.inr e.val.2,(b,none)⟩)=_
  simp only [Pi.single_apply,Fin.ext_iff,inputIndex_val,ringDimension_readout,
    FiniteCode.option_none_val,Nat.add_zero]
  simp [endpointStart,eq_comm]

theorem form_unit_radical_sum (e : Incidence A) (b : Fin q)
    (i : Fin (FiniteCode.size (OldInputIndex A R q))) :
    numericFormMap A R q (Pi.single i 1) (FiniteCode.equiv (.inr (e,b,some PUnit.unit) : FormIndex A R q))=
      ∑j : Fin (R e.val.2).dimension,
        if i.val=endpointStart A R q e b+1+j.val then radicalLift A R e j else 0 := by
  rw [numericFormMap_apply]
  change (∑j : Fin (R e.val.2).dimension,
    (Pi.single i (1:F) : Fin (FiniteCode.size (OldInputIndex A R q)) → F) (FiniteCode.equiv ⟨.inr e.val.2,(b,some j)⟩)*radicalLift A R e j)=_
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Pi.single_apply,Fin.ext_iff,inputIndex_val,ringDimension_readout,
    FiniteCode.option_some_val,FiniteCode.fin_val]
  change (if inputOffset A R q (.inr e.val.2)+b.val*((R e.val.2).dimension+1)+(j.val+1)=i.val
    then (1:F) else 0)*radicalLift A R e j=_
  have hpos : inputOffset A R q (.inr e.val.2)+b.val*((R e.val.2).dimension+1)+(j.val+1)=
      endpointStart A R q e b+1+j.val := by unfold endpointStart; omega
  rw [hpos]
  split_ifs <;> simp only [one_mul,zero_mul] <;> omega

theorem form_unit_radical (e : Incidence A) (b : Fin q)
    (i : Fin (FiniteCode.size (OldInputIndex A R q))) :
    numericFormMap A R q (Pi.single i 1) (FiniteCode.equiv (.inr (e,b,some PUnit.unit) : FormIndex A R q))=
      if h : endpointStart A R q e b < i.val ∧ i.val<endpointStart A R q e b+(R e.val.2).dimension+1
      then radicalLift A R e ⟨i.val-endpointStart A R q e b-1,by omega⟩ else 0 := by
  rw [form_unit_radical_sum]
  split_ifs with h
  · let k : Fin (R e.val.2).dimension := ⟨i.val-endpointStart A R q e b-1,by omega⟩
    rw [Finset.sum_eq_single k]
    · rw [if_pos (by dsimp [k]; omega)]
    · intro j hj hjk
      have hne : i.val≠endpointStart A R q e b+1+j.val := by
        intro he
        apply hjk
        apply Fin.ext
        dsimp [k]
        omega
      simp [hne]
    · simp
  · apply Finset.sum_eq_zero
    intro j hj
    have hne : i.val≠endpointStart A R q e b+1+j.val := by have := j.isLt; omega
    simp [hne]

end GroupWL.ConstructiveIncidence
