import GroupWL.ConstructiveOutputEncoding
import GroupWL.MachinePrograms.ConstructiveTensorAssembly
import GroupWL.MachinePrograms.LayoutRecordCorrectness

namespace GroupWL.ChargeCoordinates
open IncidenceTensor ConstructiveCoordinates ConstructiveIncidence
open scoped BigOperators
variable {F I J : Type} [Field F] [DecidableEq F]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [FiniteCode I] [FiniteCode J]
variable {V : J → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module F (V j)]
variable (A : AffineSystem F I J V) (R : ∀ j, Coordinates F (ReadoutRadical A j)) (q : ℕ)

theorem blockOffset (i : I) :
    inputOffset A R q (.inl i) = (FiniteCode.equiv i).val*(q*2) := by
  unfold inputOffset inputSizes
  rw [MachinePrograms.FilterRanks.count_ofFn _ _ (FiniteCode.equiv (α:=I⊕J) (.inl i)).isLt.le]
  trans ∑ _k : Fin (FiniteCode.equiv i).val, q*2
  · apply Finset.sum_congr rfl
    intro k _
    rw [ringDimension_runtime]
    have h : k.val < FiniteCode.size I := k.isLt.trans (FiniteCode.equiv i).isLt
    simp [MachinePrograms.RingDimensions.value, h]
  · simp

theorem blockInput (i : I) (a : Fin q) :
    (FiniteCode.equiv (scalarIndex A R q (.inl i) a)).val =
      (FiniteCode.equiv i).val*(q*2) + a.val*2 := by
  simp only [scalarIndex,FiniteCode.sum_inl_val,inputIndex_val,blockOffset,ringDimension_block,
    FiniteCode.option_none_val,Nat.add_zero]

theorem blockOutput (i : I) (hq : 2 ≤ q) :
    (FiniteCode.equiv (chargeIndex A R q hq i)).val =
      (FiniteCode.equiv i).val*(FiniteCode.size (Pair q)*2) +
        (FiniteCode.equiv (firstPair q hq)).val*2+1 := by
  rw [chargeIndex,FiniteCode.sum_inl_val,internalIndex_val,internalOffset,blockOffset,
    ringDimension_block,FiniteCode.option_some_val]
  rfl

theorem rank_lt (q : ℕ) (a b : Pair q) (h : FiniteCode.equiv a < FiniteCode.equiv b) :
    FiniteCode.equiv a.val < FiniteCode.equiv b.val := by
  let S := FiniteCode.subtypeSet (fun t : Fin q×Fin q => t.1<t.2)
  change (S.orderIsoOfFin rfl).symm _ < (S.orderIsoOfFin rfl).symm _ at h
  exact (S.orderIsoOfFin rfl).symm.lt_iff_lt.mp h

theorem rank_firstPair (q : ℕ) (hq : 2≤q) : (FiniteCode.equiv (firstPair q hq)).val=0 := by
  by_contra! h
  have hpos : 0 < (FiniteCode.equiv (firstPair q hq)).val := Nat.pos_of_ne_zero h
  let zero : Fin (FiniteCode.size (Pair q)) := ⟨0,hpos.trans (FiniteCode.equiv (firstPair q hq)).isLt⟩
  let a : Pair q := FiniteCode.equiv.symm zero
  have h' : FiniteCode.equiv a < FiniteCode.equiv (firstPair q hq) := by
    dsimp [a]
    simpa only [Equiv.apply_symm_apply] using hpos
  have h'' := rank_lt q _ _ h'
  change (FiniteCode.equiv _).val < (FiniteCode.equiv _).val at h''
  rw [FiniteCode.prod_val,FiniteCode.prod_val] at h''
  simp only [FiniteCode.fin_val,firstPair,Nat.zero_mul,Nat.zero_add] at h''
  change a.val.1.val*q + a.val.2.val < 1 at h''
  have ha := a.property
  change a.val.1.val<a.val.2.val at ha
  have hz : a.val.2.val=0 := by omega
  exact (Nat.not_lt_zero _) (hz ▸ ha)
open EvaluationTensorCoefficients MachinePrograms
local notation "X" => InputIndex A R q
local notation "Z" => OutputIndex A R q
def pulledUnit (t : Fin (FiniteCode.size X)) := 
  (inputEquiv A R q).symm ((Coordinates.pi (F:=F) X).equiv.symm (unit t))

def delta (s t : ℕ) : F := if s=t then 1 else 0

theorem scalar_unit (i : I) (a : Fin q) (t : Fin (FiniteCode.size X)) :
    scalarCoordinate A q (.inl i) a (pulledUnit A R q t) =
    delta ((FiniteCode.equiv i).val*(q*2)+a.val*2) t.val := by
  change ((pulledUnit A R q t).1 (.inl i) a).fst = _
  unfold pulledUnit
  rw [← inputEquiv_scalar A R q, LinearEquiv.apply_symm_apply]
  change (unit (F:=F) t) (FiniteCode.equiv (scalarIndex A R q (.inl i) a)) = _
  simp only [unit,Pi.single_apply,delta,Fin.ext_iff,blockInput]

theorem charge_coefficient (hq : 2 ≤ q) (β : I → F) (x y : Fin (FiniteCode.size X))
    (z : Fin (FiniteCode.size Z)) :
    (outputEquiv A R q (epsilonCharge A q hq β (pulledUnit A R q x) (pulledUnit A R q y)))
      (FiniteCode.equiv.symm z) =
      ∑ i : I, β i *
        (delta ((FiniteCode.equiv i).val*(q*2)) x.val *
         delta ((FiniteCode.equiv i).val*(q*2)+2) y.val -
         delta ((FiniteCode.equiv i).val*(q*2)) y.val *
         delta ((FiniteCode.equiv i).val*(q*2)+2) x.val) *
         delta ((FiniteCode.equiv i).val*(FiniteCode.size (Pair q)*2)+
           (FiniteCode.equiv (firstPair q hq)).val*2+1) z.val := by
  classical
  rw [epsilonCharge_apply,map_sum,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [unitCharge,elementaryTensor,LinearMap.mk₂_apply,map_smul,Pi.smul_apply,
    smul_eq_mul,outputEquiv_chargeOutput,scalar_unit]
  have h : FiniteCode.equiv.symm z=chargeIndex A R q hq i ↔
      (FiniteCode.equiv (chargeIndex A R q hq i)).val=z.val := by
    rw [← Fin.ext_iff,Equiv.symm_apply_eq, eq_comm]
  simp only [Pi.single_apply,h,blockOutput,delta,firstPair,Nat.zero_mul,Nat.add_zero,
    Nat.one_mul,mul_assoc]
  rfl

section Numeric
variable (p : ℕ) [Fact p.Prime]
variable {W : J → Type} [∀ j, AddCommGroup (W j)] [∀ j, Module (ZMod p) (W j)]
variable (B : AffineSystem (ZMod p) I J W)
  (C : ∀ j, Coordinates (ZMod p) (ReadoutRadical B j))
theorem denseTwist (hq : 2≤q) (β : I → ZMod p) :
    ConstructiveTensorAssembly.twistEntries p B C q (epsilonCharge B q hq β) =
    EvaluationAssembly.entries3 (fun (x y : Fin (FiniteCode.size (InputIndex B C q)))
      (z : Fin (FiniteCode.size (OutputIndex B C q))) =>
      (∑ i : I, β i *
        (delta ((FiniteCode.equiv i).val*(q*2)) x.val *
         delta ((FiniteCode.equiv i).val*(q*2)+2) y.val -
         delta ((FiniteCode.equiv i).val*(q*2)) y.val *
         delta ((FiniteCode.equiv i).val*(q*2)+2) x.val) *
         delta ((FiniteCode.equiv i).val*(FiniteCode.size (Pair q)*2)+1) z.val).val) := by
  unfold ConstructiveTensorAssembly.twistEntries EvaluationAssembly.twistEntries
  apply congrArg EvaluationAssembly.entries3
  funext x y z
  apply congrArg ZMod.val
  exact (by simpa only [rank_firstPair,Nat.zero_mul,Nat.add_zero] using
    charge_coefficient B C q hq β x y z)
end Numeric

end GroupWL.ChargeCoordinates

