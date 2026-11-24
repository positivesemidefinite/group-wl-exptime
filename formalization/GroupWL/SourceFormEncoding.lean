import GroupWL.EdgeWedgeEncoding
import GroupWL.IncidenceFormEntries
import GroupWL.MachinePrograms.IncidenceFormMatrix
import GroupWL.SourceRadicalEncoding

/-! Arithmetic form-matrix entries coincide with the canonical coordinate form map. -/
namespace GroupWL.ConstructiveIncidence
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 2000000
open IncidenceTensor ConstructiveCoordinates MachinePrograms
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [FiniteCode I] [FiniteCode J]
variable (p : ℕ) [Fact p.Prime]
variable {V : J → Type} [∀j,AddCommGroup (V j)] [∀j,Module (ZMod p) (V j)]
variable (A : AffineSystem (ZMod p) I J V) (R : ∀j,Coordinates (ZMod p) (ReadoutRadical A j)) (q : ℕ)

def formData (radicals : List ℕ) : IncidenceFormMatrix.Data where
  frames := q
  blocks := FiniteCode.size I
  readouts := FiniteCode.size J
  edges := FiniteCode.size (Incidence A)
  oldInput := FiniteCode.size (OldInputIndex A R q)
  dimensions := ringDimensions A R
  offsets := inputOffsets A R q
  incidences := edgeIncidences A
  radicals := radicals

def RadicalTableSpec (radicals : List ℕ) : Prop := ∀(e : Incidence A) (k : Fin (R e.val.2).dimension),
  (radicals[((FiniteCode.equiv e.val.1).val*FiniteCode.size J+(FiniteCode.equiv e.val.2).val)*FiniteCode.size I+k.val]?.getD 0 : ZMod p)=
    radicalLift A R e k

theorem formData_value (radicals : List ℕ) (spec : RadicalTableSpec p A R radicals)
    (f : FormIndex A R q) (i : Fin (FiniteCode.size (OldInputIndex A R q))) :
    (IncidenceFormMatrix.value (formData p A R q radicals)
      ((FiniteCode.equiv f).val*FiniteCode.size (OldInputIndex A R q)+i.val) : ZMod p)=
      numericFormMap A R q (Pi.single i 1) (FiniteCode.equiv f) := by
  let n := FiniteCode.size (OldInputIndex A R q)
  have hn : 0<n := by have := i.isLt; omega
  have hrow : ((FiniteCode.equiv f).val*n+i.val)/n=(FiniteCode.equiv f).val := by
    rw [Nat.mul_comm _ n,Nat.mul_add_div hn,Nat.div_eq_of_lt i.isLt,Nat.add_zero]
  have hcol : ((FiniteCode.equiv f).val*n+i.val)%n=i.val := by
    rw [Nat.mul_add_mod',Nat.mod_eq_of_lt i.isLt]
  change (IncidenceFormMatrix.value (formData p A R q radicals) ((FiniteCode.equiv f).val*n+i.val) : ZMod p)=_
  dsimp only [IncidenceFormMatrix.value,formData]
  rw [hrow,hcol]
  cases f with
  | inl a =>
      rw [form_unit_input]
      simp only [FiniteCode.sum_inl_val,if_pos (FiniteCode.equiv a).isLt]
      by_cases heq : i.val=(FiniteCode.equiv a).val
      · simp only [heq,↓reduceIte,Nat.cast_one]
      · have heq' : (FiniteCode.equiv a).val≠i.val := Ne.symm heq
        simp only [heq,heq',↓reduceIte,Nat.cast_zero]
  | inr z =>
      rcases z with ⟨e,b,c⟩
      have hq : 0<q := by have := b.isLt; omega
      have hc : (FiniteCode.equiv c).val<2 := (FiniteCode.equiv c).isLt
      have hd : (((FiniteCode.equiv e).val*q+b.val)*2+(FiniteCode.equiv c).val)/2=
          (FiniteCode.equiv e).val*q+b.val := by
        rw [Nat.mul_comm _ 2,Nat.mul_add_div (by decide),Nat.div_eq_of_lt hc,Nat.add_zero]
      have he : ((FiniteCode.equiv e).val*q+b.val)/q=(FiniteCode.equiv e).val := by
        rw [Nat.mul_comm _ q,Nat.mul_add_div hq,Nat.div_eq_of_lt b.isLt,Nat.add_zero]
      have hb : ((FiniteCode.equiv e).val*q+b.val)%q=b.val := by rw [Nat.mul_add_mod',Nat.mod_eq_of_lt b.isLt]
      have hm : (((FiniteCode.equiv e).val*q+b.val)*2+(FiniteCode.equiv c).val)%2=(FiniteCode.equiv c).val := by
        rw [Nat.mul_add_mod',Nat.mod_eq_of_lt hc]
      have hej : ((FiniteCode.equiv e.val.1).val*FiniteCode.size J+(FiniteCode.equiv e.val.2).val)%FiniteCode.size J=
          (FiniteCode.equiv e.val.2).val := by rw [Nat.mul_add_mod',Nat.mod_eq_of_lt (FiniteCode.equiv e.val.2).isLt]
      have hdr : (ringDimensions A R)[FiniteCode.size I+(FiniteCode.equiv e.val.2).val]?.getD 0=(R e.val.2).dimension+1 := by
        simpa only [FiniteCode.sum_inr_val,ringDimension_readout] using ringDimensions_read A R (.inr e.val.2)
      have hor : (inputOffsets A R q)[FiniteCode.size I+(FiniteCode.equiv e.val.2).val]?.getD 0=inputOffset A R q (.inr e.val.2) := by
        simpa only [FiniteCode.sum_inr_val] using inputOffsets_read A R q (.inr e.val.2)
      rw [formIndex_endpoint]
      have hnlt : ¬FiniteCode.size (OldInputIndex A R q)+((FiniteCode.equiv e).val*q+b.val)*2+(FiniteCode.equiv c).val<FiniteCode.size (OldInputIndex A R q) := by omega
      have htail : FiniteCode.size (OldInputIndex A R q)+((FiniteCode.equiv e).val*q+b.val)*2+(FiniteCode.equiv c).val-FiniteCode.size (OldInputIndex A R q)=
          ((FiniteCode.equiv e).val*q+b.val)*2+(FiniteCode.equiv c).val := by omega
      rw [if_neg hnlt]
      simp only [htail,hd,he,hb,hm,IncidenceFormMatrix.read,edgeIncidences_read,hej,hdr,hor]
      change ((if (FiniteCode.equiv c).val=0 then (if i.val=endpointStart A R q e b then 1 else 0)
        else if endpointStart A R q e b < i.val ∧ i.val < endpointStart A R q e b+((R e.val.2).dimension+1)
          then radicals[((FiniteCode.equiv e.val.1).val*FiniteCode.size J+(FiniteCode.equiv e.val.2).val)*FiniteCode.size I+(i.val-endpointStart A R q e b-1)]?.getD 0 else 0 : ℕ) : ZMod p)=_
      cases c with
      | none =>
          rw [form_unit_scalar]
          simp only [FiniteCode.option_none_val,↓reduceIte]
          split_ifs <;> simp
      | some u =>
          cases u
          rw [form_unit_radical]
          have hcode : (FiniteCode.equiv (some PUnit.unit : Option PUnit.{1})).val=1 := rfl
          simp only [hcode,Nat.one_ne_zero,↓reduceIte]
          split_ifs with h h'
          · exact spec e ⟨i.val-endpointStart A R q e b-1,by omega⟩
          · omega
          · omega
          · simp

end GroupWL.ConstructiveIncidence

namespace GroupWL.SourceTableEncoding
open SourceLayout ConstructiveCoordinates ConstructiveIncidence
variable {T E : Type} [FiniteCode T] [FiniteCode E] {r : ℕ} (p : ℕ) [Fact p.Prime]
  (C : ComparisonData (ZMod p) T E r) (L : ℕ)
local instance sourceFormTypeFinite : Fintype T := FiniteCode.fintype T
local instance sourceFormEdgeFinite : Fintype E := FiniteCode.fintype E
local instance sourceFormBlockFinite : Fintype (C.Block L) := FiniteCode.fintype _
local instance sourceFormReadoutFinite : Fintype (C.Readout L) := FiniteCode.fintype _
local instance sourceFormBlockDecidable : DecidableEq (C.Block L) := (FiniteCode.equiv (α:=C.Block L)).decidableEq
local instance sourceFormReadoutDecidable : DecidableEq (C.Readout L) := (FiniteCode.equiv (α:=C.Readout L)).decidableEq

local instance sourceFormIncidenceCode : FiniteCode (IncidenceTensor.Incidence (ComputableSource.affineSystem C (L:=L))) := inferInstance

theorem radicalTable_spec (hdim : ∀t,C.dim t≤2) :
    RadicalTableSpec p (ComputableSource.affineSystem C (L:=L))
      (ConstructiveSourceTensor.radicalCoordinates C L) (radicalTable p C L) := by
  intro e k
  exact radicalTable_entry p C L hdim e k

theorem source_form_value (hdim : ∀t,C.dim t≤2) (q : ℕ)
    (f : FormIndex (ComputableSource.affineSystem C (L:=L)) (ConstructiveSourceTensor.radicalCoordinates C L) q)
    (i : Fin (FiniteCode.size (OldInputIndex (ComputableSource.affineSystem C (L:=L)) (ConstructiveSourceTensor.radicalCoordinates C L) q))) :
    (MachinePrograms.IncidenceFormMatrix.value
      (formData p (ComputableSource.affineSystem C (L:=L)) (ConstructiveSourceTensor.radicalCoordinates C L) q (radicalTable p C L))
      ((FiniteCode.equiv f).val*FiniteCode.size (OldInputIndex (ComputableSource.affineSystem C (L:=L)) (ConstructiveSourceTensor.radicalCoordinates C L) q)+i.val) : ZMod p)=
      numericFormMap (ComputableSource.affineSystem C (L:=L)) (ConstructiveSourceTensor.radicalCoordinates C L) q (Pi.single i 1) (FiniteCode.equiv f) :=
  formData_value p _ _ q _ (radicalTable_spec p C L hdim) f i

end GroupWL.SourceTableEncoding
