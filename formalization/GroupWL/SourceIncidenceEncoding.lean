import GroupWL.SourceRelationTables
import GroupWL.ConstructiveSourceTensor
import GroupWL.FiniteCodeValues

/-! Canonical incidence codes are obtained by selecting the full scope table. -/
namespace GroupWL.SourceTableEncoding
open SourceLayout MachinePrograms
variable {T E : Type} [FiniteCode T] [FiniteCode E] {r : ℕ} (p : ℕ) [Fact p.Prime]
  (C : ComparisonData (ZMod p) T E r) (L : ℕ)
local instance sourceIncidenceEncodingInstance1 : Fintype T := FiniteCode.fintype T
local instance sourceIncidenceEncodingInstance2 : Fintype E := FiniteCode.fintype E
local instance sourceIncidenceEncodingInstance3 : Fintype (C.Block L) := FiniteCode.fintype _
local instance sourceIncidenceEncodingInstance4 : Fintype (C.Readout L) := FiniteCode.fintype _
local instance sourceIncidenceEncodingInstance5 : DecidableEq (C.Block L) := (FiniteCode.equiv (α := C.Block L)).decidableEq
local instance sourceIncidenceEncodingInstance6 : DecidableEq (C.Readout L) := (FiniteCode.equiv (α := C.Readout L)).decidableEq

abbrev SourceIncidence := IncidenceTensor.Incidence (ComputableSource.affineSystem C (L:=L))
def incidenceWord : List ℕ := List.ofFn (fun i : Fin (FiniteCode.size (SourceIncidence p C L)) =>
  (FiniteCode.equiv (α:=C.Block L×C.Readout L) ((FiniteCode.equiv (α:=SourceIncidence p C L)).symm i).val).val)

theorem incidenceWord_selected : incidenceWord p C L=
    SourceNeighbors.selected (scopeTable p C L) 1 0 (blockCount p C L*readoutCount p C L) := by
  unfold incidenceWord SourceNeighbors.selected
  apply FiniteCode.subtype_values_filter
  intro i
  let B := ((FiniteCode.equiv (α:=C.Block L×C.Readout L)).symm i).1
  let j := ((FiniteCode.equiv (α:=C.Block L×C.Readout L)).symm i).2
  have he : blockIndex p C L B*readoutCount p C L+readoutIndex p C L j=i.val := by
    have h := FiniteCode.prod_val B j
    change (FiniteCode.equiv ((FiniteCode.equiv (α:=C.Block L×C.Readout L)).symm i)).val=_ at h
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  have h := scopeTable_read p C L B j
  rw [he] at h
  simp only [Nat.mul_one,Nat.add_zero,h]
  change ((if j∈ComputableSource.scope C B then 1 else 0) != 0)=decide (j∈ComputableSource.scope C B)
  split_ifs <;> simp_all

theorem incidenceWord_read (e : SourceIncidence p C L) :
    (incidenceWord p C L)[(FiniteCode.equiv e).val]?.getD 0=
      blockIndex p C L e.val.1*readoutCount p C L+readoutIndex p C L e.val.2 := by
  simp only [incidenceWord,List.getElem?_ofFn,(FiniteCode.equiv e).isLt,dif_pos,Option.getD_some]
  erw [Equiv.symm_apply_apply]
  exact FiniteCode.prod_val e.val.1 e.val.2

theorem incidence_selected_length :
    (SourceNeighbors.selected (scopeTable p C L) 1 0 (blockCount p C L*readoutCount p C L)).length=
      FiniteCode.size (SourceIncidence p C L) := by
  rw [←incidenceWord_selected]
  exact List.length_ofFn

end GroupWL.SourceTableEncoding
