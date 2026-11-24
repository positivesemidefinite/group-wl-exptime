import GroupWL.SourceTableCorrectness
import GroupWL.FiniteCodeEnumeration
import GroupWL.MachinePrograms.SourceNeighbors
import GroupWL.MachinePrograms.SourceRelationMatrix

/-! Canonical scope columns, neighbor lists, and local relation matrices. -/
namespace GroupWL.SourceTableEncoding
open SourceLayout SourceTableCoefficients MachinePrograms
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false

private theorem flat_div (x d y : ℕ) (hy : y<d) : (x*d+y)/d=x := by
  rw [Nat.mul_comm x d,Nat.mul_add_div (by omega : 0<d),Nat.div_eq_of_lt hy,Nat.add_zero]

private theorem flat_mod (x d y : ℕ) (hy : y<d) : (x*d+y)%d=y := by
  rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hy]

variable {T E : Type} {r : ℕ} (p : ℕ) [Fact p.Prime]
  (C : ComparisonData (ZMod p) T E r) (L : ℕ)
variable [FiniteCode (C.Horizontal L)] [FiniteCode (C.Vertical L)] [FiniteCode (C.Square L)]
local instance : DecidableEq (C.Readout L) := (FiniteCode.equiv (α := C.Readout L)).decidableEq

def scopeTable : List ℕ :=
  List.ofFn (fun i : Fin (blockCount p C L*readoutCount p C L) =>
    SourceIncidenceTable.tableEntry (incidenceData p C L) (horizontalCount p C L)
      (readoutCount p C L) i.val)

def coefficientTable : List ℕ :=
  List.ofFn (fun i : Fin (blockCount p C L*readoutCount p C L*2) =>
    SourceCoefficientTable.tableEntry (coefficientData p C L) (horizontalCount p C L)
      p (readoutCount p C L) i.val)

abbrev Neighbor (j : C.Readout L) := {B : C.Block L // j ∈ ComputableSource.scope C B}

def neighborWord (j : C.Readout L) : List ℕ :=
  List.ofFn (fun i : Fin (FiniteCode.size (Neighbor p C L j)) =>
    blockIndex p C L ((FiniteCode.equiv (α := Neighbor p C L j)).symm i).val)

theorem blockIndex_lt (B : C.Block L) : blockIndex p C L B<blockCount p C L :=
  (FiniteCode.equiv (α := C.Block L) B).isLt

theorem readoutIndex_lt (j : C.Readout L) : readoutIndex p C L j<readoutCount p C L :=
  (FiniteCode.equiv (α := C.Readout L) j).isLt

theorem scopeTable_read (B : C.Block L) (j : C.Readout L) :
    (scopeTable p C L)[blockIndex p C L B*readoutCount p C L+readoutIndex p C L j]?.getD 0 =
      if j ∈ ComputableSource.scope C B then 1 else 0 := by
  have hb := blockIndex_lt p C L B
  have hj := readoutIndex_lt p C L j
  have hr : 0<readoutCount p C L := by omega
  have hi : blockIndex p C L B*readoutCount p C L+readoutIndex p C L j <
      blockCount p C L*readoutCount p C L := by nlinarith
  simp only [scopeTable,List.getElem?_ofFn,hi,dif_pos,Option.getD_some,
    SourceIncidenceTable.tableEntry,flat_div _ _ _ hj,flat_mod _ _ _ hj]
  exact (incidence_correct p C L B j).trans (by split_ifs <;> rfl)

theorem coefficientTable_read (B : C.Block L) (j : C.Readout L) (k : ℕ) (hk : k<2) :
    ((coefficientTable p C L)[(blockIndex p C L B*readoutCount p C L+readoutIndex p C L j)*2+k]?.getD 0 : ZMod p) =
      entry C L B j k := by
  have hb := blockIndex_lt p C L B
  have hj := readoutIndex_lt p C L j
  have hr : 0<readoutCount p C L := by omega
  have hi : (blockIndex p C L B*readoutCount p C L+readoutIndex p C L j)*2+k <
      blockCount p C L*readoutCount p C L*2 := by nlinarith
  simp only [coefficientTable,List.getElem?_ofFn,hi,dif_pos,Option.getD_some,
    SourceCoefficientTable.tableEntry,flat_div _ _ _ hk,flat_mod _ _ _ hk,
    flat_div _ _ _ hj,flat_mod _ _ _ hj]
  exact coefficient_correct p C L B j k hk

theorem neighborWord_selected (j : C.Readout L) :
    neighborWord p C L j = SourceNeighbors.selected (scopeTable p C L)
      (readoutCount p C L) (readoutIndex p C L j) (blockCount p C L) := by
  unfold neighborWord SourceNeighbors.selected blockIndex
  apply FiniteCode.subtype_values_filter (fun B : C.Block L => j ∈ ComputableSource.scope C B)
  intro i
  have h := scopeTable_read p C L ((FiniteCode.equiv (α := C.Block L)).symm i) j
  have he : blockIndex p C L ((FiniteCode.equiv (α := C.Block L)).symm i)=i.val := by
    simp [blockIndex]
  rw [he] at h
  change ((scopeTable p C L)[i.val*readoutCount p C L+readoutIndex p C L j]?.getD 0 != 0) = _
  rw [h]
  split_ifs <;> simp_all

theorem neighborWord_read (j : C.Readout L) (i : Fin (FiniteCode.size (Neighbor p C L j))) :
    (neighborWord p C L j)[i.val]?.getD 0 =
      blockIndex p C L ((FiniteCode.equiv (α := Neighbor p C L j)).symm i).val := by
  simp [neighborWord]

theorem neighborWord_valid (j : C.Readout L) :
    ∀ i < (neighborWord p C L j).length,
      (neighborWord p C L j)[i]?.getD 0 < blockCount p C L := by
  intro i hi
  have hi' : i<FiniteCode.size (Neighbor p C L j) := by simpa [neighborWord] using hi
  rw [neighborWord_read p C L j ⟨i,hi'⟩]
  exact blockIndex_lt p C L _

theorem relation_entry (j : C.Readout L) (i : Fin (FiniteCode.size (Neighbor p C L j)))
    (k : ℕ) (hk : k<2) :
    (SourceRelationMatrix.entry (coefficientTable p C L) (neighborWord p C L j)
      (readoutCount p C L) (readoutIndex p C L j) (FiniteCode.size (Neighbor p C L j))
      (k*FiniteCode.size (Neighbor p C L j)+i.val) : ZMod p) =
    entry C L ((FiniteCode.equiv (α := Neighbor p C L j)).symm i).val j k := by
  have hg : 0<FiniteCode.size (Neighbor p C L j) := Nat.pos_of_ne_zero (by intro h; simpa [h] using i.isLt)
  simp only [SourceRelationMatrix.entry,flat_div _ _ _ i.isLt,flat_mod _ _ _ i.isLt,neighborWord_read]
  exact coefficientTable_read p C L _ j k hk

end GroupWL.SourceTableEncoding
