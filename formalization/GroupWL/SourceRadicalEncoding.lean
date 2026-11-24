import GroupWL.SourceRelationCoordinates
import GroupWL.MachinePrograms.SourceRadicalEntries
import GroupWL.RadicalCoordinateEntries

/-! The executed global radical table is the scalar-first source coordinate
projection used in the incidence tensor. -/
namespace GroupWL.SourceTableEncoding
open SourceLayout ConstructiveCoordinates MachinePrograms
set_option maxHeartbeats 1600000

variable {T E : Type} [FiniteCode T] [FiniteCode E] {r : ℕ} (p : ℕ) [Fact p.Prime]
  (C : ComparisonData (ZMod p) T E r) (L : ℕ)
local instance sourceRadicalEncodingInstance1 : Fintype T := FiniteCode.fintype T
local instance sourceRadicalEncodingInstance2 : Fintype E := FiniteCode.fintype E
local instance sourceRadicalEncodingInstance3 : Fintype (C.Block L) := FiniteCode.fintype _
local instance sourceRadicalEncodingInstance4 : Fintype (C.Readout L) := FiniteCode.fintype _
local instance sourceRadicalEncodingInstance5 : DecidableEq (C.Block L) := (FiniteCode.equiv (α := C.Block L)).decidableEq
local instance sourceRadicalEncodingInstance6 : DecidableEq (C.Readout L) := (FiniteCode.equiv (α := C.Readout L)).decidableEq

def readoutDimensions : List ℕ :=
  List.ofFn (fun i : Fin (readoutCount p C L) =>
    (ComputableSource.readoutCoordinates C ((FiniteCode.equiv (α := C.Readout L)).symm i)).dimension)

@[simp] theorem readoutDimensions_read (j : C.Readout L) :
    (readoutDimensions p C L)[readoutIndex p C L j]?.getD 0=
      (ComputableSource.readoutCoordinates C j).dimension := by
  simp [readoutDimensions,readoutIndex]
  erw [Equiv.symm_apply_apply]

theorem degree_eq (j : C.Readout L) :
    (SourceNeighbors.selected (scopeTable p C L) (readoutCount p C L)
      (readoutIndex p C L j) (blockCount p C L)).length=FiniteCode.size (Neighbor p C L j) := by
  rw [←neighborWord_selected]
  exact List.length_ofFn

theorem relation_canonical (j : C.Readout L) :
    SourceRadicalClient.relation (scopeTable p C L) (coefficientTable p C L)
      (blockCount p C L) (readoutCount p C L) (readoutIndex p C L j)
      (ComputableSource.readoutCoordinates C j).dimension=relationWord p C L j := by
  unfold SourceRadicalClient.relation relationWord
  rw [←neighborWord_selected]
  simp only [neighborWord,List.length_ofFn]
  congr 1

theorem data_canonical (hdim : ∀ t, C.dim t≤2) (j : C.Readout L) :
    SourceRadicalClient.data p (scopeTable p C L) (coefficientTable p C L)
      (blockCount p C L) (readoutCount p C L) (readoutIndex p C L j)
      (ComputableSource.readoutCoordinates C j).dimension=
        KernelProgramCorrectness.encode (radicalChart p C L j) := by
  unfold SourceRadicalClient.data
  rw [relation_canonical,degree_eq]
  exact relation_executeRows p C L hdim j

def radicalTable : List ℕ :=
  SourceRadicalTables.collect p (scopeTable p C L) (coefficientTable p C L) (readoutDimensions p C L)
    (blockCount p C L) (readoutCount p C L) (readoutCount p C L)

theorem radicalTable_entry (hdim : ∀ t, C.dim t≤2)
    (e : IncidenceTensor.Incidence (ComputableSource.affineSystem C (L:=L)))
    (k : Fin (ConstructiveSourceTensor.radicalCoordinates C L e.1.2).dimension) :
    ((radicalTable p C L)[SourceRadicalTables.address (blockCount p C L) (readoutCount p C L)
      (blockIndex p C L e.1.1) (readoutIndex p C L e.1.2) k.val]?.getD 0 : ZMod p)=
      ConstructiveIncidence.radicalLift (ComputableSource.affineSystem C (L:=L))
        (ConstructiveSourceTensor.radicalCoordinates C L) e k := by
  let a := FiniteCode.equiv (α := Neighbor p C L e.1.2) ⟨e.1.1,e.2⟩
  have ha : a.val<(SourceNeighbors.selected (scopeTable p C L) (readoutCount p C L)
      (readoutIndex p C L e.1.2) (blockCount p C L)).length := by
    rw [degree_eq]
    exact a.isLt
  have hk : k.val<(SourceRadicalClient.data p (scopeTable p C L) (coefficientTable p C L)
      (blockCount p C L) (readoutCount p C L) (readoutIndex p C L e.1.2)
      ((readoutDimensions p C L)[readoutIndex p C L e.1.2]?.getD 0)).width := by
    rw [readoutDimensions_read,data_canonical p C L hdim]
    exact k.isLt
  have hblock : (SourceNeighbors.selected (scopeTable p C L) (readoutCount p C L)
      (readoutIndex p C L e.1.2) (blockCount p C L))[a.val]?.getD 0=blockIndex p C L e.1.1 := by
    rw [←neighborWord_selected,neighborWord_read]
    simp [a]
  have hit := SourceRadicalTables.collect_read_hit p (scopeTable p C L) (coefficientTable p C L)
    (readoutDimensions p C L) (blockCount p C L) (readoutCount p C L) (readoutCount p C L)
    (readoutIndex p C L e.1.2) a.val k.val (Fact.out : p.Prime).one_lt le_rfl
    (readoutIndex_lt p C L e.1.2) ha hk
  rw [hblock,readoutDimensions_read,data_canonical p C L hdim] at hit
  change (radicalTable p C L)[_]?.getD 0=
    (MatrixEncoding.word (CachedElimination.ofLinear (radicalChart p C L e.1.2).lift))[a.val*(radicalChart p C L e.1.2).width+k.val]?.getD 0 at hit
  have he := MatrixEncoding.word_read (CachedElimination.ofLinear (radicalChart p C L e.1.2).lift) a k
  have hit := hit.trans he
  erw [CachedElimination.ofLinear_entry] at hit
  rw [hit,ZMod.natCast_zmod_val]
  exact (ConstructiveIncidence.radicalLift_kernel_entry (ComputableSource.affineSystem C (L:=L))
    (ComputableSource.readoutCoordinates C) e k).symm

end GroupWL.SourceTableEncoding
