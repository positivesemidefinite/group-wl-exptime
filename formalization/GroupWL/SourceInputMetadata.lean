import GroupWL.SourceRadicalEncoding
import GroupWL.ConstructiveInputEncoding

/-! Canonical source widths and the runtime input coordinate metadata. -/
namespace GroupWL.SourceTableEncoding
open SourceLayout ConstructiveCoordinates MachinePrograms
variable {T E : Type} [FiniteCode T] [FiniteCode E] {r : ℕ} (p : ℕ) [Fact p.Prime]
  (C : ComparisonData (ZMod p) T E r) (L : ℕ)
local instance sourceInputMetadataInstance1 : Fintype T := FiniteCode.fintype T
local instance sourceInputMetadataInstance2 : Fintype E := FiniteCode.fintype E
local instance sourceInputMetadataInstance3 : Fintype (C.Block L) := FiniteCode.fintype _
local instance sourceInputMetadataInstance4 : Fintype (C.Readout L) := FiniteCode.fintype _
local instance sourceInputMetadataInstance5 : DecidableEq (C.Block L) := (FiniteCode.equiv (α := C.Block L)).decidableEq
local instance sourceInputMetadataInstance6 : DecidableEq (C.Readout L) := (FiniteCode.equiv (α := C.Readout L)).decidableEq

def radicalWidths : List ℕ := List.ofFn (fun i : Fin (readoutCount p C L) =>
  SourceRadicalTables.width p (scopeTable p C L) (coefficientTable p C L) (readoutDimensions p C L)
    (blockCount p C L) (readoutCount p C L) i.val)

theorem radicalWidth_canonical (hdim : ∀ t, C.dim t≤2) (j : C.Readout L) :
    SourceRadicalTables.width p (scopeTable p C L) (coefficientTable p C L) (readoutDimensions p C L)
      (blockCount p C L) (readoutCount p C L) (readoutIndex p C L j)=
    (ConstructiveSourceTensor.radicalCoordinates C L j).dimension := by
  unfold SourceRadicalTables.width
  rw [readoutDimensions_read,data_canonical p C L hdim]
  rfl

theorem radicalWidths_canonical (hdim : ∀ t, C.dim t≤2) :
    radicalWidths p C L=ConstructiveIncidence.readoutWidths
      (ComputableSource.affineSystem C (L:=L)) (ConstructiveSourceTensor.radicalCoordinates C L) := by
  apply congrArg List.ofFn
  funext i
  have h := radicalWidth_canonical p C L hdim ((FiniteCode.equiv (α:=C.Readout L)).symm i)
  simpa [readoutIndex] using h

theorem radicalWidths_le : ∀ x∈radicalWidths p C L,x≤blockCount p C L := by
  intro x hx
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  have h := (SourceRadicalClient.data_valid p (scopeTable p C L) (coefficientTable p C L)
    (blockCount p C L) (readoutCount p C L) i.val ((readoutDimensions p C L)[i.val]?.getD 0)
    (Fact.out : p.Prime).one_lt).width
  exact h.trans (SourceNeighbors.selected_length_le _ _ _ _)

end GroupWL.SourceTableEncoding
