import GroupWL.LayoutMetadataArrays
import GroupWL.MachinePrograms.ReadoutDimensionProgram
import GroupWL.MachinePrograms.DuplicateFlags
import GroupWL.MachinePrograms.LinkFormRecords
import GroupWL.MachinePrograms.SquareCharges

/-! Exact adapters from the executed dimension, form and charge arrays to the typed source tensor. -/
namespace GroupWL.MachinePrograms.PadRepeatedSelection

theorem padded_append (xs : List ℕ) (padding k : ℕ) :
    padded xs padding (xs.length+k)=xs++List.replicate k padding := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i<xs.length+k
  · simp only [padded,List.getElem?_ofFn,dif_pos hi,Option.getD_some]
    by_cases hx : i<xs.length
    · rw [List.getElem?_append_left hx]
      simp only [ArrayPad.entry,if_pos hx]
      simp [List.getElem?_eq_getElem hx]
    · rw [List.getElem?_append_right (by omega)]
      simp [ArrayPad.entry,hx,show i-xs.length<k by omega]
  · rw [List.getElem?_eq_none (by simp only [padded,List.length_ofFn]; omega),
      List.getElem?_eq_none (by simp only [List.length_append,List.length_replicate]; omega)]

end GroupWL.MachinePrograms.PadRepeatedSelection

namespace GroupWL.LayoutMetadata
open SourceLayout MachinePrograms
variable {T E : Type} [FiniteCode T] [FiniteCode E] {r : ℕ}
  (p : ℕ) [Fact p.Prime] (C : ComparisonData (ZMod p) T E r) (L : ℕ)

theorem readoutDimensionProgram_correct :
    ReadoutDimensionProgram.dimensions (ComparisonMetadata.dimensions p C)
      (horizontalFlags (ComparisonMetadata.ofComparison p C) L)
      (nodeCount (ComparisonMetadata.ofComparison p C) L) (4*r)
      (SourceTableEncoding.readoutCount p C L)=SourceTableEncoding.readoutDimensions p C L := by
  change PadRepeatedSelection.padded (selectedHorizontalDimensions p C L) 1 _=_
  have hl : (selectedHorizontalDimensions p C L).length=FiniteCode.size (C.Horizontal L) := by
    rw [selectedHorizontalDimensions_correct,List.length_ofFn]
  have hn : SourceTableEncoding.readoutCount p C L=(selectedHorizontalDimensions p C L).length+
      verticalCount (ComparisonMetadata.ofComparison p C) L := by
    rw [hl,verticalCount_correct]
    rfl
  rw [hn,PadRepeatedSelection.padded_append,readoutDimensions_correct]

def sourceCharge (b : E → ZMod p) : List ℕ :=
  List.ofFn (fun i : Fin (FiniteCode.size (C.Block L)) =>
    (C.sourceShift b ((FiniteCode.equiv (α:=C.Block L)).symm i)).val)

theorem selected_charge (chargedComparison : ℕ) :
    List.replicate (horizontalCount (ComparisonMetadata.ofComparison p C) L) 0++
      selectSquares p C L (squareCharge (ComparisonMetadata.ofComparison p C) L chargedComparison)=
      sourceCharge p C L (fun e => if (FiniteCode.equiv e).val=chargedComparison then 1 else 0) := by
  rw [selectSquares_eq p C L _ _ (squareCharge_correct p C L chargedComparison),horizontalCount_correct]
  unfold sourceCharge
  rw [FiniteCode.ofFn_sum (fun j : C.Block L =>
    (C.sourceShift (fun e => if (FiniteCode.equiv e).val=chargedComparison then 1 else 0) j).val)]
  congr 1
  simp only [ComparisonData.sourceShift,ZMod.val_zero,List.ofFn_const]

theorem squareCharges_selected (chargedComparison : ℕ) :
    List.replicate (horizontalCount (ComparisonMetadata.ofComparison p C) L) 0++
      SelectArray.selectedPrefix (squareFlags (ComparisonMetadata.ofComparison p C) L)
        (List.ofFn (fun i : Fin (linkCount (ComparisonMetadata.ofComparison p C) L*r*4) =>
          SquareCharges.entry r (FiniteCode.size E+FiniteCode.size E*L+chargedComparison) i))
        (squareFlags (ComparisonMetadata.ofComparison p C) L).length=
      sourceCharge p C L (fun e => if (FiniteCode.equiv e).val=chargedComparison then 1 else 0) :=
  selected_charge p C L chargedComparison

end GroupWL.LayoutMetadata

namespace GroupWL.LayoutMetadata
open SourceLayout MachinePrograms CircuitComparisons AddressedCircuit
variable {T : Type} [FiniteCode T] {r : ℕ} (p : ℕ) [Fact p.Prime] (A : Circuit T r) (L : ℕ)

theorem circuit_charge_correct :
    List.replicate (horizontalCount (ComparisonMetadata.ofComparison p (comparisons A (ZMod p))) L) 0++
      selectSquares p (comparisons A (ZMod p)) L
        (squareCharge (ComparisonMetadata.ofComparison p (comparisons A (ZMod p))) L
          (FiniteCode.size (Comparison A)-3))=
      sourceCharge p (comparisons A (ZMod p)) L (rejectingConstant A (ZMod p)) := by
  rw [selected_charge]
  congr 1
  funext e
  exact (CircuitComparisonCodes.rejectingConstant_eq_code A e).symm

end GroupWL.LayoutMetadata
