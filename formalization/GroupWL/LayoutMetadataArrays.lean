import GroupWL.LayoutMetadataCompaction
import GroupWL.SourceRadicalEncoding
import GroupWL.MachinePrograms.RepeatedSelection
import GroupWL.MachinePrograms.ArrayPad

/-! The compacted numeric endpoint records and dimensions are the exact source-table arrays. -/
namespace GroupWL.LayoutMetadata
open SourceLayout MachinePrograms
variable {T E : Type} [FiniteCode T] [FiniteCode E] {r : ℕ}
  (p : ℕ) [Fact p.Prime] (C : ComparisonData (ZMod p) T E r) (L : ℕ)

def squareArray (f : ℕ → ℕ) : List ℕ :=
  List.ofFn (fun i : Fin (linkCount (ComparisonMetadata.ofComparison p C) L*r*4) => f i)

def selectSquares (f : ℕ → ℕ) : List ℕ :=
  SelectArray.selectedPrefix (squareFlags (ComparisonMetadata.ofComparison p C) L)
    (squareArray p C L f) (squareFlags (ComparisonMetadata.ofComparison p C) L).length

theorem squareArray_read (f : ℕ → ℕ) (s : C.Square L) :
    (squareArray p C L f)[squareKey p C L s]?.getD 0=f (squareKey p C L s) := by
  have h := squareKey_lt p C L s
  simp only [squareFlags,List.length_ofFn,ComparisonMetadata.ofComparison] at h
  simp only [squareArray,List.getElem?_ofFn]
  split_ifs with hi
  · rfl
  · exact (hi h).elim

theorem selectSquares_eq (f : ℕ → ℕ) (g : C.Square L → ℕ)
    (h : ∀s,f (squareKey p C L s)=g s) :
    selectSquares p C L f=List.ofFn (fun i : Fin (FiniteCode.size (C.Square L)) => g (FiniteCode.equiv.symm i)) := by
  apply square_compaction
  intro s
  rw [squareArray_read,h]

theorem selected_left : selectSquares p C L (squareLeft (ComparisonMetadata.ofComparison p C) L)=
    SourceTableEncoding.coefficientData p C L .left :=
  selectSquares_eq p C L _ _ (squareLeft_correct p C L)
theorem selected_right : selectSquares p C L (squareRight (ComparisonMetadata.ofComparison p C) L)=
    SourceTableEncoding.coefficientData p C L .right :=
  selectSquares_eq p C L _ _ (squareRight_correct p C L)
theorem selected_before : selectSquares p C L (squareBefore (ComparisonMetadata.ofComparison p C) L)=
    SourceTableEncoding.coefficientData p C L .before :=
  selectSquares_eq p C L _ _ (squareBefore_correct p C L)
theorem selected_after : selectSquares p C L (squareAfter (ComparisonMetadata.ofComparison p C) L)=
    SourceTableEncoding.coefficientData p C L .after :=
  selectSquares_eq p C L _ _ (squareAfter_correct p C L)

def nodeDimensions : List ℕ :=
  List.ofFn (fun i : Fin (nodeCount (ComparisonMetadata.ofComparison p C) L) =>
    ArrayPad.entry (ComparisonMetadata.dimensions p C) 1 i)

theorem nodeDimensions_read (t : Node T E L) :
    (nodeDimensions p C L)[(FiniteCode.equiv t).val]?.getD 0=
      (ComputableSource.nodeCoordinates C t).dimension := by
  have ht : (FiniteCode.equiv t).val<nodeCount (ComparisonMetadata.ofComparison p C) L := (FiniteCode.equiv t).isLt
  simp only [nodeDimensions,List.getElem?_ofFn,dif_pos ht,Option.getD_some,
    ArrayPad.entry,ComparisonMetadata.dimensions_length]
  exact nodeDimension_correct p C L t

def horizontalDimensions : List ℕ :=
  RepeatedSelection.repeated (nodeDimensions p C L)
    (nodeCount (ComparisonMetadata.ofComparison p C) L) 1 (4*r)

theorem horizontalDimensions_read (h : C.Horizontal L) :
    (horizontalDimensions p C L)[horizontalTypedKey p C L h]?.getD 0=
      (ComputableSource.nodeCoordinates C h.1).dimension := by
  have ht := horizontalTypedKey_lt p C L h
  simp only [horizontalFlags,List.length_ofFn,ComparisonMetadata.ofComparison] at ht
  change horizontalTypedKey p C L h<nodeCount (ComparisonMetadata.ofComparison p C) L*r*4 at ht
  have hn : horizontalTypedKey p C L h<nodeCount (ComparisonMetadata.ofComparison p C) L*1*(4*r) := by nlinarith
  have ha : (FiniteCode.equiv h.2.2.1.val).val<2 := (FiniteCode.equiv h.2.2.1.val).isLt
  have hb : (FiniteCode.equiv h.2.2.2.val).val<2 := (FiniteCode.equiv h.2.2.2.val).isLt
  have htail : 4*h.2.1.val+2*(FiniteCode.equiv h.2.2.1.val).val+(FiniteCode.equiv h.2.2.2.val).val<4*r := by have := h.2.1.isLt; omega
  have hd : horizontalTypedKey p C L h/(4*r)=(FiniteCode.equiv h.1).val := by
    have he : horizontalTypedKey p C L h=(4*r)*(FiniteCode.equiv h.1).val+
        (4*h.2.1.val+2*(FiniteCode.equiv h.2.2.1.val).val+(FiniteCode.equiv h.2.2.2.val).val) := by
      simp only [horizontalTypedKey,horizontalKey,ComparisonMetadata.ofComparison]; ring
    rw [he,packed_div _ _ _ htail]
  simp only [horizontalDimensions,RepeatedSelection.repeated,List.getElem?_ofFn]
  split_ifs with hi
  all_goals first
    | exact (hi hn).elim
    | simpa only [Option.getD_some,ArrayRepeatBlocks.entry,Nat.div_one,Nat.mod_one,Nat.mul_one,Nat.add_zero,hd] using nodeDimensions_read p C L h.1

def selectedHorizontalDimensions : List ℕ :=
  SelectArray.selectedPrefix (horizontalFlags (ComparisonMetadata.ofComparison p C) L)
    (horizontalDimensions p C L) (horizontalFlags (ComparisonMetadata.ofComparison p C) L).length

theorem selectedHorizontalDimensions_correct :
    selectedHorizontalDimensions p C L=List.ofFn (fun i : Fin (FiniteCode.size (C.Horizontal L)) =>
      (ComputableSource.nodeCoordinates C ((FiniteCode.equiv (α:=C.Horizontal L)).symm i).1).dimension) :=
  horizontal_compaction p C L _ _ (horizontalDimensions_read p C L)

theorem readoutDimensions_correct :
    selectedHorizontalDimensions p C L++List.replicate (verticalCount (ComparisonMetadata.ofComparison p C) L) 1=
      SourceTableEncoding.readoutDimensions p C L := by
  rw [selectedHorizontalDimensions_correct,verticalCount_correct]
  unfold SourceTableEncoding.readoutDimensions SourceTableEncoding.readoutCount
  rw [List.ofFn_add]
  congr 1
  · congr 1
    funext i
    have he : (FiniteCode.equiv (α:=C.Readout L)).symm (Fin.castLE (Nat.le_add_right _ _) i)=
        Sum.inl ((FiniteCode.equiv (α:=C.Horizontal L)).symm i) := by
      apply (FiniteCode.equiv (α:=C.Readout L)).injective
      apply Fin.ext
      simp only [Equiv.apply_symm_apply,FiniteCode.sum_inl_val,Fin.val_castLE]
    rw [he]
    rfl
  · rw [←List.ofFn_const (n:=FiniteCode.size (C.Vertical L)) (1:ℕ)]
    congr 1
    funext i
    have he : (FiniteCode.equiv (α:=C.Readout L)).symm (Fin.natAdd (FiniteCode.size (C.Horizontal L)) i)=
        Sum.inr ((FiniteCode.equiv (α:=C.Vertical L)).symm i) := by
      apply (FiniteCode.equiv (α:=C.Readout L)).injective
      apply Fin.ext
      simp only [Equiv.apply_symm_apply,FiniteCode.sum_inr_val,Fin.val_natAdd]
    rw [he]
    rfl

end GroupWL.LayoutMetadata
