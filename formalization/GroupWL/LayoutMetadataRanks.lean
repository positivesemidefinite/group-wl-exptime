import GroupWL.LayoutMetadataFlags
import GroupWL.FiniteCodeFlatRanks

/-! The operational prefix ranks and counts are exactly the canonical
source-layout horizontal, vertical and square codes. -/
namespace GroupWL.LayoutMetadata
open SourceLayout MachinePrograms
variable {T E : Type} [FiniteCode T] [FiniteCode E] {r : ℕ}
  (p : ℕ) [Fact p.Prime] (C : ComparisonData (ZMod p) T E r) (L : ℕ)

theorem horizontal_block_read (t : Node T E L) (i : Fin r) (j : ℕ) (hj : j<4) :
    (horizontalFlags (ComparisonMetadata.ofComparison p C) L)[((FiniteCode.equiv t).val*r+i.val)*4+j]?.getD 0=
      (FiniteCode.boolPairFlags (C.labelDomain L t i) (C.labelDomain L t (finRotate r i)))[j]?.getD 0 := by
  interval_cases j
  · simpa [FiniteCode.boolPairFlags,Nat.mul_comm] using horizontalFlags_read p C L t i false false
  · simpa [FiniteCode.boolPairFlags,Nat.mul_comm] using horizontalFlags_read p C L t i false true
  · simpa [FiniteCode.boolPairFlags,Nat.mul_comm] using horizontalFlags_read p C L t i true false
  · simpa [FiniteCode.boolPairFlags,Nat.mul_comm] using horizontalFlags_read p C L t i true true

theorem square_block_read (l : Link E L) (i : Fin r) (j : ℕ) (hj : j<4) :
    (squareFlags (ComparisonMetadata.ofComparison p C) L)[((FiniteCode.equiv l).val*r+i.val)*4+j]?.getD 0=
      (FiniteCode.boolPairFlags (C.domain l.comparison i) (C.domain l.comparison (finRotate r i)))[j]?.getD 0 := by
  interval_cases j
  · simpa [FiniteCode.boolPairFlags,Nat.mul_comm] using squareFlags_read p C L l i false false
  · simpa [FiniteCode.boolPairFlags,Nat.mul_comm] using squareFlags_read p C L l i false true
  · simpa [FiniteCode.boolPairFlags,Nat.mul_comm] using squareFlags_read p C L l i true false
  · simpa [FiniteCode.boolPairFlags,Nat.mul_comm] using squareFlags_read p C L l i true true

theorem vertical_block_read (l : Link E L) (i : Fin r) (j : ℕ) (hj : j<2) :
    (linkLabels (ComparisonMetadata.ofComparison p C) L)[((FiniteCode.equiv l).val*r+i.val)*2+j]?.getD 0=
      (FiniteCode.boolFlags (C.domain l.comparison i))[j]?.getD 0 := by
  interval_cases j
  · simpa [FiniteCode.boolFlags,Nat.mul_comm] using linkLabels_read p C L l i false
  · simpa [FiniteCode.boolFlags,Nat.mul_comm] using linkLabels_read p C L l i true

theorem horizontalRank_correct (h : C.Horizontal L) :
    horizontalRank (ComparisonMetadata.ofComparison p C) L
      (horizontalKey (ComparisonMetadata.ofComparison p C) (FiniteCode.equiv h.1).val h.2.1.val
        (FiniteCode.equiv h.2.2.1.val).val (FiniteCode.equiv h.2.2.2.val).val)=
      (FiniteCode.equiv h).val := by
  have hh := FiniteCode.nested_flat_rank (α:=Node T E L)
    (γ:=fun t i => C.Label L t i × C.Label L t (finRotate r i))
    4 (horizontalFlags (ComparisonMetadata.ofComparison p C) L)
    (fun t i => FiniteCode.boolPairFlags (C.labelDomain L t i) (C.labelDomain L t (finRotate r i)))
    (fun _ _ ab => 2*(FiniteCode.equiv ab.1.val).val+(FiniteCode.equiv ab.2.val).val)
    (horizontal_block_read p C L)
    (fun t i => FiniteCode.bool_pair_size _ _)
    (fun t i ab => FiniteCode.bool_pair_rank _ _ ab.1 ab.2)
    (fun t i ab => by
      have ha : (FiniteCode.equiv ab.1.val).val<2 := (FiniteCode.equiv ab.1.val).isLt
      have hb : (FiniteCode.equiv ab.2.val).val<2 := (FiniteCode.equiv ab.2.val).isLt
      change 2*(FiniteCode.equiv ab.1.val).val+(FiniteCode.equiv ab.2.val).val≤4
      omega)
    h.1 h.2.1 h.2.2
  simpa only [horizontalRank,horizontalKey,ComparisonMetadata.ofComparison,Nat.mul_comm,Nat.add_assoc] using hh.symm

theorem verticalRank_correct (v : C.Vertical L) :
    verticalRank (ComparisonMetadata.ofComparison p C) L
      (verticalKey (ComparisonMetadata.ofComparison p C) (FiniteCode.equiv v.1).val v.2.1.val
        (FiniteCode.equiv v.2.2.val).val)=(FiniteCode.equiv v).val := by
  have hh := FiniteCode.nested_flat_rank (α:=Link E L)
    (γ:=fun l i => C.DomainLabel l.comparison i)
    2 (linkLabels (ComparisonMetadata.ofComparison p C) L)
    (fun l i => FiniteCode.boolFlags (C.domain l.comparison i))
    (fun _ _ a => (FiniteCode.equiv a.val).val)
    (vertical_block_read p C L)
    (fun l i => FiniteCode.bool_subtype_size _)
    (fun l i a => FiniteCode.bool_subtype_rank _ a)
    (fun l i a => Nat.le_of_lt (FiniteCode.equiv a.val).isLt)
    v.1 v.2.1 v.2.2
  simpa only [verticalRank,verticalKey,ComparisonMetadata.ofComparison,Nat.mul_comm] using hh.symm

theorem squareRank_correct (s : C.Square L) :
    squareRank (ComparisonMetadata.ofComparison p C) L
      (horizontalKey (ComparisonMetadata.ofComparison p C) (FiniteCode.equiv s.1).val s.2.1.val
        (FiniteCode.equiv s.2.2.1.val).val (FiniteCode.equiv s.2.2.2.val).val)=
      (FiniteCode.equiv s).val := by
  have hh := FiniteCode.nested_flat_rank (α:=Link E L)
    (γ:=fun l i => C.DomainLabel l.comparison i × C.DomainLabel l.comparison (finRotate r i))
    4 (squareFlags (ComparisonMetadata.ofComparison p C) L)
    (fun l i => FiniteCode.boolPairFlags (C.domain l.comparison i) (C.domain l.comparison (finRotate r i)))
    (fun _ _ ab => 2*(FiniteCode.equiv ab.1.val).val+(FiniteCode.equiv ab.2.val).val)
    (square_block_read p C L)
    (fun l i => FiniteCode.bool_pair_size _ _)
    (fun l i ab => FiniteCode.bool_pair_rank _ _ ab.1 ab.2)
    (fun l i ab => by
      have ha : (FiniteCode.equiv ab.1.val).val<2 := (FiniteCode.equiv ab.1.val).isLt
      have hb : (FiniteCode.equiv ab.2.val).val<2 := (FiniteCode.equiv ab.2.val).isLt
      change 2*(FiniteCode.equiv ab.1.val).val+(FiniteCode.equiv ab.2.val).val≤4
      omega)
    s.1 s.2.1 s.2.2
  simpa only [squareRank,horizontalKey,ComparisonMetadata.ofComparison,Nat.mul_comm,Nat.add_assoc] using hh.symm

theorem horizontalCount_correct : horizontalCount (ComparisonMetadata.ofComparison p C) L=
    FiniteCode.size (C.Horizontal L) := by
  have h := FiniteCode.nested_flat_size (α:=Node T E L)
    (γ:=fun t i => C.Label L t i × C.Label L t (finRotate r i))
    4 (horizontalFlags (ComparisonMetadata.ofComparison p C) L)
    (fun t i => FiniteCode.boolPairFlags (C.labelDomain L t i) (C.labelDomain L t (finRotate r i)))
    (horizontal_block_read p C L) (fun t i => FiniteCode.bool_pair_size _ _)
  simpa only [horizontalCount,horizontalFlags,List.length_ofFn,ComparisonMetadata.ofComparison,nodeCount_eq] using h.symm

theorem verticalCount_correct : verticalCount (ComparisonMetadata.ofComparison p C) L=
    FiniteCode.size (C.Vertical L) := by
  have h := FiniteCode.nested_flat_size (α:=Link E L)
    (γ:=fun l i => C.DomainLabel l.comparison i)
    2 (linkLabels (ComparisonMetadata.ofComparison p C) L)
    (fun l i => FiniteCode.boolFlags (C.domain l.comparison i))
    (vertical_block_read p C L) (fun l i => FiniteCode.bool_subtype_size _)
  simpa only [verticalCount,linkLabels,List.length_ofFn,ComparisonMetadata.ofComparison,linkCount_eq] using h.symm

theorem squareCount_correct : squareCount (ComparisonMetadata.ofComparison p C) L=
    FiniteCode.size (C.Square L) := by
  have h := FiniteCode.nested_flat_size (α:=Link E L)
    (γ:=fun l i => C.DomainLabel l.comparison i × C.DomainLabel l.comparison (finRotate r i))
    4 (squareFlags (ComparisonMetadata.ofComparison p C) L)
    (fun l i => FiniteCode.boolPairFlags (C.domain l.comparison i) (C.domain l.comparison (finRotate r i)))
    (square_block_read p C L) (fun l i => FiniteCode.bool_pair_size _ _)
  simpa only [squareCount,squareFlags,List.length_ofFn,ComparisonMetadata.ofComparison,linkCount_eq] using h.symm

end GroupWL.LayoutMetadata
