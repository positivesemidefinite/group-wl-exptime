import GroupWL.SourceTableCoefficients
import GroupWL.SourceCoefficientResidues
import GroupWL.MachinePrograms.SourceCoefficientTable
import GroupWL.MachinePrograms.SourceIncidenceTable

/-! Canonical numeric square records and their exact source-matrix meaning. -/
namespace GroupWL.SourceTableEncoding

open SourceLayout SourceTableCoefficients
open MachinePrograms

variable {T E : Type} {r : ℕ} (p : ℕ) [Fact p.Prime]
  (C : ComparisonData (ZMod p) T E r) (L : ℕ)
variable [FiniteCode (C.Horizontal L)] [FiniteCode (C.Vertical L)] [FiniteCode (C.Square L)]

abbrev horizontalCount := FiniteCode.size (C.Horizontal L)
abbrev squareCount := FiniteCode.size (C.Square L)
abbrev readoutCount := FiniteCode.size (C.Readout L)
abbrev blockCount := FiniteCode.size (C.Block L)

def readoutIndex (j : C.Readout L) : ℕ := (FiniteCode.equiv (α := C.Readout L) j).val

def blockIndex (B : C.Block L) : ℕ := (FiniteCode.equiv (α := C.Block L) B).val

@[simp] theorem readoutIndex_inj (j k : C.Readout L) :
    readoutIndex p C L j = readoutIndex p C L k ↔ j=k := by
  unfold readoutIndex
  rw [← Fin.ext_iff]
  exact (FiniteCode.equiv (α := C.Readout L)).injective.eq_iff

@[simp] theorem blockIndex_site (h : C.Horizontal L) :
    blockIndex p C L (.inl h) = (FiniteCode.equiv (α := C.Horizontal L) h).val := rfl

@[simp] theorem blockIndex_square (s : C.Square L) :
    blockIndex p C L (.inr s) = horizontalCount p C L+(FiniteCode.equiv (α := C.Square L) s).val := rfl

@[simp] theorem readoutIndex_site (h : C.Horizontal L) :
    readoutIndex p C L (.inl h) = (FiniteCode.equiv (α := C.Horizontal L) h).val := rfl

def idArray (f : C.Square L → C.Readout L) : List ℕ :=
  List.ofFn (fun i : Fin (squareCount p C L) =>
    readoutIndex p C L (f ((FiniteCode.equiv (α := C.Square L)).symm i)))

def formArray (f : C.Square L → ℕ → ZMod p) : List ℕ :=
  List.ofFn (fun i : Fin (squareCount p C L*2) =>
    (f ((FiniteCode.equiv (α := C.Square L)).symm
      ⟨i.val/2,(Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).2 i.isLt⟩) (i.val%2)).val)

def coefficientData : SourceCoefficients.Arr → List ℕ
  | .left => idArray p C L (fun s => .inl (C.squareLeft L s))
  | .right => idArray p C L (fun s => .inl (C.squareRight L s))
  | .after => idArray p C L (fun s => .inr (C.squareAfter L s))
  | .before => idArray p C L (fun s => .inr (C.squareBefore L s))
  | .leftForm => formArray p C L (leftEntry C L)
  | .rightForm => formArray p C L (rightEntry C L)

def incidenceData : SourceIncidence.Arr → List ℕ
  | .left => coefficientData p C L .left
  | .right => coefficientData p C L .right
  | .after => coefficientData p C L .after
  | .before => coefficientData p C L .before

theorem idArray_read (f : C.Square L → C.Readout L) (s : C.Square L) :
    (idArray p C L f)[(FiniteCode.equiv (α := C.Square L) s).val]?.getD 0 = readoutIndex p C L (f s) := by
  simp [idArray]

theorem formArray_read (f : C.Square L → ℕ → ZMod p) (s : C.Square L) (k : ℕ) (hk : k<2) :
    (formArray p C L f)[2*(FiniteCode.equiv (α := C.Square L) s).val+k]?.getD 0 = (f s k).val := by
  let c := FiniteCode.equiv (α := C.Square L) s
  have hc : c.val < squareCount p C L := c.isLt
  have hi : 2*c.val+k < squareCount p C L*2 := by omega
  have hdiv : (2*c.val+k)/2 = c.val := by omega
  have hmod : (2*c.val+k)%2 = k := by omega
  have he : (⟨(2*c.val+k)/2,(Nat.div_lt_iff_lt_mul (by decide : 0<2)).2 hi⟩ :
      Fin (squareCount p C L)) = c := Fin.ext hdiv
  change (formArray p C L f)[2*c.val+k]?.getD 0 = _
  simp only [formArray,List.getElem?_ofFn,hi,dif_pos,Option.getD_some,he,hmod,c,
    Equiv.symm_apply_apply]

theorem coefficientData_valid : SourceCoefficientTable.RecordsValid (coefficientData p C L)
    (horizontalCount p C L) p (blockCount p C L) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  refine ⟨hp,by change _ ≤ horizontalCount p C L+squareCount p C L; omega,?_,?_⟩
  · intro a ha hb
    cases a <;> simp_all [coefficientData,idArray,blockCount,FiniteCode.size]
  · have hf (f : C.Square L → ℕ → ZMod p) :
        2*(blockCount p C L-horizontalCount p C L) ≤ (formArray p C L f).length ∧
        ∀ i < 2*(blockCount p C L-horizontalCount p C L),
          (formArray p C L f)[i]?.getD 0 < p := by
      constructor
      · change 2*((horizontalCount p C L+squareCount p C L)-horizontalCount p C L) ≤
          (formArray p C L f).length
        simp only [formArray,List.length_ofFn,Nat.add_sub_cancel_left]
        omega
      · intro i hi
        have hn : i < squareCount p C L*2 := by
          change i < 2*((horizontalCount p C L+squareCount p C L)-horizontalCount p C L) at hi
          omega
        simp only [formArray,List.getElem?_ofFn,hn,dif_pos,Option.getD_some]
        exact ZMod.val_lt _
    intro a ha
    rcases ha with rfl | rfl
    · exact hf (leftEntry C L)
    · exact hf (rightEntry C L)

theorem incidenceData_valid : SourceIncidenceTable.RecordsValid (incidenceData p C L)
    (horizontalCount p C L) (blockCount p C L) := by
  refine ⟨by change _ ≤ horizontalCount p C L+squareCount p C L; omega,?_⟩
  intro a
  cases a <;> simp [incidenceData,coefficientData,idArray,blockCount,FiniteCode.size]

end GroupWL.SourceTableEncoding
