import GroupWL.SourceTableEncoding

/-! The materialized natural tables compute the original affine source
coefficients and its full incidence relation, including zero coefficients. -/
namespace GroupWL.SourceTableEncoding

open SourceLayout SourceTableCoefficients SourceCoefficientResidues MachinePrograms

variable {T E : Type} {r : ℕ} (p : ℕ) [Fact p.Prime]
  (C : ComparisonData (ZMod p) T E r) (L : ℕ)
variable [FiniteCode (C.Horizontal L)] [FiniteCode (C.Vertical L)] [FiniteCode (C.Square L)]

theorem incidence_correct (B : C.Block L) (j : C.Readout L) :
    SourceIncidence.incidence (SourceIncidenceTable.sourceState (incidenceData p C L)
      (horizontalCount p C L) (blockIndex p C L B) (readoutIndex p C L j)) =
      if j ∈ ComputableSource.scope C B then 1 else 0 := by
  classical
  cases B with
  | inl h =>
    have hh : (FiniteCode.equiv (α := C.Horizontal L) h).val < horizontalCount p C L :=
      (FiniteCode.equiv (α := C.Horizontal L) h).isLt
    have he : (FiniteCode.equiv (α := C.Horizontal L) h).val = readoutIndex p C L j ↔ j = .inl h := by
      rw [← readoutIndex_site p C L h,readoutIndex_inj]
      exact eq_comm
    simp only [SourceIncidence.incidence,SourceIncidenceTable.sourceState,blockIndex_site,
      hh,if_true,he,SourceTableCoefficients.scope_site]
  | inr s =>
    have hn : ¬horizontalCount p C L+(FiniteCode.equiv (α := C.Square L) s).val < horizontalCount p C L := by omega
    simp only [SourceIncidence.incidence,SourceIncidenceTable.sourceState,blockIndex_square,hn,if_false,
      Nat.add_sub_cancel_left,SourceIncidence.read,incidenceData,coefficientData,idArray_read,
      readoutIndex_inj,SourceTableCoefficients.scope_square]

theorem coefficient_correct (B : C.Block L) (j : C.Readout L) (k : ℕ) (hk : k<2) :
    (SourceCoefficients.coefficient (SourceCoefficientTable.sourceState (coefficientData p C L)
      (horizontalCount p C L) p (blockIndex p C L B) (readoutIndex p C L j) k) : ZMod p) =
      entry C L B j k := by
  cases B with
  | inl h =>
    have hh : (FiniteCode.equiv (α := C.Horizontal L) h).val < horizontalCount p C L :=
      (FiniteCode.equiv (α := C.Horizontal L) h).isLt
    simp only [SourceCoefficients.coefficient,SourceCoefficientTable.sourceState,blockIndex_site,
      hh,if_true,Nat.cast_zero,entry_site]
  | inr s =>
    have hn : ¬horizontalCount p C L+(FiniteCode.equiv (α := C.Square L) s).val < horizontalCount p C L := by omega
    simp only [SourceCoefficients.coefficient,SourceCoefficientTable.sourceState,blockIndex_square,
      hn,if_false,Nat.add_sub_cancel_left,SourceCoefficients.read,coefficientData,idArray_read,
      formArray_read p C L _ s k hk]
    let dl := SourceCoefficients.delta (readoutIndex p C L j) (readoutIndex p C L (.inl (C.squareLeft L s)))
    let dr := SourceCoefficients.delta (readoutIndex p C L j) (readoutIndex p C L (.inl (C.squareRight L s)))
    let da := SourceCoefficients.delta (readoutIndex p C L j) (readoutIndex p C L (.inr (C.squareAfter L s)))
    let db := SourceCoefficients.delta (readoutIndex p C L j) (readoutIndex p C L (.inr (C.squareBefore L s)))
    let dk := SourceCoefficients.delta k 0
    have hr : (rightEntry C L s k).val*dr ≤ p := by
      calc
        _ ≤ (rightEntry C L s k).val*1 := Nat.mul_le_mul_left _ (delta_le_one _ _)
        _ ≤ p := by simpa using (ZMod.val_lt (rightEntry C L s k)).le
    have hb : db*dk ≤ p := by
      have h := Nat.mul_le_mul (delta_le_one (readoutIndex p C L j)
        (readoutIndex p C L (.inr (C.squareBefore L s)))) (delta_le_one k 0)
      have hp : 0 < p := (Fact.out : p.Prime).pos
      change db*dk ≤ p
      change db*dk ≤ 1*1 at h
      omega
    change (signedResidue p ((leftEntry C L s k).val*dl) ((rightEntry C L s k).val*dr)
      (da*dk) (db*dk) : ZMod p) = _
    rw [signedResidue_cast _ _ _ _ _ hr hb,entry_square]
    simp only [dl,dr,da,db,dk,Nat.cast_mul,ZMod.natCast_zmod_val,delta_cast,
      readoutIndex_inj,mul_ite,mul_one,mul_zero]
    split_ifs <;> simp_all

end GroupWL.SourceTableEncoding
