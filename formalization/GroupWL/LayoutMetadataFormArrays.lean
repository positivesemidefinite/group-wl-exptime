import GroupWL.LayoutMetadataArrays
import GroupWL.MachinePrograms.DuplicateFlags
import GroupWL.MachinePrograms.LinkFormRecords

/-! The executed repeated and filtered form records are the canonical two-coefficient square arrays. -/
namespace GroupWL.LayoutMetadata
open SourceLayout MachinePrograms
variable {T E : Type} [FiniteCode T] [FiniteCode E] {r : ℕ}
  (p : ℕ) [Fact p.Prime] (C : ComparisonData (ZMod p) T E r) (L : ℕ)

theorem square_pair_compaction (values : List ℕ) (f : C.Square L → Fin 2 → ℕ)
    (read : ∀s k,values[2*squareKey p C L s+k.val]?.getD 0=f s k) :
    SelectArray.selectedPrefix (DuplicateFlags.word (squareFlags (ComparisonMetadata.ofComparison p C) L)) values
      (DuplicateFlags.word (squareFlags (ComparisonMetadata.ofComparison p C) L)).length=
      List.ofFn (fun i : Fin (FiniteCode.size (C.Square L)*2) =>
        f (FiniteCode.equiv.symm i.divNat) i.modNat) := by
  let key : C.Square L×Fin 2 → ℕ := fun z => 2*squareKey p C L z.1+z.2.val
  have hh := FiniteCode.selectedPrefix_eq_ofFn
    (α:=C.Square L×Fin 2) (DuplicateFlags.word (squareFlags (ComparisonMetadata.ofComparison p C) L)) values
    (DuplicateFlags.word (squareFlags (ComparisonMetadata.ofComparison p C) L)).length key (fun z => f z.1 z.2)
    (DuplicateFlags.binary _ (squareFlags_binary p C L))
    (by rw [DuplicateFlags.length,DuplicateFlags.count_even _ _ le_rfl];
        change 2*squareCount _ _=FiniteCode.size (C.Square L)*2
        rw [squareCount_correct]; omega)
    (by intro z; dsimp [key]; rw [DuplicateFlags.length]; have := squareKey_lt p C L z.1; have := z.2.isLt; omega)
    (by intro z; dsimp [key]; rw [DuplicateFlags.read _ _ _ (squareKey_lt p C L z.1) z.2.isLt,squareKey_chosen])
    (by intro z; dsimp [key]; rw [DuplicateFlags.count_key _ _ _ (squareKey_lt p C L z.1) z.2.isLt (squareKey_chosen p C L z.1),
          show FilterRanks.count (squareFlags (ComparisonMetadata.ofComparison p C) L) (squareKey p C L z.1)=(FiniteCode.equiv z.1).val from squareRank_correct p C L z.1,
          FiniteCode.prod_val,FiniteCode.fin_val]; change _=(FiniteCode.equiv z.1).val*2+z.2.val; omega)
    (fun z => read z.1 z.2)
  exact hh

theorem linkForm_entry (right : Bool) (l : ℕ) (k : Fin 2) :
    LinkForms.entry right
      (if right then (ComparisonMetadata.ofComparison p C).targetForm else (ComparisonMetadata.ofComparison p C).sourceForm)
      (FiniteCode.size E) L (2*l+k.val)=
      if right then rightForm (ComparisonMetadata.ofComparison p C) L l k.val
        else leftForm (ComparisonMetadata.ofComparison p C) L l k.val := by
  have hd : (2*l+k.val)/2=l := by omega
  have hm : (2*l+k.val)%2=k.val := by omega
  cases right
  · simp only [Bool.false_eq_true,↓reduceIte,LinkForms.entry,LinkForms.cutoff,hd,hm,
      leftForm,ComparisonMetadata.ofComparison]
  · simp only [↓reduceIte,LinkForms.entry,LinkForms.cutoff,hd,hm,rightForm,ComparisonMetadata.ofComparison]
    by_cases h : l<FiniteCode.size E+FiniteCode.size E*L
    · simp [h]
    · have h' : ¬l<FiniteCode.size E := by omega
      have he : 2*l+k.val-2*(FiniteCode.size E+FiniteCode.size E*L)=
          2*(l-(FiniteCode.size E+FiniteCode.size E*L))+k.val := by omega
      simp only [if_neg h,linkComparison,if_neg h',ComparisonMetadata.ofComparison,if_neg h,he]

def repeatedForms (right : Bool) : List ℕ :=
  RepeatedSelection.repeated
    (LinkFormRecords.forms right (if right then ComparisonMetadata.targetForm p C else ComparisonMetadata.sourceForm p C)
      (FiniteCode.size E) L) (linkCount (ComparisonMetadata.ofComparison p C) L) 2 (4*r)

theorem repeatedForms_read (right : Bool) (s : C.Square L) (k : Fin 2) :
    (repeatedForms p C L right)[2*squareKey p C L s+k.val]?.getD 0=
      if right then (SourceTableCoefficients.rightEntry C L s k.val).val
        else (SourceTableCoefficients.leftEntry C L s k.val).val := by
  have hkey := squareKey_lt p C L s
  simp only [squareFlags,List.length_ofFn] at hkey
  change squareKey p C L s<linkCount (ComparisonMetadata.ofComparison p C) L*r*4 at hkey
  have hi : 2*squareKey p C L s+k.val<linkCount (ComparisonMetadata.ofComparison p C) L*2*(4*r) := by have := k.isLt; nlinarith
  have hd : (2*squareKey p C L s+k.val)/2=squareKey p C L s := by omega
  have hm : (2*squareKey p C L s+k.val)%2=k.val := by omega
  have hl : squareKey p C L s/(4*r)=(FiniteCode.equiv s.1).val := by
    rw [←Nat.div_div_eq_div_mul]
    exact (squareKey_parts p C L s).1
  have hlb : 2*(FiniteCode.equiv s.1).val+k.val<
      (FiniteCode.size E+FiniteCode.size E*L+FiniteCode.size E)*2 := by
    have hh : (FiniteCode.equiv s.1).val<FiniteCode.size E+FiniteCode.size E*L+FiniteCode.size E := (FiniteCode.equiv s.1).isLt
    have := k.isLt; omega
  simp only [repeatedForms,RepeatedSelection.repeated]
  rw [List.getElem?_ofFn,dif_pos hi]
  simp only [Option.getD_some,ArrayRepeatBlocks.entry,hd,hm,hl]
  rw [LinkFormRecords.forms,List.getElem?_ofFn,dif_pos (show (FiniteCode.equiv s.1).val*2+k.val<
    (FiniteCode.size E+FiniteCode.size E*L+FiniteCode.size E)*2 by omega)]
  simp only [Option.getD_some]
  rw [show (FiniteCode.equiv s.1).val*2+k.val=2*(FiniteCode.equiv s.1).val+k.val by omega]
  have he := linkForm_entry p C L right (FiniteCode.equiv s.1).val k
  change LinkForms.entry right
    (if right then (ComparisonMetadata.ofComparison p C).targetForm else (ComparisonMetadata.ofComparison p C).sourceForm)
    (FiniteCode.size E) L (2*(FiniteCode.equiv s.1).val+k.val)=_
  rw [he]
  cases right <;> simp only [Bool.false_eq_true,↓reduceIte,leftForm_correct,rightForm_correct]

def selectedForms (right : Bool) : List ℕ :=
  SelectArray.selectedPrefix (DuplicateFlags.word (squareFlags (ComparisonMetadata.ofComparison p C) L))
    (repeatedForms p C L right) (DuplicateFlags.word (squareFlags (ComparisonMetadata.ofComparison p C) L)).length

theorem selectedForms_correct (right : Bool) : selectedForms p C L right=
    SourceTableEncoding.coefficientData p C L (if right then .rightForm else .leftForm) := by
  rw [selectedForms,square_pair_compaction p C L _ _ (repeatedForms_read p C L right)]
  cases right <;> rfl

end GroupWL.LayoutMetadata
