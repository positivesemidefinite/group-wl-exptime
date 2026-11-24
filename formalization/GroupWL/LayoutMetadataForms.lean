import GroupWL.LayoutMetadataEndpoints

/-! Numeric source forms and dimensions agree with the actual coordinate
vectors of the typed source tensor. -/
namespace GroupWL.LayoutMetadata
open SourceLayout ConstructiveCoordinates
variable {T E : Type} [FiniteCode T] [FiniteCode E] {r : ℕ}
  (p : ℕ) [Fact p.Prime] (C : ComparisonData (ZMod p) T E r) (L : ℕ)

theorem nodeDimension_correct (t : Node T E L) :
    nodeDimension (ComparisonMetadata.ofComparison p C) L (FiniteCode.equiv t).val=
      (ComputableSource.nodeCoordinates (L:=L) C t).dimension := by
  cases t with
  | inl t =>
      simp only [nodeDimension,ComparisonMetadata.ofComparison,node_real_val,
        if_pos (FiniteCode.equiv t).isLt,ComputableSource.nodeCoordinates,Coordinates.pi]
      exact ComparisonMetadata.dimensions_read p C t
  | inr z =>
      rcases z with ⟨e,j⟩
      have hn : ¬FiniteCode.size T+(FiniteCode.equiv e).val*(L+1)+j.val<FiniteCode.size T := by omega
      simp only [nodeDimension,ComparisonMetadata.ofComparison,node_wire_val,if_neg hn,
        ComputableSource.nodeCoordinates,Coordinates.scalar]

theorem leftForm_correct (s : C.Square L) (k : Fin 2) :
    leftForm (ComparisonMetadata.ofComparison p C) L (FiniteCode.equiv s.1).val k.val=
      (SourceTableCoefficients.leftEntry C L s k.val).val := by
  letI : Fact (1<p) := ⟨(Fact.out : p.Prime).one_lt⟩
  rcases s with ⟨l,i,a,b⟩
  cases l with
  | first e =>
      simp only [leftForm,ComparisonMetadata.ofComparison,link_first_val,if_pos (FiniteCode.equiv e).isLt]
      change (ComparisonMetadata.sourceForm p C)[2*(FiniteCode.equiv e).val+k.val]?.getD 0=
        (C.sourceForm e (ComparisonMetadata.unit p C (C.source e) k)).val
      exact ComparisonMetadata.sourceForm_read p C e k
  | middle e j =>
      simp only [leftForm,ComparisonMetadata.ofComparison,link_middle_val,if_neg (middle_bounds L e j).1]
      change (if k.val=0 then 1 else 0)=(if (0:ℕ)=k.val then (1:ZMod p) else 0).val
      split_ifs <;> simp_all [ZMod.val_one,eq_comm]
  | last e =>
      simp only [leftForm,ComparisonMetadata.ofComparison,link_last_val,if_neg (last_bounds L e).1]
      change (if k.val=0 then 1 else 0)=(if (0:ℕ)=k.val then (1:ZMod p) else 0).val
      split_ifs <;> simp_all [ZMod.val_one,eq_comm]

theorem rightForm_correct (s : C.Square L) (k : Fin 2) :
    rightForm (ComparisonMetadata.ofComparison p C) L (FiniteCode.equiv s.1).val k.val=
      (SourceTableCoefficients.rightEntry C L s k.val).val := by
  letI : Fact (1<p) := ⟨(Fact.out : p.Prime).one_lt⟩
  rcases s with ⟨l,i,a,b⟩
  cases l with
  | first e =>
      have hlt : (FiniteCode.equiv e).val<FiniteCode.size E+FiniteCode.size E*L := by have := (FiniteCode.equiv e).isLt; omega
      simp only [rightForm,ComparisonMetadata.ofComparison,link_first_val,if_pos hlt]
      change (if k.val=0 then 1 else 0)=(if (0:ℕ)=k.val then (1:ZMod p) else 0).val
      split_ifs <;> simp_all [ZMod.val_one,eq_comm]
  | middle e j =>
      simp only [rightForm,ComparisonMetadata.ofComparison,link_middle_val,if_pos (middle_bounds L e j).2]
      change (if k.val=0 then 1 else 0)=(if (0:ℕ)=k.val then (1:ZMod p) else 0).val
      split_ifs <;> simp_all [ZMod.val_one,eq_comm]
  | last e =>
      have hl := linkComparison_code p C L (Link.last e)
      simp only [ComparisonMetadata.ofComparison,link_last_val,Link.comparison] at hl
      simp only [rightForm,ComparisonMetadata.ofComparison,link_last_val,if_neg (last_bounds L e).2,hl]
      change (ComparisonMetadata.targetForm p C)[2*(FiniteCode.equiv e).val+k.val]?.getD 0=
        (C.targetForm e (ComparisonMetadata.unit p C (C.target e) k)).val
      exact ComparisonMetadata.targetForm_read p C e k

end GroupWL.LayoutMetadata
