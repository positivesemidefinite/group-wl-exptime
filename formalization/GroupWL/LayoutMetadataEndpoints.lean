import GroupWL.LayoutMetadataRanks
import GroupWL.SourceTableEncoding

/-! The flat square incidence indices are exactly the typed source-layout
endpoint readout codes. -/
namespace GroupWL.LayoutMetadata
open SourceLayout
variable {T E : Type} [FiniteCode T] [FiniteCode E] {r : ℕ}
  (p : ℕ) [Fact p.Prime] (C : ComparisonData (ZMod p) T E r) (L : ℕ)

theorem middle_bounds (e : E) (j : Fin L) :
    ¬FiniteCode.size E+(FiniteCode.equiv e).val*L+j.val<FiniteCode.size E ∧
    FiniteCode.size E+(FiniteCode.equiv e).val*L+j.val<FiniteCode.size E+FiniteCode.size E*L := by
  refine ⟨by omega,?_⟩
  have h := (finProdFinEquiv (FiniteCode.equiv e,j)).isLt
  change j.val+L*(FiniteCode.equiv e).val<FiniteCode.size E*L at h
  nlinarith

theorem last_bounds (e : E) :
    ¬FiniteCode.size E+FiniteCode.size E*L+(FiniteCode.equiv e).val<FiniteCode.size E ∧
    ¬FiniteCode.size E+FiniteCode.size E*L+(FiniteCode.equiv e).val<FiniteCode.size E+FiniteCode.size E*L := by
  constructor <;> omega

theorem middle_sub (e : E) (j : Fin L) :
    FiniteCode.size E+(FiniteCode.equiv e).val*L+j.val-FiniteCode.size E=L*(FiniteCode.equiv e).val+j.val := by
  simp only [Nat.add_assoc,Nat.add_sub_cancel_left,Nat.mul_comm]

theorem leftNode_code (l : Link E L) :
    leftNode (ComparisonMetadata.ofComparison p C) L (FiniteCode.equiv l).val=
      (FiniteCode.equiv (C.leftNode L l)).val := by
  cases l with
  | first e =>
      simp only [leftNode,ComparisonMetadata.ofComparison,link_first_val,if_pos (FiniteCode.equiv e).isLt,
        ComparisonData.leftNode,node_real_val]
      exact ComparisonMetadata.source_read p C e
  | middle e j =>
      simp only [leftNode,ComparisonMetadata.ofComparison,link_middle_val,
        if_neg (middle_bounds L e j).1,if_pos (middle_bounds L e j).2,
        middle_sub,packed_div _ _ _ j.isLt,packed_mod _ _ _ j.isLt,ComparisonData.leftNode,node_wire_val,Fin.val_castSucc]
  | last e =>
      simp only [leftNode,ComparisonMetadata.ofComparison,link_last_val,
        if_neg (last_bounds L e).1,if_neg (last_bounds L e).2,Nat.add_sub_cancel_left,
        ComparisonData.leftNode,node_wire_val,Fin.val_last]

theorem rightNode_code (l : Link E L) :
    rightNode (ComparisonMetadata.ofComparison p C) L (FiniteCode.equiv l).val=
      (FiniteCode.equiv (C.rightNode L l)).val := by
  cases l with
  | first e =>
      simp only [rightNode,ComparisonMetadata.ofComparison,link_first_val,if_pos (FiniteCode.equiv e).isLt,
        ComparisonData.rightNode,node_wire_val,Fin.val_zero,Nat.add_zero]
  | middle e j =>
      simp only [rightNode,ComparisonMetadata.ofComparison,link_middle_val,
        if_neg (middle_bounds L e j).1,if_pos (middle_bounds L e j).2,
        middle_sub,packed_div _ _ _ j.isLt,packed_mod _ _ _ j.isLt,ComparisonData.rightNode,node_wire_val,Fin.val_succ]
      omega
  | last e =>
      simp only [rightNode,ComparisonMetadata.ofComparison,link_last_val,
        if_neg (last_bounds L e).1,if_neg (last_bounds L e).2,Nat.add_sub_cancel_left,
        ComparisonData.rightNode,node_real_val]
      exact ComparisonMetadata.target_read p C e

theorem permutation_bool_code (e : Equiv.Perm Bool) (a : Bool) :
    (FiniteCode.equiv (e a)).val=(if (if e false then 1 else 0 : ℕ)=0 then
      (FiniteCode.equiv a).val else 1-(FiniteCode.equiv a).val) := by
  cases ha : e false <;> cases a
  · simp [ha]
  · have hb : e true=true := by
      cases hb : e true
      · have hh := e.injective (ha.trans hb.symm); cases hh
      · rfl
    simp [ha,hb]
  · simp [ha]
  · have hb : e true=false := by
      cases hb : e true
      · rfl
      · have hh := e.injective (ha.trans hb.symm); cases hh
    simp [ha,hb]

theorem rightLabel_code (l : Link E L) (i : Fin r) (a : C.DomainLabel l.comparison i) :
    rightLabel (ComparisonMetadata.ofComparison p C) L (FiniteCode.equiv l).val i.val (FiniteCode.equiv a.val).val=
      (FiniteCode.equiv (C.rightLabel L l i a).val).val := by
  cases l with
  | first e =>
      have hlt : (FiniteCode.equiv e).val<FiniteCode.size E+FiniteCode.size E*L := by have := (FiniteCode.equiv e).isLt; omega
      simp only [rightLabel,ComparisonMetadata.ofComparison,link_first_val,if_pos hlt,ComparisonData.rightLabel]
  | middle e j =>
      simp only [rightLabel,ComparisonMetadata.ofComparison,link_middle_val,
        if_pos (middle_bounds L e j).2,ComparisonData.rightLabel]
  | last e =>
      have hl := linkComparison_code p C L (Link.last e)
      simp only [ComparisonMetadata.ofComparison,link_last_val,Link.comparison] at hl
      simp only [rightLabel,ComparisonMetadata.ofComparison,link_last_val,
        if_neg (last_bounds L e).2,hl,ComparisonData.rightLabel]
      rw [ComparisonMetadata.permutation_read]
      exact (permutation_bool_code (C.permutation e i) a.val).symm

theorem leftLabel_val (l : Link E L) (i : Fin r) (a : C.DomainLabel l.comparison i) :
    (C.leftLabel L l i a).val=a.val := by cases l <;> rfl

def squareKey (s : C.Square L) : ℕ :=
  horizontalKey (ComparisonMetadata.ofComparison p C) (FiniteCode.equiv s.1).val s.2.1.val
    (FiniteCode.equiv s.2.2.1.val).val (FiniteCode.equiv s.2.2.2.val).val

theorem squareKey_parts (s : C.Square L) :
    squareKey p C L s/4/r=(FiniteCode.equiv s.1).val ∧
    squareKey p C L s/4%r=s.2.1.val ∧
    squareKey p C L s%4/2=(FiniteCode.equiv s.2.2.1.val).val ∧
    squareKey p C L s%4%2=(FiniteCode.equiv s.2.2.2.val).val := by
  have ha : (FiniteCode.equiv s.2.2.1.val).val<2 := (FiniteCode.equiv s.2.2.1.val).isLt
  have hb : (FiniteCode.equiv s.2.2.2.val).val<2 := (FiniteCode.equiv s.2.2.2.val).isLt
  have hbits : 2*(FiniteCode.equiv s.2.2.1.val).val+(FiniteCode.equiv s.2.2.2.val).val<4 := by omega
  have hd : ((FiniteCode.equiv s.1).val*r+s.2.1.val)/r=(FiniteCode.equiv s.1).val := by
    simpa only [Nat.mul_comm] using packed_div (FiniteCode.equiv s.1).val r s.2.1.val s.2.1.isLt
  have hm : ((FiniteCode.equiv s.1).val*r+s.2.1.val)%r=s.2.1.val := by
    simpa only [Nat.mul_comm] using packed_mod (FiniteCode.equiv s.1).val r s.2.1.val s.2.1.isLt
  simp only [squareKey,horizontalKey,ComparisonMetadata.ofComparison,Nat.add_assoc,
    packed_div _ _ _ hbits,packed_mod _ _ _ hbits,hd,hm,packed_div _ _ _ hb,packed_mod _ _ _ hb,and_self]

theorem squareLeft_correct (s : C.Square L) :
    squareLeft (ComparisonMetadata.ofComparison p C) L (squareKey p C L s)=
      SourceTableEncoding.readoutIndex p C L (.inl (C.squareLeft L s)) := by
  have hs := squareKey_parts p C L s
  simp only [squareLeft,ComparisonMetadata.ofComparison,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2]
  have hn := leftNode_code p C L s.1
  dsimp only [ComparisonMetadata.ofComparison] at hn
  rw [hn]
  have h := horizontalRank_correct p C L (C.squareLeft L s)
  have hal : (C.leftLabel L s.1 s.2.1 s.2.2.1).val=s.2.2.1.val := leftLabel_val p C L _ _ _
  have hbl : (C.leftLabel L s.1 (finRotate r s.2.1) s.2.2.2).val=s.2.2.2.val := leftLabel_val p C L _ _ _
  simpa only [SourceTableEncoding.readoutIndex_site,ComparisonData.squareLeft,hal,hbl,ComparisonMetadata.ofComparison] using h

theorem squareRight_correct (s : C.Square L) :
    squareRight (ComparisonMetadata.ofComparison p C) L (squareKey p C L s)=
      SourceTableEncoding.readoutIndex p C L (.inl (C.squareRight L s)) := by
  have hs := squareKey_parts p C L s
  simp only [squareRight,ComparisonMetadata.ofComparison,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2]
  have hn := rightNode_code p C L s.1
  have ha := rightLabel_code p C L s.1 s.2.1 s.2.2.1
  have hb := rightLabel_code p C L s.1 (finRotate r s.2.1) s.2.2.2
  dsimp only [ComparisonMetadata.ofComparison] at hn ha hb
  rw [hn,ha,←rotate_val s.2.1,hb]
  exact horizontalRank_correct p C L (C.squareRight L s)

theorem squareBefore_correct (s : C.Square L) :
    squareBefore (ComparisonMetadata.ofComparison p C) L (squareKey p C L s)=
      SourceTableEncoding.readoutIndex p C L (.inr (C.squareBefore L s)) := by
  have hs := squareKey_parts p C L s
  simp only [squareBefore,ComparisonMetadata.ofComparison,hs.1,hs.2.1,hs.2.2.1]
  have h := verticalRank_correct p C L (C.squareBefore L s)
  have hc := horizontalCount_correct p C L
  dsimp only [ComparisonMetadata.ofComparison] at h hc
  rw [hc]
  exact congrArg (FiniteCode.size (C.Horizontal L)+·) h

theorem squareAfter_correct (s : C.Square L) :
    squareAfter (ComparisonMetadata.ofComparison p C) L (squareKey p C L s)=
      SourceTableEncoding.readoutIndex p C L (.inr (C.squareAfter L s)) := by
  have hs := squareKey_parts p C L s
  simp only [squareAfter,ComparisonMetadata.ofComparison,hs.1,hs.2.1,hs.2.2.2]
  rw [←rotate_val s.2.1]
  have h := verticalRank_correct p C L (C.squareAfter L s)
  have hc := horizontalCount_correct p C L
  dsimp only [ComparisonMetadata.ofComparison] at h hc
  rw [hc]
  exact congrArg (FiniteCode.size (C.Horizontal L)+·) h

end GroupWL.LayoutMetadata
