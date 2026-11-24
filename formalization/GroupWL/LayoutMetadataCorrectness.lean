import GroupWL.LayoutMetadata
import GroupWL.ComparisonMetadataRead
import GroupWL.FiniteBoolCodeRanks
import GroupWL.FiniteCodeRanks

/-! The flat metadata arrays use the canonical dependent finite codes of
the source layout. -/
namespace GroupWL.LayoutMetadata
open SourceLayout
open scoped BigOperators
variable {T E : Type} [FiniteCode T] [FiniteCode E] {r : ℕ}
  (p : ℕ) [Fact p.Prime] (C : ComparisonData (ZMod p) T E r) (L : ℕ)

@[simp] theorem nodeCount_eq : nodeCount (ComparisonMetadata.ofComparison p C) L=
    FiniteCode.size (Node T E L) := rfl
@[simp] theorem linkCount_eq : linkCount (ComparisonMetadata.ofComparison p C) L=
    FiniteCode.size (Link E L) := rfl

theorem node_real_val (t : T) : (FiniteCode.equiv (Sum.inl t : Node T E L)).val=(FiniteCode.equiv t).val := rfl

theorem node_wire_val (e : E) (j : Fin (L+1)) :
    (FiniteCode.equiv (Sum.inr (e,j) : Node T E L)).val=
      FiniteCode.size T+(FiniteCode.equiv e).val*(L+1)+j.val := by
  change FiniteCode.size T+(j.val+(L+1)*(FiniteCode.equiv e).val)=_
  ring

theorem link_first_val (e : E) : (FiniteCode.equiv (Link.first e : Link E L)).val=(FiniteCode.equiv e).val := rfl

theorem link_middle_val (e : E) (j : Fin L) :
    (FiniteCode.equiv (Link.middle e j : Link E L)).val=
      FiniteCode.size E+(FiniteCode.equiv e).val*L+j.val := by
  change FiniteCode.size E+(j.val+L*(FiniteCode.equiv e).val)=_
  ring

theorem link_last_val (e : E) : (FiniteCode.equiv (Link.last e : Link E L)).val=
    FiniteCode.size E+FiniteCode.size E*L+(FiniteCode.equiv e).val := rfl

theorem packed_div (a d b : ℕ) (hb : b<d) : (d*a+b)/d=a := by
  have hd : 0<d := lt_of_le_of_lt (Nat.zero_le _) hb
  rw [Nat.mul_add_div hd,Nat.div_eq_of_lt hb,Nat.add_zero]

theorem packed_mod (a d b : ℕ) (hb : b<d) : (d*a+b)%d=b := by
  rw [Nat.mul_add_mod,Nat.mod_eq_of_lt hb]

theorem nodeLabel_key (t : Node T E L) (i : Fin r) (a : Bool) :
    nodeLabel (ComparisonMetadata.ofComparison p C) L
      (2*((FiniteCode.equiv t).val*r+i.val)+(FiniteCode.equiv a).val)=
      FiniteCode.boolFlag (C.labelDomain L t i) a := by
  have hab : (FiniteCode.equiv a).val<2 := (FiniteCode.equiv a).isLt
  have hdiv : ((FiniteCode.equiv t).val*r+i.val)/r=(FiniteCode.equiv t).val := by
    simpa only [Nat.mul_comm] using packed_div (FiniteCode.equiv t).val r i.val i.isLt
  have hmod : ((FiniteCode.equiv t).val*r+i.val)%r=i.val := by
    simpa only [Nat.mul_comm] using packed_mod (FiniteCode.equiv t).val r i.val i.isLt
  simp only [nodeLabel,ComparisonMetadata.ofComparison,
    packed_div _ 2 _ hab,packed_mod _ 2 _ hab,hdiv,hmod]
  cases t with
  | inl t =>
      rw [node_real_val,if_pos (FiniteCode.equiv t).isLt]
      simp [FiniteCode.boolFlag,ComparisonData.labelDomain]
  | inr z =>
      rcases z with ⟨e,j⟩
      rw [node_wire_val]
      have hnot : ¬FiniteCode.size T+(FiniteCode.equiv e).val*(L+1)+j.val<FiniteCode.size T := by omega
      rw [if_neg hnot]
      have hsub : FiniteCode.size T+(FiniteCode.equiv e).val*(L+1)+j.val-FiniteCode.size T=
          (L+1)*(FiniteCode.equiv e).val+j.val := by
        simp only [Nat.add_assoc,Nat.add_sub_cancel_left,Nat.mul_comm]
      rw [hsub,packed_div _ _ _ j.isLt]
      exact ComparisonMetadata.domain_read p C e i a

theorem linkComparison_code (l : Link E L) :
    linkComparison (ComparisonMetadata.ofComparison p C) L (FiniteCode.equiv l).val=
      (FiniteCode.equiv l.comparison).val := by
  cases l with
  | first e =>
      simp only [linkComparison,ComparisonMetadata.ofComparison,link_first_val,
        if_pos (FiniteCode.equiv e).isLt,Link.comparison]
  | middle e j =>
      rw [link_middle_val]
      have hnot : ¬FiniteCode.size E+(FiniteCode.equiv e).val*L+j.val<FiniteCode.size E := by omega
      have hlt : FiniteCode.size E+(FiniteCode.equiv e).val*L+j.val<FiniteCode.size E+FiniteCode.size E*L := by
        have := (finProdFinEquiv (FiniteCode.equiv e,j)).isLt
        change j.val+L*(FiniteCode.equiv e).val<FiniteCode.size E*L at this
        nlinarith
      simp only [linkComparison,ComparisonMetadata.ofComparison,if_neg hnot,if_pos hlt,Link.comparison]
      have hsub : FiniteCode.size E+(FiniteCode.equiv e).val*L+j.val-FiniteCode.size E=
          L*(FiniteCode.equiv e).val+j.val := by
        simp only [Nat.add_assoc,Nat.add_sub_cancel_left,Nat.mul_comm]
      rw [hsub,packed_div _ _ _ j.isLt]
  | last e =>
      rw [link_last_val]
      have hnot : ¬FiniteCode.size E+FiniteCode.size E*L+(FiniteCode.equiv e).val<FiniteCode.size E := by omega
      have hnot' : ¬FiniteCode.size E+FiniteCode.size E*L+(FiniteCode.equiv e).val<FiniteCode.size E+FiniteCode.size E*L := by omega
      simp only [linkComparison,ComparisonMetadata.ofComparison,if_neg hnot,if_neg hnot',Link.comparison]
      omega

theorem linkLabel_key (l : Link E L) (i : Fin r) (a : Bool) :
    linkLabel (ComparisonMetadata.ofComparison p C) L
      (2*((FiniteCode.equiv l).val*r+i.val)+(FiniteCode.equiv a).val)=
      FiniteCode.boolFlag (C.domain l.comparison i) a := by
  have hab : (FiniteCode.equiv a).val<2 := (FiniteCode.equiv a).isLt
  have hdiv : ((FiniteCode.equiv l).val*r+i.val)/r=(FiniteCode.equiv l).val := by
    simpa only [Nat.mul_comm] using packed_div (FiniteCode.equiv l).val r i.val i.isLt
  have hmod : ((FiniteCode.equiv l).val*r+i.val)%r=i.val := by
    simpa only [Nat.mul_comm] using packed_mod (FiniteCode.equiv l).val r i.val i.isLt
  simp only [linkLabel,ComparisonMetadata.ofComparison,
    packed_div _ 2 _ hab,packed_mod _ 2 _ hab,hdiv,hmod]
  have hlink := linkComparison_code p C L l
  dsimp only [ComparisonMetadata.ofComparison] at hlink
  rw [hlink]
  exact ComparisonMetadata.domain_read p C l.comparison i a

end GroupWL.LayoutMetadata
