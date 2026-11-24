import GroupWL.LayoutMetadataCorrectness
import GroupWL.FiniteCodeValues

/-! Pointwise semantics of the flattened source-layout predicate arrays. -/
namespace GroupWL.LayoutMetadata
open SourceLayout MachinePrograms
variable {T E : Type} [FiniteCode T] [FiniteCode E] {r : ℕ}
  (p : ℕ) [Fact p.Prime] (C : ComparisonData (ZMod p) T E r) (L : ℕ)

theorem key_lt {N r d a i b : ℕ} (ha : a<N) (hi : i<r) (hb : b<d) :
    d*(a*r+i)+b<N*r*d := by
  have h₁ := Nat.mul_le_mul_right r (Nat.succ_le_of_lt ha)
  have h₂ : a*r+i<N*r := by nlinarith
  have h₃ := Nat.mul_le_mul_left d (Nat.succ_le_of_lt h₂)
  nlinarith

theorem nodeLabels_read (t : Node T E L) (i : Fin r) (a : Bool) :
    (nodeLabels (ComparisonMetadata.ofComparison p C) L)[2*((FiniteCode.equiv t).val*r+i.val)+(FiniteCode.equiv a).val]?.getD 0=
      FiniteCode.boolFlag (C.labelDomain L t i) a := by
  have hi : 2*((FiniteCode.equiv t).val*r+i.val)+(FiniteCode.equiv a).val<
      nodeCount (ComparisonMetadata.ofComparison p C) L*r*2 := by
    rw [nodeCount_eq]
    exact key_lt (FiniteCode.equiv t).isLt i.isLt (FiniteCode.equiv a).isLt
  simp only [nodeLabels,List.getElem?_ofFn]
  split_ifs with h
  · exact nodeLabel_key p C L t i a
  · exact (h hi).elim

theorem linkLabels_read (l : Link E L) (i : Fin r) (a : Bool) :
    (linkLabels (ComparisonMetadata.ofComparison p C) L)[2*((FiniteCode.equiv l).val*r+i.val)+(FiniteCode.equiv a).val]?.getD 0=
      FiniteCode.boolFlag (C.domain l.comparison i) a := by
  have hi : 2*((FiniteCode.equiv l).val*r+i.val)+(FiniteCode.equiv a).val<
      linkCount (ComparisonMetadata.ofComparison p C) L*r*2 := by
    rw [linkCount_eq]
    exact key_lt (FiniteCode.equiv l).isLt i.isLt (FiniteCode.equiv a).isLt
  simp only [linkLabels,List.getElem?_ofFn]
  split_ifs with h
  · exact linkLabel_key p C L l i a
  · exact (h hi).elim

theorem rotate_val (i : Fin r) : (finRotate r i).val=(i.val+1)%r := by
  haveI := i.neZero
  rw [finRotate_apply]
  rw [Fin.val_add,Fin.val_one',Nat.add_mod_mod]

theorem rectangle_key (xs : List ℕ) (row : ℕ) (i : Fin r) (a b : Bool) :
    RectangleFlags.entry xs r (4*(row*r+i.val)+2*(FiniteCode.equiv a).val+(FiniteCode.equiv b).val)=
      xs[2*(row*r+i.val)+(FiniteCode.equiv a).val]?.getD 0 *
        xs[2*(row*r+(finRotate r i).val)+(FiniteCode.equiv b).val]?.getD 0 := by
  have ha : (FiniteCode.equiv a).val<2 := (FiniteCode.equiv a).isLt
  have hb : (FiniteCode.equiv b).val<2 := (FiniteCode.equiv b).isLt
  have hbits : 2*(FiniteCode.equiv a).val+(FiniteCode.equiv b).val<4 := by omega
  have he : 4*(row*r+i.val)+2*(FiniteCode.equiv a).val+(FiniteCode.equiv b).val=
      4*(row*r+i.val)+(2*(FiniteCode.equiv a).val+(FiniteCode.equiv b).val) := by omega
  rw [he]
  simp only [RectangleFlags.entry,packed_div _ _ _ hbits,packed_mod _ _ _ hbits,
    packed_div _ _ _ hb,packed_mod _ _ _ hb]
  have hd : (row*r+i.val)/r=row := by simpa only [Nat.mul_comm] using packed_div row r i.val i.isLt
  have hm : (row*r+i.val)%r=i.val := by simpa only [Nat.mul_comm] using packed_mod row r i.val i.isLt
  rw [hd,hm,rotate_val]

theorem horizontalFlags_read (t : Node T E L) (i : Fin r) (a b : Bool) :
    (horizontalFlags (ComparisonMetadata.ofComparison p C) L)[4*((FiniteCode.equiv t).val*r+i.val)+2*(FiniteCode.equiv a).val+(FiniteCode.equiv b).val]?.getD 0=
      FiniteCode.boolFlag (C.labelDomain L t i) a *
        FiniteCode.boolFlag (C.labelDomain L t (finRotate r i)) b := by
  have ha : (FiniteCode.equiv a).val<2 := (FiniteCode.equiv a).isLt
  have hb : (FiniteCode.equiv b).val<2 := (FiniteCode.equiv b).isLt
  have hbits : 2*(FiniteCode.equiv a).val+(FiniteCode.equiv b).val<4 := by omega
  have hi : 4*((FiniteCode.equiv t).val*r+i.val)+2*(FiniteCode.equiv a).val+(FiniteCode.equiv b).val<
      nodeCount (ComparisonMetadata.ofComparison p C) L*r*4 := by
    rw [nodeCount_eq]
    simpa only [Nat.add_assoc] using key_lt (FiniteCode.equiv t).isLt i.isLt hbits
  simp only [horizontalFlags,List.getElem?_ofFn]
  split_ifs with h
  · change RectangleFlags.entry (nodeLabels (ComparisonMetadata.ofComparison p C) L) r _=_
    rw [rectangle_key,nodeLabels_read,nodeLabels_read]
  · exact (h hi).elim

theorem squareFlags_read (l : Link E L) (i : Fin r) (a b : Bool) :
    (squareFlags (ComparisonMetadata.ofComparison p C) L)[4*((FiniteCode.equiv l).val*r+i.val)+2*(FiniteCode.equiv a).val+(FiniteCode.equiv b).val]?.getD 0=
      FiniteCode.boolFlag (C.domain l.comparison i) a *
        FiniteCode.boolFlag (C.domain l.comparison (finRotate r i)) b := by
  have ha : (FiniteCode.equiv a).val<2 := (FiniteCode.equiv a).isLt
  have hb : (FiniteCode.equiv b).val<2 := (FiniteCode.equiv b).isLt
  have hbits : 2*(FiniteCode.equiv a).val+(FiniteCode.equiv b).val<4 := by omega
  have hi : 4*((FiniteCode.equiv l).val*r+i.val)+2*(FiniteCode.equiv a).val+(FiniteCode.equiv b).val<
      linkCount (ComparisonMetadata.ofComparison p C) L*r*4 := by
    rw [linkCount_eq]
    simpa only [Nat.add_assoc] using key_lt (FiniteCode.equiv l).isLt i.isLt hbits
  simp only [squareFlags,List.getElem?_ofFn]
  split_ifs with h
  · change RectangleFlags.entry (linkLabels (ComparisonMetadata.ofComparison p C) L) r _=_
    rw [rectangle_key,linkLabels_read,linkLabels_read]
  · exact (h hi).elim

end GroupWL.LayoutMetadata
