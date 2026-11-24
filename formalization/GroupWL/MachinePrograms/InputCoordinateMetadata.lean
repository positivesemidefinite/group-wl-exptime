import GroupWL.MachinePrograms.ArrayScaledOffsets
import GroupWL.MachinePrograms.CoordinateSizeBounds

/-! Complete scalar-first old-input block sizes and coordinate offsets. -/
namespace GroupWL.MachinePrograms.InputCoordinateMetadata
open NatArrayLanguage
set_option maxHeartbeats 1600000

abbrev Reg := RingDimensions.Reg ⊕ ArrayScaledOffsets.Reg
abbrev Arr := RingDimensions.Arr ⊕ ArrayScaledOffsets.Arr
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def setup : List (Atom Reg Arr) := [
  .arrayLength (.inl .total) (.inl .widths),.binary .add (.inl .total) (.inl .blocks) (.inl .total)]
def program : Code := .seq (atoms setup)
  (.seq (RingDimensions.program.map Sum.inl Sum.inl)
    (.seq (.atom (.copyArray (.inr (.inl .input)) (.inl .output)))
      (ArrayScaledOffsets.program.map Sum.inr Sum.inr)))

theorem program_runs (widths : List ℕ) (b q M : ℕ) (hq : 1≤q) (hM : b+2≤M)
    (hsize : (b+widths.length)*(b+2)*q≤M) (hv : ∀ x∈widths,x≤b)
    (S : State) (bounded : S.Bounded M) (hws : S.left.array .widths=widths)
    (hb : S.left.scalar .blocks=b) (hf : S.right.left.scalar .factor=q) :
    ∃ t≤(b+widths.length)*22+25, ∃ T,
      Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧
      T.left.array .output=RingDimensions.dimensions widths b ∧
      T.right.left.array .output=ArrayScaledOffsets.scaled (RingDimensions.dimensions widths b) q ∧
      T.right.right.scalar .count=FilterRanks.count
        (ArrayScaledOffsets.scaled (RingDimensions.dimensions widths b) q)
        (ArrayScaledOffsets.scaled (RingDimensions.dimensions widths b) q).length ∧
      T.right.right.array .ranks=List.ofFn
        (fun i : Fin (ArrayScaledOffsets.scaled (RingDimensions.dimensions widths b) q).length =>
          FilterRanks.count (ArrayScaledOffsets.scaled (RingDimensions.dimensions widths b) q) i.val) := by
  let xs := RingDimensions.dimensions widths b
  have hlen : xs.length=b+widths.length := List.length_ofFn
  have hxs : ∀ x∈xs,x≤b+2 := RingDimensions.dimensions_values widths b hv
  have hnM : b+widths.length≤M :=
    (Nat.le_mul_of_pos_right _ (by omega : 0<b+2)).trans
      ((Nat.le_mul_of_pos_right _ (by omega : 0<q)).trans hsize)
  have small : ∀ i<xs.length,xs[i]?.getD 0*q≤M := by
    intro i hi
    have hn : 1≤b+widths.length := by rw [hlen] at hi; omega
    calc
      _ ≤ (b+2)*q := Nat.mul_le_mul_right _ (RingDimensions.read_le xs (b+2) hxs i)
      _ ≤ (b+widths.length)*((b+2)*q) := by
        have h := Nat.mul_le_mul_right ((b+2)*q) hn
        simpa only [Nat.one_mul] using h
      _ ≤ M := by simpa only [Nat.mul_assoc] using hsize
  have scaledValues : ∀ x∈ArrayScaledOffsets.scaled xs q,x≤(b+2)*q := by
    intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact Nat.mul_le_mul_right _ (RingDimensions.read_le xs (b+2) hxs i.val)
  have total : FilterRanks.count (ArrayScaledOffsets.scaled xs q) (ArrayScaledOffsets.scaled xs q).length≤M := by
    have h := count_le_mul _ ((b+2)*q) scaledValues (ArrayScaledOffsets.scaled xs q).length
    have hslen : (ArrayScaledOffsets.scaled xs q).length=b+widths.length := (List.length_ofFn).trans hlen
    rw [hslen] at h
    rw [hslen]
    exact h.trans (by simpa only [Nat.mul_assoc] using hsize)
  change S.array (.inl .widths)=widths at hws
  change S.scalar (.inl .blocks)=b at hb
  have valid : ValidAtoms M setup S := by
    simp [setup,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar,hws,hb,hnM]
  obtain ⟨first,hUB⟩ := atoms_runs bounded setup valid
  let U := applyAtoms setup S
  have ready : RingDimensions.Ready widths b U.left := by
    simp [RingDimensions.Ready,U,setup,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.left,hws,hb]
  obtain ⟨t,ht,V,ring,hVB,hVR,hVout⟩ := RingDimensions.program_runs widths b M hM hv U.left ready hUB.left
  have ringRun := ring.left_bounded hUB
  let W := V.join U.right
  have hWB : W.Bounded M := hVB.join hUB.right
  let X := (Atom.copyArray (.inr (.inl ArrayScale.Arr.input)) (.inl RingDimensions.Arr.output) : Atom Reg Arr).apply W
  have hXB := Atom.apply_bounded hWB (Atom.copyArray (.inr (.inl ArrayScale.Arr.input)) (.inl RingDimensions.Arr.output)) trivial
  have copy := atom_runs hWB (Atom.copyArray (.inr (.inl ArrayScale.Arr.input)) (.inl RingDimensions.Arr.output)) trivial trivial
  have hx : X.right.left.array .input=xs := hVout
  have hq' : X.right.left.scalar .factor=q := hf
  obtain ⟨u,hu,Y,offsets,hYB,hYi,hYo,hYtotal,hYoffsets⟩ :=
    ArrayScaledOffsets.program_runs xs q M (by omega) small total X.right hXB.right hx hq'
  have offsetsRun := offsets.right_bounded hXB
  rw [hlen] at hu
  exact ⟨2+(t+(1+u)),by omega,X.left.join Y,first.seq (ringRun.seq (copy.seq offsetsRun)),
    hXB.left.join hYB,hVout,hYo,hYtotal,hYoffsets⟩

end GroupWL.MachinePrograms.InputCoordinateMetadata
