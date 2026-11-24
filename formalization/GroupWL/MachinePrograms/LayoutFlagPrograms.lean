import GroupWL.MachinePrograms.LayoutLabelPrograms
import GroupWL.MachinePrograms.RectangleFlags

/-! The complete label and square-candidate flag preprocessing stage. -/
namespace GroupWL.MachinePrograms.LayoutFlagPrograms
open NatArrayLanguage LayoutMetadata
set_option maxHeartbeats 2000000
abbrev Reg := LayoutLabelPrograms.Reg⊕(RectangleFlags.Reg⊕RectangleFlags.Reg)
abbrev Arr := LayoutLabelPrograms.Arr⊕(RectangleFlags.Arr⊕RectangleFlags.Arr)
abbrev State := Store Reg Arr
abbrev Code := NatArrayLanguage.Program Reg Arr
abbrev nr (r : NodeLabels.Reg) : Reg := .inl (.inl r)
abbrev lr (r : LinkLabels.Reg) : Reg := .inl (.inr r)
abbrev hr (r : RectangleFlags.Reg) : Reg := .inr (.inl r)
abbrev sr (r : RectangleFlags.Reg) : Reg := .inr (.inr r)

def setup : List (Atom Reg Arr) := [
  .const (hr .one) 1,.binary .add (hr .base) (lr (LinkLabels.lr .length)) (hr .one),
  .binary .mul (hr .rows) (nr .comparisons) (hr .base),
  .binary .add (hr .rows) (hr .rows) (nr .types),.copy (hr .width) (nr .width),
  .copyArray (.inr (.inl .labels)) (.inl (.inl .output)),
  .binary .mul (sr .rows) (nr .comparisons) (lr (LinkLabels.lr .length)),
  .binary .add (sr .rows) (sr .rows) (nr .comparisons),
  .binary .add (sr .rows) (sr .rows) (nr .comparisons),.copy (sr .width) (nr .width),
  .copyArray (.inr (.inr .labels)) (.inl (.inr (LinkLabels.wa .output)))]
def flags : Code := .seq (atoms setup)
  ((NatArrayLanguage.Program.seq (RectangleFlags.program.map Sum.inl Sum.inl)
    (RectangleFlags.program.map Sum.inr Sum.inr)).map Sum.inr Sum.inr)
def program : Code := .seq (LayoutLabelPrograms.program.map Sum.inl Sum.inl) flags

structure Output (C : ComparisonMetadata.Table) (L : ℕ) (S : State) : Prop where
  labels : LayoutLabelPrograms.Output C L S.left
  horizontal : S.right.left.array .output=horizontalFlags C L
  square : S.right.right.array .output=squareFlags C L

theorem node_binary (C : ComparisonMetadata.Table) (L : ℕ) (binary : ∀x∈C.domain,x≤1) :
    ∀x∈nodeLabels C L,x≤1 := by
  intro x hx
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  dsimp only [nodeLabel]
  split_ifs
  · omega
  · exact RectangleFlags.read_small binary _
theorem link_binary (C : ComparisonMetadata.Table) (L : ℕ) (binary : ∀x∈C.domain,x≤1) :
    ∀x∈linkLabels C L,x≤1 := by
  intro x hx
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  exact RectangleFlags.read_small binary _
theorem horizontal_binary (C : ComparisonMetadata.Table) (L : ℕ) (binary : ∀x∈C.domain,x≤1) :
    ∀x∈horizontalFlags C L,x≤1 := by
  intro x hx
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  exact RectangleFlags.entry_small (node_binary C L binary) _ _
theorem square_binary (C : ComparisonMetadata.Table) (L : ℕ) (binary : ∀x∈C.domain,x≤1) :
    ∀x∈squareFlags C L,x≤1 := by
  intro x hx
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  exact RectangleFlags.entry_small (link_binary C L binary) _ _

theorem flags_runs (C : ComparisonMetadata.Table) (L M : ℕ) (S : State)
    (bounded : S.Bounded M) (input : LayoutLabelPrograms.Output C L S.left)
    (room : 4≤M) (steps : L+1≤M) (nodes : nodeCount C L≤M) (links : linkCount C L≤M)
    (nsize : nodeCount C L*C.coordinates*4≤M) (lsize : linkCount C L*C.coordinates*4≤M)
    (binary : ∀x∈C.domain,x≤1) :
    ∃t≤19*(nodeCount C L*C.coordinates*4)+19*(linkCount C L*C.coordinates*4)+31,∃T,
      Runs (storageBound Reg Arr M) flags S t T ∧ T.Bounded M ∧ Output C L T := by
  have st : S.scalar (nr .types)=C.types := input.types
  have se : S.scalar (nr .comparisons)=C.comparisons := input.comparisons
  have sw : S.scalar (nr .width)=C.coordinates := input.width
  have sl : S.scalar (lr (LinkLabels.lr .length))=L := input.length
  simp only [nr,lr] at st se sw sl
  have sv : ValidAtoms M setup S := by
    simp [setup,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar,
      st,se,sw,sl,nr,lr,hr,sr]
    unfold nodeCount at nodes
    unfold linkCount at links
    exact ⟨by omega,steps,by omega,by omega,by omega,by omega,by omega⟩
  obtain ⟨first,hU⟩ := atoms_runs bounded setup sv
  let U := applyAtoms setup S
  have ur : U.right.left.scalar .rows=nodeCount C L := by
    simp [U,setup,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.left,Store.right,
      nr,lr,hr,sr,st,se,sw,sl,nodeCount,linkCount,Nat.add_comm]
  have uw : U.right.left.scalar .width=C.coordinates := by
    simpa [U,setup,applyAtoms,Atom.apply,Store.setScalar,Store.left,Store.right,nr,lr,hr,sr] using sw
  have ul : U.right.left.array .labels=nodeLabels C L := input.nodeLabels
  have vr : U.right.right.scalar .rows=linkCount C L := by
    simp [U,setup,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.left,Store.right,
      nr,lr,hr,sr,st,se,sw,sl,nodeCount,linkCount,Nat.add_comm]
  have vw : U.right.right.scalar .width=C.coordinates := by
    simpa [U,setup,applyAtoms,Atom.apply,Store.setScalar,Store.left,Store.right,nr,lr,hr,sr] using sw
  have vl : U.right.right.array .labels=linkLabels C L := input.linkLabels
  obtain ⟨t,ht,V,run,hV,hout⟩ := RectangleFlags.program_runs U.right.left M hU.right.left room
    (by rwa [ur,uw]) (by rw [ul,ur,uw];simp [nodeLabels,Nat.mul_comm])
    (by rw [ul];exact node_binary C L binary)
  let W := V.join U.right.right
  have hW : W.Bounded M := hV.join hU.right.right
  obtain ⟨s,hs,X,last,hX,hout'⟩ := RectangleFlags.program_runs W.right M hW.right room
    (by simpa [W,vr,vw] using lsize)
    (by simp [W,vl,vr,vw,linkLabels,Nat.mul_comm])
    (by change ∀x∈U.right.right.array .labels,x≤1;rw [vl];exact link_binary C L binary)
  have combined := (run.left_bounded hU.right).seq (last.right_bounded hW)
  refine ⟨11+(t+s),?_,U.left.join (W.left.join X),first.seq (combined.right_bounded hU),
    hU.left.join (hW.left.join hX),?_,?_,?_⟩
  · rw [ur,uw] at ht
    change s≤19*(U.right.right.scalar .rows*U.right.right.scalar .width*4)+10 at hs
    rw [vr,vw] at hs
    omega
  · exact input
  · simpa [horizontalFlags,ul,ur,uw] using hout
  · simpa [squareFlags,W,vl,vr,vw] using hout'

theorem program_runs (C : ComparisonMetadata.Table) (L M : ℕ) (S : State)
    (bounded : S.Bounded M) (input : LayoutLabelPrograms.Input C L S.left)
    (room : 4≤M) (positive : 0<L) (steps : L+1≤M)
    (nodes : nodeCount C L≤M) (links : linkCount C L≤M)
    (nsize : nodeCount C L*C.coordinates*4≤M) (lsize : linkCount C L*C.coordinates*4≤M)
    (domainLength : C.domain.length=2*(C.comparisons*C.coordinates))
    (binary : ∀x∈C.domain,x≤1) :
    ∃t≤106*(nodeCount C L*C.coordinates)+122*(linkCount C L*C.coordinates)+59,∃T,
      Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧ Output C L T := by
  obtain ⟨t,ht,U,first,hU,hout⟩ := LayoutLabelPrograms.program_runs C L M S.left bounded.left input
    (by omega) positive steps nodes links (by omega) (by omega) domainLength
  let V := U.join S.right
  have hV : V.Bounded M := hU.join bounded.right
  obtain ⟨s,hs,T,last,hT,output⟩ := flags_runs C L M V hV hout room steps nodes links nsize lsize binary
  exact ⟨t+s,by omega,T,(first.left_bounded bounded).seq last,hT,output⟩

end GroupWL.MachinePrograms.LayoutFlagPrograms
