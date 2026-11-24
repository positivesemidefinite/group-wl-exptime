import GroupWL.MachinePrograms.LayoutNodePrograms
import GroupWL.MachinePrograms.SquareSelections

/-! The complete concrete comparison-to-incidence preprocessing pipeline. -/
namespace GroupWL.MachinePrograms.LayoutIncidencePrograms
open NatArrayLanguage LayoutMetadata
set_option maxHeartbeats 3000000
set_option synthInstance.maxSize 16384
set_option maxRecDepth 8192
abbrev Reg := LayoutNodePrograms.Reg⊕SquareSelections.Reg
abbrev Arr := LayoutNodePrograms.Arr⊕SquareSelections.Arr
abbrev State := Store Reg Arr
abbrev Code := NatArrayLanguage.Program Reg Arr
abbrev nr (r : NodeLabels.Reg) : Reg := .inl (.inl (.inl (.inl (.inl r))))
abbrev lr (r : LinkLabels.Reg) : Reg := .inl (.inl (.inl (.inl (.inr r))))
abbrev qr (r : SquareIndices.Reg) : Reg := .inr (.inl (.inl r))
abbrev sr (r : SelectArray.Reg) : Reg := .inr (.inl (.inr r))
abbrev qa (a : SquareIndices.Arr) : Arr := .inr (.inl (.inl a))
abbrev sa (a : SelectArray.Arr) : Arr := .inr (.inl (.inr a))
abbrev hreg (r : FilterRanks.Reg) : Reg := .inl (.inl (.inr (.inl r)))
abbrev sreg (r : FilterRanks.Reg) : Reg := .inl (.inl (.inr (.inr (.inr r))))
abbrev harr (a : FilterRanks.Arr) : Arr := .inl (.inl (.inr (.inl a)))
abbrev varr (a : FilterRanks.Arr) : Arr := .inl (.inl (.inr (.inr (.inl a))))
abbrev nodesArr (a : LinkNodes.WorkArr) : Arr := .inl (.inr (LinkNodes.wa a))
def setup : List (Atom Reg Arr) := [
  .const (qr .one) 1,.const (qr .two) 2,.const (qr .four) 4,.const (qr .zero) 0,
  .copy (qr .width) (nr .width),
  .binary .mul (qr .cutoff) (nr .comparisons) (lr (LinkLabels.lr .length)),
  .binary .add (qr .cutoff) (qr .cutoff) (nr .comparisons),
  .binary .add (qr .total) (qr .cutoff) (nr .comparisons),
  .binary .mul (qr .total) (qr .total) (qr .width),
  .binary .mul (qr .total) (qr .total) (qr .four),
  .copy (qr .hcount) (hreg .count),
  .copyArray (qa .leftNodes) (nodesArr .leftNodes),.copyArray (qa .rightNodes) (nodesArr .rightNodes),
  .copyArray (qa .horizontalRanks) (harr .ranks),.copyArray (qa .verticalRanks) (varr .ranks),
  .copyArray (sa .flags) (.inl (.inl (.inl (.inr (.inr .output))))),
  .copy (sr .selected) (sreg .count)]
def incidence : Code := .seq (atoms setup) (SquareSelections.program.map Sum.inr Sum.inr)
def program : Code := .seq (LayoutNodePrograms.program.map Sum.inl Sum.inl) incidence

structure Input (C : ComparisonMetadata.Table) (L : ℕ) (S : State) : Prop where
  labels : LayoutLabelPrograms.Input C L S.left.left.left.left
  source : S.left.right.array (LinkNodes.wa .source)=C.source
  target : S.left.right.array (LinkNodes.wa .target)=C.target
  permutation : S.array (qa .permutation)=C.permutation

structure Valid (C : ComparisonMetadata.Table) : Prop where
  domainLength : C.domain.length=2*(C.comparisons*C.coordinates)
  domainBinary : ∀x∈C.domain,x≤1
  sourceLength : C.source.length=C.comparisons
  targetLength : C.target.length=C.comparisons
  sourceValues : ∀x∈C.source,x<C.types
  targetValues : ∀x∈C.target,x<C.types
  permutationLength : C.permutation.length=C.comparisons*C.coordinates

structure Room (C : ComparisonMetadata.Table) (L M : ℕ) : Prop where
  four : 4≤M
  steps : L+1≤M
  nodes : nodeCount C L≤M
  links : linkCount C L≤M
  horizontal : nodeCount C L*C.coordinates*4≤M
  square : linkCount C L*C.coordinates*4≤M
  ranks : horizontalCount C L+verticalCount C L≤M

structure Output (C : ComparisonMetadata.Table) (L : ℕ) (S : State) : Prop where
  metadata : LayoutNodePrograms.Output C L S.left
  endpoints : ∀which,S.right.array (.inr which)=SquareSelected.word C L which

theorem incidence_runs (C : ComparisonMetadata.Table) (L M : ℕ) (S : State)
    (bounded : S.Bounded M) (metadata : LayoutNodePrograms.Output C L S.left)
    (permutation : S.array (qa .permutation)=C.permutation)
    (valid : Valid C) (room : Room C L M) (positive : 0<L) :
    ∃t≤196*(linkCount C L*C.coordinates*4)+73,∃T,
      Runs (storageBound Reg Arr M) incidence S t T ∧ T.Bounded M ∧ Output C L T := by
  have se : S.scalar (nr .comparisons)=C.comparisons := metadata.ranks.flags.labels.comparisons
  have sw : S.scalar (nr .width)=C.coordinates := metadata.ranks.flags.labels.width
  have sl : S.scalar (lr (LinkLabels.lr .length))=L := metadata.ranks.flags.labels.length
  have sh : S.scalar (hreg .count)=horizontalCount C L := metadata.ranks.horizontalCount
  have ss : S.scalar (sreg .count)=squareCount C L := metadata.ranks.squareCount
  simp only [nr,lr,hreg,sreg] at se sw sl sh ss
  have sv : ValidAtoms M setup S := by
    simp [setup,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar,
      Store.setArray,nr,lr,qr,sr,qa,sa,hreg,sreg,harr,varr,nodesArr,se,sw,sl]
    have hl := room.links
    have hs := room.square
    unfold linkCount at hl hs
    exact ⟨by have := room.four;omega,by have := room.four;omega,room.four,
      by omega,by omega,by omega,by nlinarith,by nlinarith⟩
  obtain ⟨first,hU⟩ := atoms_runs bounded setup sv
  let U := applyAtoms setup S
  have context : SquareSelected.Input C L U.right.left := by
    refine ⟨?_,?_,?_,?_⟩
    · refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
      · simp [U,setup,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.right,Store.left,
          nr,lr,qr,sr,qa,sa,hreg,sreg,harr,varr,nodesArr,sw,SquareIndices.layoutData]
      · simp [U,setup,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.right,Store.left,
          nr,lr,qr,sr,qa,sa,hreg,sreg,harr,varr,nodesArr,se,sl,SquareIndices.layoutData,Nat.add_comm]
      · simpa [U,setup,applyAtoms,Atom.apply,Store.setScalar,Store.right,Store.left,
          nr,lr,qr,sr,qa,sa,hreg,sreg,harr,varr,nodesArr,SquareIndices.layoutData] using sh
      · rfl
      · rfl
      · rfl
      · rfl
      · exact metadata.leftNodes
      · exact metadata.rightNodes
      · exact permutation
      · exact metadata.ranks.horizontalRanks
      · exact metadata.ranks.verticalRanks
    · simp [U,setup,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.right,Store.left,
        nr,lr,qr,sr,qa,sa,hreg,sreg,harr,varr,nodesArr,se,sl,sw,linkCount,Nat.add_comm]
    · exact metadata.ranks.flags.square
    · simpa [U,setup,applyAtoms,Atom.apply,Store.setScalar,Store.right,Store.left,
        nr,lr,qr,sr,qa,sa,hreg,sreg,harr,varr,nodesArr] using ss
  have dataValid := SquareIndices.layoutData_valid C L M positive valid.sourceLength valid.targetLength
    valid.sourceValues valid.targetValues valid.permutationLength room.ranks
  obtain ⟨t,ht,V,last,hV,hinput,hout⟩ := SquareSelections.program_runs C L M U.right hU.right
    context dataValid valid.domainBinary
  exact ⟨17+t,by omega,U.left.join V,first.seq (last.right_bounded hU),hU.left.join hV,metadata,hout⟩

theorem program_runs (C : ComparisonMetadata.Table) (L M : ℕ) (S : State)
    (bounded : S.Bounded M) (input : Input C L S) (valid : Valid C) (room : Room C L M) (positive : 0<L) :
    ∃t≤130*(nodeCount C L*C.coordinates)+942*(linkCount C L*C.coordinates)+58*linkCount C L+180,∃T,
      Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧ Output C L T := by
  obtain ⟨t,ht,U,first,hU,hout⟩ := LayoutNodePrograms.program_runs C L M S.left bounded.left input.labels
    input.source input.target room.four positive room.steps room.nodes room.links room.horizontal room.square
    valid.domainLength valid.domainBinary valid.sourceLength valid.targetLength
  let V := U.join S.right
  have hV : V.Bounded M := hU.join bounded.right
  obtain ⟨s,hs,T,last,hT,output⟩ := incidence_runs C L M V hV hout input.permutation valid room positive
  exact ⟨t+s,by omega,T,(first.left_bounded bounded).seq last,hT,output⟩

end GroupWL.MachinePrograms.LayoutIncidencePrograms
