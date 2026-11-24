import GroupWL.MachinePrograms.LayoutRankPrograms
import GroupWL.MachinePrograms.LinkNodes

/-! Source labels, ranks, and both endpoint-node tables in one program. -/
namespace GroupWL.MachinePrograms.LayoutNodePrograms
open NatArrayLanguage LayoutMetadata
set_option maxHeartbeats 2500000
set_option synthInstance.maxSize 8192
set_option maxRecDepth 4096
abbrev Reg := LayoutRankPrograms.Reg⊕LinkNodes.Reg
abbrev Arr := LayoutRankPrograms.Arr⊕LinkNodes.Arr
abbrev State := Store Reg Arr
abbrev Code := NatArrayLanguage.Program Reg Arr
abbrev nr (r : NodeLabels.Reg) : Reg := .inl (.inl (.inl (.inl r)))
abbrev lr (r : LinkLabels.Reg) : Reg := .inl (.inl (.inl (.inr r)))
def setup : List (Atom Reg Arr) := [
  .copy (.inr (LinkNodes.lr .comparisons)) (nr .comparisons),
  .copy (.inr (LinkNodes.lr .length)) (lr (LinkLabels.lr .length)),
  .copy (.inr (LinkNodes.wr .types)) (nr .types)]
def nodes : Code := .seq (atoms setup)
  ((NatArrayLanguage.Program.seq (LinkNodes.program false) (LinkNodes.program true)).map Sum.inr Sum.inr)
def program : Code := .seq (LayoutRankPrograms.program.map Sum.inl Sum.inl) nodes

structure Output (C : ComparisonMetadata.Table) (L : ℕ) (S : State) : Prop where
  ranks : LayoutRankPrograms.Output C L S.left
  leftNodes : S.right.array (LinkNodes.wa .leftNodes)=List.ofFn (fun i : Fin (linkCount C L) => leftNode C L i)
  rightNodes : S.right.array (LinkNodes.wa .rightNodes)=List.ofFn (fun i : Fin (linkCount C L) => rightNode C L i)

theorem nodes_runs (C : ComparisonMetadata.Table) (L M : ℕ) (S : State)
    (bounded : S.Bounded M) (input : LayoutRankPrograms.Output C L S.left)
    (source : S.right.array (LinkNodes.wa .source)=C.source)
    (target : S.right.array (LinkNodes.wa .target)=C.target)
    (room : 2≤M) (positive : 0<L) (nodesBound : nodeCount C L≤M) (links : linkCount C L≤M)
    (sourceLength : C.source.length=C.comparisons) (targetLength : C.target.length=C.comparisons) :
    ∃t≤58*linkCount C L+21,∃T,Runs (storageBound Reg Arr M) nodes S t T ∧
      T.Bounded M ∧ Output C L T := by
  obtain ⟨first,hU⟩ := atoms_runs bounded setup (by simp [setup,ValidAtoms,Atom.Valid,Atom.SmallResult])
  let U := applyAtoms setup S
  have ue : U.right.scalar (LinkNodes.lr .comparisons)=C.comparisons := by
    simpa [U,setup,applyAtoms,Atom.apply,Store.setScalar,Store.right,nr,lr,Store.left] using input.flags.labels.comparisons
  have ul : U.right.scalar (LinkNodes.lr .length)=L := by
    simpa [U,setup,applyAtoms,Atom.apply,Store.setScalar,Store.right,nr,lr,Store.left] using input.flags.labels.length
  have ut : U.right.scalar (LinkNodes.wr .types)=C.types := by
    simpa [U,setup,applyAtoms,Atom.apply,Store.setScalar,Store.right,nr,lr,Store.left] using input.flags.labels.types
  have us : U.right.array (LinkNodes.wa .source)=C.source := source
  have ud : U.right.array (LinkNodes.wa .target)=C.target := target
  obtain ⟨t,ht,V,run,hV,hleft⟩ := LinkNodes.program_runs false U.right M hU.right room
    (by rwa [ul]) (by simpa [ue,ul,linkCount] using links)
    (by simpa [ut,ue,ul,nodeCount] using nodesBound)
    (by rw [us,ue];exact sourceLength) (by rw [ud,ue];exact targetLength)
  have ve := (run.scalar_eq_of_not_mem (LinkNodes.lr .comparisons) (by decide)).trans ue
  have vl := (run.scalar_eq_of_not_mem (LinkNodes.lr .length) (by decide)).trans ul
  have vt := (run.scalar_eq_of_not_mem (LinkNodes.wr .types) (by decide)).trans ut
  have vs := (run.array_eq_of_not_mem (LinkNodes.wa .source) (by decide)).trans us
  have vd := (run.array_eq_of_not_mem (LinkNodes.wa .target) (by decide)).trans ud
  obtain ⟨s,hs,W,last,hW,hright⟩ := LinkNodes.program_runs true V M hV room
    (by rwa [vl]) (by simpa [ve,vl,linkCount] using links)
    (by simpa [vt,ve,vl,nodeCount] using nodesBound)
    (by rw [vs,ve];exact sourceLength) (by rw [vd,ve];exact targetLength)
  refine ⟨3+(t+s),?_,U.left.join W,first.seq ((run.seq last).right_bounded hU),
    hU.left.join hW,input,?_,?_⟩
  · rw [ue,ul] at ht;rw [ve,vl] at hs;unfold linkCount;omega
  · change W.array (LinkNodes.wa .leftNodes)=_
    rw [last.array_eq_of_not_mem (LinkNodes.wa .leftNodes) (by decide)]
    simpa [LinkNodes.outputArray,LinkNodes.value,LinkNodes.leftNode,leftNode,us,ud,ut,ue,ul,linkCount] using hleft
  · simpa [LinkNodes.outputArray,LinkNodes.value,LinkNodes.rightNode,rightNode,vs,vd,vt,ve,vl,linkCount] using hright

theorem program_runs (C : ComparisonMetadata.Table) (L M : ℕ) (S : State)
    (bounded : S.Bounded M) (input : LayoutLabelPrograms.Input C L S.left.left.left)
    (source : S.right.array (LinkNodes.wa .source)=C.source)
    (target : S.right.array (LinkNodes.wa .target)=C.target)
    (room : 4≤M) (positive : 0<L) (steps : L+1≤M)
    (nodesBound : nodeCount C L≤M) (links : linkCount C L≤M)
    (nsize : nodeCount C L*C.coordinates*4≤M) (lsize : linkCount C L*C.coordinates*4≤M)
    (domainLength : C.domain.length=2*(C.comparisons*C.coordinates)) (binary : ∀x∈C.domain,x≤1)
    (sourceLength : C.source.length=C.comparisons) (targetLength : C.target.length=C.comparisons) :
    ∃t≤130*(nodeCount C L*C.coordinates)+158*(linkCount C L*C.coordinates)+58*linkCount C L+107,∃T,
      Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧ Output C L T := by
  obtain ⟨t,ht,U,first,hU,hout⟩ := LayoutRankPrograms.program_runs C L M S.left bounded.left input
    room positive steps nodesBound links nsize lsize domainLength binary
  let V := U.join S.right
  have hV : V.Bounded M := hU.join bounded.right
  obtain ⟨s,hs,T,last,hT,output⟩ := nodes_runs C L M V hV hout source target (by omega) positive
    nodesBound links sourceLength targetLength
  exact ⟨t+s,by omega,T,(first.left_bounded bounded).seq last,hT,output⟩

end GroupWL.MachinePrograms.LayoutNodePrograms
