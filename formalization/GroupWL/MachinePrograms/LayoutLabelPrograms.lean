import GroupWL.MachinePrograms.NodeLabels
import GroupWL.MachinePrograms.LinkLabels
import GroupWL.MachinePrograms.NatArrayComponents
import GroupWL.LayoutMetadata

/-! One executable stage materializing both source-layout label arrays. -/
namespace GroupWL.MachinePrograms.LayoutLabelPrograms
open NatArrayLanguage LayoutMetadata
set_option maxHeartbeats 2000000
abbrev Reg := NodeLabels.Reg⊕LinkLabels.Reg
abbrev Arr := NodeLabels.Arr⊕LinkLabels.Arr
abbrev State := Store Reg Arr
abbrev Code := NatArrayLanguage.Program Reg Arr

structure Input (C : ComparisonMetadata.Table) (L : ℕ) (S : State) : Prop where
  types : S.left.scalar .types=C.types
  comparisons : S.left.scalar .comparisons=C.comparisons
  width : S.left.scalar .width=C.coordinates
  length : S.right.scalar (LinkLabels.lr .length)=L
  domain : S.left.array .domain=C.domain

def setup : List (Atom Reg Arr) := [
  .const (.inl .one) 1,.binary .add (.inl .wireSteps) (.inr (LinkLabels.lr .length)) (.inl .one),
  .copy (.inr (LinkLabels.lr .comparisons)) (.inl .comparisons),
  .copy (.inr (LinkLabels.wr .width)) (.inl .width),
  .copyArray (.inr (LinkLabels.wa .domain)) (.inl .domain)]
def program : Code := .seq (atoms setup)
  (.seq (NodeLabels.program.map Sum.inl Sum.inl) (LinkLabels.program.map Sum.inr Sum.inr))

structure Output (C : ComparisonMetadata.Table) (L : ℕ) (S : State) : Prop extends Input C L S where
  nodeLabels : S.left.array .output=LayoutMetadata.nodeLabels C L
  linkLabels : S.right.array (LinkLabels.wa .output)=LayoutMetadata.linkLabels C L

theorem program_runs (C : ComparisonMetadata.Table) (L M : ℕ) (S : State)
    (bounded : S.Bounded M) (input : Input C L S) (room : 2≤M) (positive : 0<L)
    (steps : L+1≤M) (nodes : nodeCount C L≤M) (links : linkCount C L≤M)
    (nsize : nodeCount C L*C.coordinates*2≤M) (lsize : linkCount C L*C.coordinates*2≤M)
    (domainLength : C.domain.length=2*(C.comparisons*C.coordinates)) :
    ∃t≤15*(nodeCount C L*C.coordinates*2)+23*(linkCount C L*C.coordinates*2)+28,∃T,
      Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧ Output C L T := by
  have hL : S.scalar (.inr (LinkLabels.lr .length))=L := input.length
  have sv : ValidAtoms M setup S := by
    simp [setup,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar,
      hL]
    exact ⟨by omega,steps⟩
  obtain ⟨first,hU⟩ := atoms_runs bounded setup sv
  let U := applyAtoms setup S
  have ut : U.left.scalar .types=C.types := input.types
  have ue : U.left.scalar .comparisons=C.comparisons := input.comparisons
  have uw : U.left.scalar .width=C.coordinates := input.width
  have us : U.left.scalar .wireSteps=L+1 := by
    simp [U,setup,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.left,hL]
  have ud : U.left.array .domain=C.domain := input.domain
  have uL : U.right.scalar (LinkLabels.lr .length)=L := input.length
  have uE : U.right.scalar (LinkLabels.lr .comparisons)=C.comparisons := by
    simpa [U,setup,applyAtoms,Atom.apply,Store.setScalar,Store.right,Store.left] using input.comparisons
  have uW : U.right.scalar (LinkLabels.wr .width)=C.coordinates := by
    simpa [U,setup,applyAtoms,Atom.apply,Store.setScalar,Store.right,Store.left] using input.width
  have uD : U.right.array (LinkLabels.wa .domain)=C.domain := by
    simpa [U,setup,applyAtoms,Atom.apply,Store.setArray,Store.right,Store.left] using input.domain
  obtain ⟨t,ht,V,nodeRun,hV,hnode⟩ := NodeLabels.program_runs U.left M hU.left room
    (by rw [us];omega) (by simpa [ut,ue,us,nodeCount] using nodes)
    (by simpa [ut,ue,us,uw,nodeCount] using nsize) (by rw [ud,ue,uw];exact domainLength)
  let W := V.join U.right
  have hW : W.Bounded M := hV.join hU.right
  obtain ⟨s,hs,X,linkRun,hX,hlink⟩ := LinkLabels.program_runs W.right M hW.right room
    (by simpa [W,uL] using positive) (by simpa [W,uE,uL,linkCount] using links)
    (by simpa [W,uE,uL,uW,linkCount] using lsize)
    (by simpa [W,uD,uE,uW] using domainLength)
  refine ⟨5+(t+s),?_,W.left.join X,first.seq ((nodeRun.left_bounded hU).seq
    (linkRun.right_bounded hW)),hW.left.join hX,?_,?_,?_⟩
  · simp only [ut,ue,us,uw] at ht
    change s≤23*((U.right.scalar (LinkLabels.lr .comparisons)+U.right.scalar (LinkLabels.lr .comparisons)*
      U.right.scalar (LinkLabels.lr .length)+U.right.scalar (LinkLabels.lr .comparisons))*U.right.scalar (LinkLabels.wr .width)*2)+12 at hs
    rw [uE,uL,uW] at hs
    unfold nodeCount linkCount
    omega
  · refine ⟨?_,?_,?_,?_,?_⟩
    · exact (nodeRun.scalar_eq_of_not_mem .types (by decide)).trans ut
    · exact (nodeRun.scalar_eq_of_not_mem .comparisons (by decide)).trans ue
    · exact (nodeRun.scalar_eq_of_not_mem .width (by decide)).trans uw
    · exact (linkRun.scalar_eq_of_not_mem (LinkLabels.lr .length) (by decide)).trans uL
    · exact (nodeRun.array_eq_of_not_mem .domain (by decide)).trans ud
  · simpa [nodeLabels,nodeLabel,NodeLabels.entry,ut,ue,us,uw,ud,nodeCount] using hnode
  · simpa [linkLabels,linkLabel,LinkLabels.entry,LinkIndex.comparison,linkComparison,W,uE,uL,uW,uD,linkCount] using hlink

end GroupWL.MachinePrograms.LayoutLabelPrograms
