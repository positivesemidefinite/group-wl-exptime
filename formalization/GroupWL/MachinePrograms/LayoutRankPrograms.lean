import GroupWL.MachinePrograms.LayoutFlagPrograms
import GroupWL.MachinePrograms.FilterRanks

/-! One bounded program computing all label flags and all three rank arrays. -/
namespace GroupWL.MachinePrograms.LayoutRankPrograms
open NatArrayLanguage LayoutMetadata
set_option maxHeartbeats 2000000
abbrev RankReg := FilterRanks.Reg⊕(FilterRanks.Reg⊕FilterRanks.Reg)
abbrev RankArr := FilterRanks.Arr⊕(FilterRanks.Arr⊕FilterRanks.Arr)
abbrev Reg := LayoutFlagPrograms.Reg⊕RankReg
abbrev Arr := LayoutFlagPrograms.Arr⊕RankArr
abbrev State := Store Reg Arr
abbrev Code := NatArrayLanguage.Program Reg Arr
def triple : NatArrayLanguage.Program RankReg RankArr :=
  .seq (FilterRanks.program.map Sum.inl Sum.inl)
    ((NatArrayLanguage.Program.seq (FilterRanks.program.map Sum.inl Sum.inl)
      (FilterRanks.program.map Sum.inr Sum.inr)).map Sum.inr Sum.inr)
def setup : List (Atom Reg Arr) := [
  .copyArray (.inr (.inl .flags)) (.inl (.inr (.inl .output))),
  .copyArray (.inr (.inr (.inl .flags))) (.inl (.inl (.inr (LinkLabels.wa .output)))),
  .copyArray (.inr (.inr (.inr .flags))) (.inl (.inr (.inr .output)))]
def ranks : Code := .seq (atoms setup) (triple.map Sum.inr Sum.inr)
def program : Code := .seq (LayoutFlagPrograms.program.map Sum.inl Sum.inl) ranks
def rankWord (xs : List ℕ) := List.ofFn (fun i : Fin xs.length => FilterRanks.count xs i)

structure Output (C : ComparisonMetadata.Table) (L : ℕ) (S : State) : Prop where
  flags : LayoutFlagPrograms.Output C L S.left
  horizontalRanks : S.right.left.array .ranks=rankWord (horizontalFlags C L)
  verticalRanks : S.right.right.left.array .ranks=rankWord (linkLabels C L)
  squareRanks : S.right.right.right.array .ranks=rankWord (squareFlags C L)
  horizontalCount : S.right.left.scalar .count=LayoutMetadata.horizontalCount C L
  verticalCount : S.right.right.left.scalar .count=LayoutMetadata.verticalCount C L
  squareCount : S.right.right.right.scalar .count=LayoutMetadata.squareCount C L

theorem ranks_runs (C : ComparisonMetadata.Table) (L M : ℕ) (S : State)
    (bounded : S.Bounded M) (input : LayoutFlagPrograms.Output C L S.left)
    (room : 1≤M) (binary : ∀x∈C.domain,x≤1) :
    ∃t≤6*(horizontalFlags C L).length+6*(linkLabels C L).length+6*(squareFlags C L).length+27,∃T,
      Runs (storageBound Reg Arr M) ranks S t T ∧ T.Bounded M ∧ Output C L T := by
  obtain ⟨first,hU⟩ := atoms_runs bounded setup (by simp [setup,ValidAtoms,Atom.Valid,Atom.SmallResult])
  let U := applyAtoms setup S
  have uh : U.right.left.array .flags=horizontalFlags C L := input.horizontal
  have uv : U.right.right.left.array .flags=linkLabels C L := input.labels.linkLabels
  have us : U.right.right.right.array .flags=squareFlags C L := input.square
  obtain ⟨t,ht,V,run,hV,hcount,hword⟩ := FilterRanks.program_runs U.right.left M hU.right.left room
    (by rw [uh];exact LayoutFlagPrograms.horizontal_binary C L binary)
  let A := V.join U.right.right
  have hA : A.Bounded M := hV.join hU.right.right
  obtain ⟨s,hs,W,middle,hW,vcount,vword⟩ := FilterRanks.program_runs A.right.left M hA.right.left room
    (by change ∀x∈U.right.right.left.array .flags,x≤1;rw [uv];exact LayoutFlagPrograms.link_binary C L binary)
  let B := W.join A.right.right
  have hB : B.Bounded M := hW.join hA.right.right
  obtain ⟨u,hu,X,last,hX,scount,sword⟩ := FilterRanks.program_runs B.right M hB.right room
    (by change ∀x∈U.right.right.right.array .flags,x≤1;rw [us];exact LayoutFlagPrograms.square_binary C L binary)
  have two := (middle.left_bounded hA.right).seq (last.right_bounded hB)
  have three := (run.left_bounded hU.right).seq (two.right_bounded hA)
  refine ⟨3+(t+(s+u)),?_,U.left.join (A.left.join (B.left.join X)),
    first.seq (three.right_bounded hU),hU.left.join (hA.left.join (hB.left.join hX)),
    input,?_,?_,?_,?_,?_,?_⟩
  · rw [uh] at ht
    change s≤6*(U.right.right.left.array .flags).length+8 at hs
    change u≤6*(U.right.right.right.array .flags).length+8 at hu
    rw [uv] at hs;rw [us] at hu;omega
  · simpa only [rankWord,uh] using hword
  · simpa only [rankWord,A,Store.right_join,uv] using vword
  · simpa only [rankWord,B,A,Store.right_join,us] using sword
  · simpa only [horizontalCount,uh] using hcount
  · simpa only [verticalCount,A,Store.right_join,uv] using vcount
  · simpa only [squareCount,B,A,Store.right_join,us] using scount

theorem program_runs (C : ComparisonMetadata.Table) (L M : ℕ) (S : State)
    (bounded : S.Bounded M) (input : LayoutLabelPrograms.Input C L S.left.left)
    (room : 4≤M) (positive : 0<L) (steps : L+1≤M)
    (nodes : nodeCount C L≤M) (links : linkCount C L≤M)
    (nsize : nodeCount C L*C.coordinates*4≤M) (lsize : linkCount C L*C.coordinates*4≤M)
    (domainLength : C.domain.length=2*(C.comparisons*C.coordinates)) (binary : ∀x∈C.domain,x≤1) :
    ∃t≤130*(nodeCount C L*C.coordinates)+158*(linkCount C L*C.coordinates)+86,∃T,
      Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧ Output C L T := by
  obtain ⟨t,ht,U,first,hU,hout⟩ := LayoutFlagPrograms.program_runs C L M S.left bounded.left input
    room positive steps nodes links nsize lsize domainLength binary
  let V := U.join S.right
  have hV : V.Bounded M := hU.join bounded.right
  obtain ⟨s,hs,T,last,hT,output⟩ := ranks_runs C L M V hV hout (by omega) binary
  simp only [horizontalFlags,linkLabels,squareFlags,List.length_ofFn] at hs
  exact ⟨t+s,by omega,T,(first.left_bounded bounded).seq last,hT,output⟩

end GroupWL.MachinePrograms.LayoutRankPrograms
