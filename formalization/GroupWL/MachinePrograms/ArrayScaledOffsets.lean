import GroupWL.MachinePrograms.ArrayScale
import GroupWL.MachinePrograms.PrefixSums
import GroupWL.MachinePrograms.NatArrayComponents

/-! Runtime block sizes and their starting offsets. -/
namespace GroupWL.MachinePrograms.ArrayScaledOffsets
open NatArrayLanguage

abbrev Reg := ArrayScale.Reg ⊕ FilterRanks.Reg
abbrev Arr := ArrayScale.Arr ⊕ FilterRanks.Arr
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def scaled (xs : List ℕ) (factor : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin xs.length => xs[i.val]?.getD 0*factor)

def program : Code := .seq (ArrayScale.program.map Sum.inl Sum.inl)
  (.seq (.atom (.copyArray (.inr .flags) (.inl .output))) (FilterRanks.program.map Sum.inr Sum.inr))

theorem program_runs (xs : List ℕ) (factor M : ℕ) (hM : 1≤M)
    (small : ∀ i<xs.length,xs[i]?.getD 0*factor≤M)
    (total : FilterRanks.count (scaled xs factor) (scaled xs factor).length≤M)
    (S : State) (bounded : S.Bounded M) (hx : S.left.array .input=xs) (hf : S.left.scalar .factor=factor) :
    ∃ t≤xs.length*12+16, ∃ T, Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧
      T.left.array .input=xs ∧ T.left.array .output=scaled xs factor ∧
      T.right.scalar .count=FilterRanks.count (scaled xs factor) (scaled xs factor).length ∧
      T.right.array .ranks=List.ofFn (fun i : Fin (scaled xs factor).length => FilterRanks.count (scaled xs factor) i.val) := by
  obtain ⟨t,ht,U,scale,hUB,hUR,hUout⟩ := ArrayScale.program_runs xs factor M hM small S.left bounded.left hx hf
  have first := scale.left_bounded bounded
  let V := U.join S.right
  have hVB : V.Bounded M := hUB.join bounded.right
  let W := (Atom.copyArray (.inr FilterRanks.Arr.flags) (.inl ArrayScale.Arr.output) : Atom Reg Arr).apply V
  have hWB := Atom.apply_bounded hVB (Atom.copyArray (.inr FilterRanks.Arr.flags) (.inl ArrayScale.Arr.output)) trivial
  have copy := atom_runs hVB (Atom.copyArray (.inr FilterRanks.Arr.flags) (.inl ArrayScale.Arr.output)) trivial trivial
  have hw : W.right.array .flags=scaled xs factor := hUout
  obtain ⟨u,hu,X,prefixRun,hXB,hcount,hoffsets⟩ := FilterRanks.program_runs_total W.right M hWB.right hM (by simpa only [hw] using total)
  have last := prefixRun.right_bounded hWB
  rw [hw] at hu hcount hoffsets
  have hwlen : (scaled xs factor).length=xs.length := List.length_ofFn
  rw [hwlen] at hu
  exact ⟨t+(1+u),by omega,W.left.join X,first.seq (copy.seq last),hWB.left.join hXB,
    hUR.1,hUout,hcount,hoffsets⟩

end GroupWL.MachinePrograms.ArrayScaledOffsets
