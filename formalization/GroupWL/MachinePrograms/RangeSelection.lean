import GroupWL.MachinePrograms.SourceNeighbors

/-! Select the indices of all nonzero entries of one runtime array. -/
namespace GroupWL.MachinePrograms.RangeSelection
open NatArrayLanguage SourceNeighbors
def setup : List (Atom Reg Arr) := [.arrayLength .length .input,.const .stride 1,.const .offset 0]
def program : Code := .seq (atoms setup) SourceNeighbors.program
def selected (xs : List ℕ) := SourceNeighbors.selected xs 1 0 xs.length

theorem program_runs (xs : List ℕ) (M : ℕ) (hM : 1≤M)
    (S : State) (bounded : S.Bounded M) (hinput : S.array .input=xs) :
    ∃ t≤xs.length*9+10, ∃ T, Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧
      T.array .input=xs ∧ T.scalar .count=(selected xs).length ∧
      (T.array .output).length=xs.length ∧ (T.array .output).take (T.scalar .count)=selected xs := by
  have valid : ValidAtoms M setup S := by simp [setup,ValidAtoms,Atom.Valid,Atom.SmallResult,hM]
  obtain ⟨first,hUB⟩ := atoms_runs bounded setup valid
  let U := applyAtoms setup S
  have hi : U.array .input=xs := hinput
  have hn : U.scalar .length=xs.length := by simp [U,setup,applyAtoms,Atom.apply,Store.setScalar,hinput]
  have hs : U.scalar .stride=1 := by simp [U,setup,applyAtoms,Atom.apply,Store.setScalar]
  have ho : U.scalar .offset=0 := by simp [U,setup,applyAtoms,Atom.apply,Store.setScalar]
  obtain ⟨t,ht,T,run,hTB,hTi,hTc,hTl,hTo⟩ := SourceNeighbors.program_runs U xs xs.length 1 0 M
    hUB hM hi hn hs ho (by intro i hi; simpa using hi)
  exact ⟨3+t,by omega,T,first.seq run,hTB,hTi,hTc,hTl,hTo⟩

end GroupWL.MachinePrograms.RangeSelection
