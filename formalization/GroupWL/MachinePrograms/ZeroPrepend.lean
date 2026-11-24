import GroupWL.MachinePrograms.NatArrayConcat

namespace GroupWL.MachinePrograms.ZeroPrepend
open NatArrayLanguage
abbrev Reg := NatArrayConcat.Reg
abbrev Arr := NatArrayConcat.Arr
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def setup : List (Atom Reg Arr) := [.const 9 0,.allocate 0 0 9]
def program : Code := .seq (atoms setup) NatArrayConcat.concat

theorem program_runs (S : State) (M : ℕ) (bounded : S.Bounded M) (room : 1≤M)
    (size : S.scalar 0+(S.array 1).length≤M) :
    ∃ t≤8*(S.scalar 0+(S.array 1).length)+11,∃ T,
      Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧
      T.array 2=List.replicate (S.scalar 0) 0++S.array 1 := by
  have valid : ValidAtoms M setup S := by simp [setup,ValidAtoms,Atom.Valid,Atom.SmallResult]
  obtain ⟨first,hU⟩ := atoms_runs bounded setup valid
  let U := applyAtoms setup S
  have ux : U.array 0=List.replicate (S.scalar 0) 0 := by simp [U,setup,applyAtoms,Atom.apply,Store.setScalar,Store.setArray]
  have uy : U.array 1=S.array 1 := rfl
  obtain ⟨t,ht,T,run,hT,out,_,_⟩ := NatArrayConcat.concat_runs U M hU (by simpa [ux,uy] using size) room
  refine ⟨2+t,?_,T,first.seq run,hT,?_⟩
  · simp only [ux,uy,List.length_replicate] at ht; omega
  · simpa only [ux,uy] using out

end GroupWL.MachinePrograms.ZeroPrepend
