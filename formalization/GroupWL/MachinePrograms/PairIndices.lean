import GroupWL.MachinePrograms.PairFlags
import GroupWL.MachinePrograms.RangeSelection
import GroupWL.MachinePrograms.NatArrayComponents

/-! The complete ordered frame-pair enumerator. -/
namespace GroupWL.MachinePrograms.PairIndices
open NatArrayLanguage
abbrev Reg := PairFlags.Reg ⊕ SourceNeighbors.Reg
abbrev Arr := PairFlags.Arr ⊕ SourceNeighbors.Arr
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr
def transfer : Atom Reg Arr := .copyArray (.inr .input) (.inl .output)
def program : Code := .seq (PairFlags.program.map Sum.inl Sum.inl)
  (.seq (.atom transfer) (RangeSelection.program.map Sum.inr Sum.inr))

theorem program_runs (q M : ℕ) (hq : 0<q) (hM : 1≤M) (small : q*q≤M)
    (S : State) (bounded : S.Bounded M) (hf : S.left.scalar .frames=q) :
    ∃ t≤q*q*15+18, ∃ T, Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧
      T.right.scalar .count=(RangeSelection.selected (PairFlags.flags q)).length ∧
      (T.right.array .output).length=q*q ∧
      (T.right.array .output).take (T.right.scalar .count)=RangeSelection.selected (PairFlags.flags q) := by
  obtain ⟨t,ht,U,flags,hUB,hUR,hUout⟩ := PairFlags.program_runs q M hq hM small S.left bounded.left hf
  have first := flags.left_bounded bounded
  let V := U.join S.right
  have hVB := hUB.join bounded.right
  let W := transfer.apply V
  have hWB := Atom.apply_bounded hVB transfer trivial
  have copy := atom_runs hVB transfer trivial trivial
  have hi : W.right.array .input=PairFlags.flags q := hUout
  obtain ⟨u,hu,X,selected,hXB,hXi,hXc,hXlen,hXout⟩ := RangeSelection.program_runs
    (PairFlags.flags q) M hM W.right hWB.right hi
  have hlen : (PairFlags.flags q).length=q*q := List.length_ofFn
  rw [hlen] at hu hXlen
  exact ⟨t+(1+u),by omega,W.left.join X,first.seq (copy.seq (selected.right_bounded hWB)),
    hWB.left.join hXB,hXc,hXlen,hXout⟩

end GroupWL.MachinePrograms.PairIndices
