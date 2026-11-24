import GroupWL.MachinePrograms.ArrayPad
import GroupWL.MachinePrograms.RepeatedSelection

/-! Pad per-node data, repeat it over candidate positions, and filter the positions. -/
namespace GroupWL.MachinePrograms.PadRepeatedSelection
open NatArrayLanguage
set_option maxHeartbeats 1500000
abbrev Reg := ArrayPad.Reg ⊕ RepeatedSelection.Reg
abbrev Arr := ArrayPad.Arr ⊕ RepeatedSelection.Arr
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def padded (xs : List ℕ) (padding n : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin n => ArrayPad.entry xs padding i)
def transfer : List (Atom Reg Arr) := [
  .copyArray (.inr (.inl .input)) (.inl .output),
  .copy (.inr (.inl .blocks)) (.inl .count),.const (.inr (.inl .width)) 1]
def program : Code := .seq (ArrayPad.program.map Sum.inl Sum.inl)
  (.seq (atoms transfer) (RepeatedSelection.program.map Sum.inr Sum.inr))

theorem program_runs (S : State) (M : ℕ) (bounded : S.Bounded M) (room : 1≤M)
    (flags : (S.right.right.array .flags).length=S.left.scalar .count*S.right.left.scalar .repeats)
    (binary : ∀x∈S.right.right.array .flags,x≤1)
    (selected : S.right.right.scalar .selected=FilterRanks.count (S.right.right.array .flags) (S.right.right.array .flags).length) :
    ∃ t≤7*S.left.scalar .count+17*(S.right.right.array .flags).length+27,∃ T,
      Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧
      T.right.right.array .output=SelectArray.selectedPrefix (S.right.right.array .flags)
        (RepeatedSelection.repeated (padded (S.left.array .input) (S.left.scalar .padding) (S.left.scalar .count))
          (S.left.scalar .count) 1 (S.right.left.scalar .repeats)) (S.right.right.array .flags).length := by
  obtain ⟨t,ht,U,run,hU,hout⟩ := ArrayPad.program_runs S.left M bounded.left room
  let V := U.join S.right
  have hV : V.Bounded M := hU.join bounded.right
  have lifted := run.left_bounded bounded
  have uc : U.scalar .count=S.left.scalar .count := run.scalar_eq_of_not_mem .count (by decide)
  have valid : ValidAtoms M transfer V := by
    simp [transfer,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,Store.setScalar,uc]
    exact room
  obtain ⟨copy,hW⟩ := atoms_runs hV transfer valid
  let W := applyAtoms transfer V
  have wi : W.right.left.array .input=padded (S.left.array .input) (S.left.scalar .padding) (S.left.scalar .count) := hout
  have wb : W.right.left.scalar .blocks=S.left.scalar .count := uc
  have ww : W.right.left.scalar .width=1 := by simp [W,transfer,applyAtoms,Atom.apply,Store.setScalar,Store.right,Store.left]
  have wr : W.right.left.scalar .repeats=S.right.left.scalar .repeats := rfl
  have wf : W.right.right.array .flags=S.right.right.array .flags := rfl
  have ws : W.right.right.scalar .selected=S.right.right.scalar .selected := rfl
  obtain ⟨u,hu,X,last,hX,hresult⟩ := RepeatedSelection.program_runs W.right M hW.right room
    (by rw [wi,wb,ww]; simp [padded]) (by rw [wf,wb,ww,wr]; simpa using flags)
    (by rwa [wf]) (by rwa [ws,wf])
  refine ⟨t+(3+u),?_,W.left.join X,lifted.seq (copy.seq (last.right_bounded hW)),hW.left.join hX,?_⟩
  · rw [wf] at hu; omega
  · simpa only [Store.right_join,wi,wb,ww,wr,wf] using hresult

end GroupWL.MachinePrograms.PadRepeatedSelection
