import GroupWL.MachinePrograms.LinkForms
import GroupWL.MachinePrograms.RepeatedSelection

/-! Complete link-form expansion and selection into padded square records. -/
namespace GroupWL.MachinePrograms.LinkFormRecords
open NatArrayLanguage
set_option maxHeartbeats 1800000
abbrev Reg := LinkForms.Reg ⊕ RepeatedSelection.Reg
abbrev Arr := LinkForms.Arr ⊕ RepeatedSelection.Arr
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def transfer : List (Atom Reg Arr) := [
  .copyArray (.inr (.inl .input)) (.inl .output),.const (.inr (.inl .width)) 2,
  .binary .mul (.inr (.inl .blocks)) (.inl .comparisons) (.inl .length),
  .binary .add (.inr (.inl .blocks)) (.inr (.inl .blocks)) (.inl .comparisons),
  .binary .add (.inr (.inl .blocks)) (.inr (.inl .blocks)) (.inl .comparisons)]
def program (right : Bool) : Code := .seq ((LinkForms.program right).map Sum.inl Sum.inl)
  (.seq (atoms transfer) (RepeatedSelection.program.map Sum.inr Sum.inr))
def forms (right : Bool) (xs : List ℕ) (e L : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin ((e+e*L+e)*2) => LinkForms.entry right xs e L i)

theorem program_runs (right : Bool) (S : State) (M : ℕ) (bounded : S.Bounded M) (room : 2≤M)
    (size : (S.left.scalar .comparisons+S.left.scalar .comparisons*S.left.scalar .length+S.left.scalar .comparisons)*2≤M)
    (input : (S.left.array .forms).length=2*S.left.scalar .comparisons)
    (flags : (S.right.right.array .flags).length=
      (S.left.scalar .comparisons+S.left.scalar .comparisons*S.left.scalar .length+S.left.scalar .comparisons)*2*S.right.left.scalar .repeats)
    (binary : ∀x∈S.right.right.array .flags,x≤1)
    (selected : S.right.right.scalar .selected=FilterRanks.count (S.right.right.array .flags) (S.right.right.array .flags).length) :
    ∃ t≤9*((S.left.scalar .comparisons+S.left.scalar .comparisons*S.left.scalar .length+S.left.scalar .comparisons)*2)+
        17*(S.right.right.array .flags).length+35,∃ T,
      Runs (storageBound Reg Arr M) (program right) S t T ∧ T.Bounded M ∧
      T.right.right.array .output=SelectArray.selectedPrefix (S.right.right.array .flags)
        (RepeatedSelection.repeated
          (forms right (S.left.array .forms) (S.left.scalar .comparisons) (S.left.scalar .length))
          (S.left.scalar .comparisons+S.left.scalar .comparisons*S.left.scalar .length+S.left.scalar .comparisons)
          2 (S.right.left.scalar .repeats)) (S.right.right.array .flags).length := by
  obtain ⟨t,ht,U,run,hU,hout⟩ := LinkForms.program_runs right S.left M bounded.left room size input
  let V := U.join S.right
  have hV : V.Bounded M := hU.join bounded.right
  have lifted := run.left_bounded bounded
  have ue : U.scalar .comparisons=S.left.scalar .comparisons :=
    run.scalar_eq_of_not_mem .comparisons (by cases right <;> decide)
  have ul : U.scalar .length=S.left.scalar .length :=
    run.scalar_eq_of_not_mem .length (by cases right <;> decide)
  have valid : ValidAtoms M transfer V := by
    simp [transfer,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar,V,Store.join,ue,ul]
    omega
  obtain ⟨copy,hW⟩ := atoms_runs hV transfer valid
  let W := applyAtoms transfer V
  have wi : W.right.left.array .input=forms right (S.left.array .forms) (S.left.scalar .comparisons) (S.left.scalar .length) := hout
  have wb : W.right.left.scalar .blocks=S.left.scalar .comparisons+S.left.scalar .comparisons*S.left.scalar .length+S.left.scalar .comparisons := by
    simp [W,transfer,applyAtoms,Atom.apply,Store.setScalar,Store.left,Store.right,V,Store.join,ue,ul,BinaryOp.eval,Nat.add_comm]
  have ww : W.right.left.scalar .width=2 := by
    simp [W,transfer,applyAtoms,Atom.apply,Store.setScalar,Store.left,Store.right]
  have wr : W.right.left.scalar .repeats=S.right.left.scalar .repeats := rfl
  have wf : W.right.right.array .flags=S.right.right.array .flags := rfl
  have ws : W.right.right.scalar .selected=S.right.right.scalar .selected := rfl
  obtain ⟨u,hu,X,last,hX,hresult⟩ := RepeatedSelection.program_runs W.right M hW.right (by omega)
    (by rw [wi,wb,ww]; simp [forms]) (by rwa [wf,wb,ww,wr])
    (by rwa [wf]) (by rwa [ws,wf])
  refine ⟨t+(5+u),?_,W.left.join X,lifted.seq (copy.seq (last.right_bounded hW)),hW.left.join hX,?_⟩
  · rw [wf] at hu; omega
  · simpa only [Store.right_join,wi,wb,ww,wr,wf] using hresult

end GroupWL.MachinePrograms.LinkFormRecords
