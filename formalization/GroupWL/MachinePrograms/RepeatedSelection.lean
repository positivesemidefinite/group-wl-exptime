import GroupWL.MachinePrograms.ArrayRepeatBlocks
import GroupWL.MachinePrograms.SelectArray
import GroupWL.MachinePrograms.NatArrayComponents

/-! Repeat fixed-width records, then retain the entries selected by a Boolean mask. -/
namespace GroupWL.MachinePrograms.RepeatedSelection
open NatArrayLanguage
set_option maxHeartbeats 1500000
abbrev Reg := ArrayRepeatBlocks.Reg ⊕ SelectArray.Reg
abbrev Arr := ArrayRepeatBlocks.Arr ⊕ SelectArray.Arr
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def repeated (xs : List ℕ) (blocks width repeats : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin (blocks*width*repeats) => ArrayRepeatBlocks.entry xs width repeats i)
def transfer : Atom Reg Arr := .copyArray (.inr .values) (.inl .output)
def program : Code := .seq (ArrayRepeatBlocks.program.map Sum.inl Sum.inl)
  (.seq (.atom transfer) (SelectArray.program.map Sum.inr Sum.inr))

theorem program_runs (S : State) (M : ℕ) (bounded : S.Bounded M) (room : 1≤M)
    (input : (S.left.array .input).length=S.left.scalar .blocks*S.left.scalar .width)
    (flags : (S.right.array .flags).length=S.left.scalar .blocks*S.left.scalar .width*S.left.scalar .repeats)
    (binary : ∀x∈S.right.array .flags,x≤1)
    (selected : S.right.scalar .selected=FilterRanks.count (S.right.array .flags) (S.right.array .flags).length) :
    ∃ t≤17*(S.right.array .flags).length+17,∃ T,
      Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧
      T.right.array .output=SelectArray.selectedPrefix (S.right.array .flags)
        (repeated (S.left.array .input) (S.left.scalar .blocks) (S.left.scalar .width) (S.left.scalar .repeats))
        (S.right.array .flags).length := by
  have size : S.left.scalar .blocks*S.left.scalar .width*S.left.scalar .repeats≤M := by
    rw [← flags]; exact bounded.right.2.1 SelectArray.Arr.flags
  obtain ⟨t,ht,U,run,hU,hout⟩ := ArrayRepeatBlocks.program_runs S.left M bounded.left room input size
  let V := U.join S.right
  have hV : V.Bounded M := hU.join bounded.right
  have lifted := run.left_bounded bounded
  let W := transfer.apply V
  have copy := atom_runs hV transfer trivial trivial
  have hW : W.Bounded M := transfer.apply_bounded hV trivial
  have wf : W.right.array .flags=S.right.array .flags := rfl
  have wv : W.right.array .values=repeated (S.left.array .input) (S.left.scalar .blocks)
      (S.left.scalar .width) (S.left.scalar .repeats) := hout
  have wselected : W.right.scalar .selected=S.right.scalar .selected := rfl
  obtain ⟨u,hu,X,last,hX,hresult,hcount⟩ := SelectArray.program_runs W.right M hW.right room
    (by rw [wv,wf]; simpa [repeated] using flags.symm) (by rwa [wf])
    (by rwa [wselected,wf])
  refine ⟨t+(1+u),?_,W.left.join X,lifted.seq (copy.seq (last.right_bounded hW)),hW.left.join hX,?_⟩
  · rw [← flags] at ht
    rw [wf] at hu
    omega
  · simpa only [Store.right_join,wv,wf] using hresult

end GroupWL.MachinePrograms.RepeatedSelection
