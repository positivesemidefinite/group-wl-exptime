import GroupWL.MachinePrograms.SelectArray
import GroupWL.MachinePrograms.ZeroPrepend
import GroupWL.MachinePrograms.NatArrayComponents

namespace GroupWL.MachinePrograms.SelectAndPrepend
open NatArrayLanguage
set_option maxHeartbeats 1500000
abbrev Reg := SelectArray.Reg ⊕ ZeroPrepend.Reg
abbrev Arr := SelectArray.Arr ⊕ ZeroPrepend.Arr
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def transfer : Atom Reg Arr := .copyArray (.inr 1) (.inl .output)
def program : Code := .seq (SelectArray.program.map Sum.inl Sum.inl)
  (.seq (.atom transfer) (ZeroPrepend.program.map Sum.inr Sum.inr))

theorem program_runs (S : State) (M : ℕ) (bounded : S.Bounded M) (room : 1≤M)
    (values : (S.left.array .values).length=(S.left.array .flags).length)
    (binary : ∀x∈S.left.array .flags,x≤1)
    (selected : S.left.scalar .selected=FilterRanks.count (S.left.array .flags) (S.left.array .flags).length)
    (size : S.right.scalar 0+S.left.scalar .selected≤M) :
    ∃ t≤8*(S.left.array .flags).length+8*(S.right.scalar 0+S.left.scalar .selected)+20,∃ T,
      Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧
      T.right.array 2=List.replicate (S.right.scalar 0) 0++
        SelectArray.selectedPrefix (S.left.array .flags) (S.left.array .values) (S.left.array .flags).length := by
  obtain ⟨t,ht,U,run,hU,hout,_⟩ := SelectArray.program_runs S.left M bounded.left room values binary selected
  let V := U.join S.right
  have hV : V.Bounded M := hU.join bounded.right
  have lifted := run.left_bounded bounded
  let W := transfer.apply V
  have copy := atom_runs hV transfer trivial trivial
  have hW : W.Bounded M := transfer.apply_bounded hV trivial
  have wi : W.right.array 1=SelectArray.selectedPrefix (S.left.array .flags)
      (S.left.array .values) (S.left.array .flags).length := hout
  have wp : W.right.scalar 0=S.right.scalar 0 := rfl
  have wlen : (W.right.array 1).length=S.left.scalar .selected := by
    rw [wi,SelectArray.selectedPrefix_length _ _ binary,selected]
  obtain ⟨u,hu,X,last,hX,hresult⟩ := ZeroPrepend.program_runs W.right M hW.right room
    (by rwa [wp,wlen])
  refine ⟨t+(1+u),?_,W.left.join X,lifted.seq (copy.seq (last.right_bounded hW)),hW.left.join hX,?_⟩
  · rw [wp,wlen] at hu; omega
  · simpa only [Store.right_join,wi,wp] using hresult

end GroupWL.MachinePrograms.SelectAndPrepend
