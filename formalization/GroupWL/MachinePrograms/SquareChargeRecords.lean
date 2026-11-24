import GroupWL.MachinePrograms.SquareCharges
import GroupWL.MachinePrograms.SelectAndPrepend

namespace GroupWL.MachinePrograms.SquareChargeRecords
open NatArrayLanguage
abbrev Reg := SquareCharges.Reg ⊕ SelectAndPrepend.Reg
abbrev Arr := SquareCharges.Arr ⊕ SelectAndPrepend.Arr
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def transfer : Atom Reg Arr := .copyArray (.inr (.inl .values)) (.inl .output)
def program : Code := .seq (SquareCharges.program.map Sum.inl Sum.inl)
  (.seq (.atom transfer) (SelectAndPrepend.program.map Sum.inr Sum.inr))
def word (width special count : ℕ) := List.ofFn (fun i : Fin count=>SquareCharges.entry width special i)

theorem program_runs (S : State) (M : ℕ) (bounded : S.Bounded M) (room : 4≤M)
    (width : 0<S.left.scalar .width)
    (flags : (S.right.left.array .flags).length=S.left.scalar .links*S.left.scalar .width*4)
    (binary : ∀x∈S.right.left.array .flags,x≤1)
    (selected : S.right.left.scalar .selected=FilterRanks.count (S.right.left.array .flags) (S.right.left.array .flags).length)
    (size : S.right.right.scalar 0+S.right.left.scalar .selected≤M) :
    ∃t≤18*(S.right.left.array .flags).length+8*(S.right.right.scalar 0+S.right.left.scalar .selected)+30,∃T,
      Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧
      T.right.right.array 2=List.replicate (S.right.right.scalar 0) 0++SelectArray.selectedPrefix
        (S.right.left.array .flags)
        (word (S.left.scalar .width) (S.left.scalar .special) (S.right.left.array .flags).length)
        (S.right.left.array .flags).length := by
  have nM : S.left.scalar .links*S.left.scalar .width*4≤M := by
    rw [←flags]; exact bounded.right.left.2.1 SelectArray.Arr.flags
  obtain ⟨t,ht,U,first,hU,hout⟩ := SquareCharges.program_runs S.left M bounded.left room width nM
  let V := U.join S.right
  have hV : V.Bounded M := hU.join bounded.right
  let W := transfer.apply V
  have hW : W.Bounded M := transfer.apply_bounded hV trivial
  have copy := atom_runs hV transfer trivial trivial
  have wi : W.right.left.array .values=word (S.left.scalar .width) (S.left.scalar .special)
      (S.right.left.array .flags).length := by simpa only [word,flags] using hout
  have wf : W.right.left.array .flags=S.right.left.array .flags := rfl
  have ws : W.right.left.scalar .selected=S.right.left.scalar .selected := rfl
  have wp : W.right.right.scalar 0=S.right.right.scalar 0 := rfl
  obtain ⟨u,hu,X,last,hX,hresult⟩ := SelectAndPrepend.program_runs W.right M hW.right (by omega)
    (by rw [wi,wf]; simp [word]) (by rwa [wf]) (by rwa [ws,wf]) (by rwa [wp,ws])
  refine ⟨t+(1+u),?_,W.left.join X,(first.left_bounded bounded).seq (copy.seq (last.right_bounded hW)),hW.left.join hX,?_⟩
  · rw [wf,wp,ws] at hu
    rw [←flags] at ht
    omega
  · simpa only [Store.right_join,wi,wf,wp] using hresult

end GroupWL.MachinePrograms.SquareChargeRecords
