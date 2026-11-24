import GroupWL.MachinePrograms.InternalWedgeDescriptors
import GroupWL.MachinePrograms.SelectArray
import GroupWL.MachinePrograms.NatArrayComponents

namespace GroupWL.MachinePrograms.InternalDescriptorRecords
open NatArrayLanguage NatArrayExpressions
abbrev Field := InternalWedgeDescriptors.Field
abbrev Reg (f : Field) := Registers InternalWedgeDescriptors.Reg (InternalWedgeDescriptors.expression f).need ⊕ SelectArray.Reg
abbrev Arr := InternalWedgeDescriptors.Arr ⊕ SelectArray.Arr
abbrev State (f : Field) := Store (Reg f) Arr
abbrev Code (f : Field) := Program (Reg f) Arr

def transfer (f : Field) : Atom (Reg f) Arr := .copyArray (.inr .values) (.inl .output)
def program (f : Field) : Code f := .seq ((InternalWedgeDescriptors.program f).map Sum.inl Sum.inl)
  (.seq (.atom (transfer f)) (SelectArray.program.map Sum.inr Sum.inr))
def word (D : InternalWedgeDescriptors.Data) (f : Field) :=
  List.ofFn (fun i : Fin (D.vertices*D.pairs*D.cap)=>InternalWedgeDescriptors.value D f i)

theorem program_runs (D : InternalWedgeDescriptors.Data) (f : Field) (M : ℕ)
    (valid : InternalWedgeDescriptors.Valid D M) (S : State f) (bounded : S.Bounded M)
    (ready : InternalWedgeDescriptors.Ready D (inputs S.left))
    (total : S.left.scalar (.inl .total)=D.vertices*D.pairs*D.cap)
    (flags : (S.right.array .flags).length=D.vertices*D.pairs*D.cap)
    (binary : ∀x∈S.right.array .flags,x≤1)
    (selected : S.right.scalar .selected=FilterRanks.count (S.right.array .flags) (S.right.array .flags).length) :
    ∃t≤(D.vertices*D.pairs*D.cap)*((InternalWedgeDescriptors.expression f).cost+12)+15,∃T,
      Runs (storageBound (Reg f) Arr M) (program f) S t T ∧ T.Bounded M ∧
      T.right.array .output=SelectArray.selectedPrefix (S.right.array .flags) (word D f) (S.right.array .flags).length := by
  obtain ⟨t,ht,U,first,hU,_,hout⟩ := InternalWedgeDescriptors.program_runs D f M valid S.left bounded.left ready total
  let V := U.join S.right
  have hV : V.Bounded M := hU.join bounded.right
  let W := (transfer f).apply V
  have hW : W.Bounded M := (transfer f).apply_bounded hV trivial
  have copy := atom_runs hV (transfer f) trivial trivial
  have wi : W.right.array .values=word D f := hout
  have wf : W.right.array .flags=S.right.array .flags := rfl
  have ws : W.right.scalar .selected=S.right.scalar .selected := rfl
  obtain ⟨u,hu,X,last,hX,hresult,_⟩ := SelectArray.program_runs W.right M hW.right valid.room
    (by rw [wi,wf]; simpa [word] using flags.symm) (by rwa [wf]) (by rwa [ws,wf])
  refine ⟨t+(1+u),?_,W.left.join X,(first.left_bounded bounded).seq (copy.seq (last.right_bounded hW)),hW.left.join hX,?_⟩
  · rw [wf,flags] at hu; nlinarith
  · simpa only [Store.right_join,wi,wf] using hresult

end GroupWL.MachinePrograms.InternalDescriptorRecords
