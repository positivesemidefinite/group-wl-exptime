import GroupWL.MachinePrograms.InternalDescriptorRecords
import GroupWL.MachinePrograms.EdgeWedgeDescriptors
import GroupWL.MachinePrograms.NatArrayConcat

/-! Both descriptor families in the exact internal-then-incidence output order. -/
namespace GroupWL.MachinePrograms.WedgeDescriptorTables
open NatArrayLanguage NatArrayExpressions
set_option maxHeartbeats 3000000
set_option synthInstance.maxSize 2048
abbrev Field := InternalWedgeDescriptors.Field
abbrev Clients (f : Field) := InternalDescriptorRecords.Reg f ⊕ Registers EdgeWedgeDescriptors.Reg (EdgeWedgeDescriptors.expression f).need
abbrev ClientArrays := InternalDescriptorRecords.Arr ⊕ EdgeWedgeDescriptors.Arr
abbrev Reg (f : Field) := Clients f ⊕ NatArrayConcat.Reg
abbrev Arr := ClientArrays ⊕ NatArrayConcat.Arr
abbrev State (f : Field) := Store (Reg f) Arr
abbrev Code (f : Field) := Program (Reg f) Arr

def transfer (f : Field) : List (Atom (Reg f) Arr) := [
  .copyArray (.inr 0) (.inl (.inl (.inr .output))),.copyArray (.inr 1) (.inl (.inr .output))]
def program (f : Field) : Code f := .seq
  (((InternalDescriptorRecords.program f).map Sum.inl Sum.inl).map Sum.inl Sum.inl)
  (.seq (((EdgeWedgeDescriptors.program f).map Sum.inr Sum.inr).map Sum.inl Sum.inl)
    (.seq (atoms (transfer f)) (NatArrayConcat.concat.map Sum.inr Sum.inr)))
def edgeWord (D : EdgeWedgeDescriptors.Data) (f : Field) :=
  List.ofFn (fun i : Fin (D.edges*D.frames*D.frames*2)=>EdgeWedgeDescriptors.value D f i)

theorem program_runs (D : InternalWedgeDescriptors.Data) (E : EdgeWedgeDescriptors.Data) (f : Field)
    (M : ℕ) (di : InternalWedgeDescriptors.Valid D M) (de : EdgeWedgeDescriptors.Valid E M)
    (S : State f) (bounded : S.Bounded M)
    (readyI : InternalWedgeDescriptors.Ready D (inputs S.left.left.left))
    (readyE : EdgeWedgeDescriptors.Ready E (inputs S.left.right))
    (totalI : S.left.left.left.scalar (.inl .total)=D.vertices*D.pairs*D.cap)
    (totalE : S.left.right.scalar (.inl .total)=E.edges*E.frames*E.frames*2)
    (flags : (S.left.left.right.array .flags).length=D.vertices*D.pairs*D.cap)
    (binary : ∀x∈S.left.left.right.array .flags,x≤1)
    (selected : S.left.left.right.scalar .selected=FilterRanks.count (S.left.left.right.array .flags) (S.left.left.right.array .flags).length)
    (size : S.left.left.right.scalar .selected+E.edges*E.frames*E.frames*2≤M) :
    ∃t≤(D.vertices*D.pairs*D.cap)*((InternalWedgeDescriptors.expression f).cost+12)+
      (E.edges*E.frames*E.frames*2)*((EdgeWedgeDescriptors.expression f).cost+4)+
      8*(S.left.left.right.scalar .selected+E.edges*E.frames*E.frames*2)+32,∃T,
      Runs (storageBound (Reg f) Arr M) (program f) S t T ∧ T.Bounded M ∧
      T.right.array 2=SelectArray.selectedPrefix (S.left.left.right.array .flags)
        (InternalDescriptorRecords.word D f) (S.left.left.right.array .flags).length++edgeWord E f := by
  obtain ⟨t,ht,U,first,hU,hout⟩ := InternalDescriptorRecords.program_runs D f M di S.left.left
    bounded.left.left readyI totalI flags binary selected
  let V := (U.join S.left.right).join S.right
  have hV : V.Bounded M := (hU.join bounded.left.right).join bounded.right
  have firstRun := (first.left_bounded bounded.left).left_bounded bounded
  obtain ⟨u,hu,X,second,hX,_,hxe⟩ := EdgeWedgeDescriptors.program_runs E f M de V.left.right hV.left.right readyE totalE
  let W := (V.left.left.join X).join V.right
  have hW : W.Bounded M := (hV.left.left.join hX).join hV.right
  have secondRun := (second.right_bounded hV.left).left_bounded hV
  have valid : ValidAtoms M (transfer f) W := by simp [transfer,ValidAtoms,Atom.Valid,Atom.SmallResult]
  obtain ⟨copy,hY⟩ := atoms_runs hW (transfer f) valid
  let Y := applyAtoms (transfer f) W
  have yi : Y.right.array 0=SelectArray.selectedPrefix (S.left.left.right.array .flags)
      (InternalDescriptorRecords.word D f) (S.left.left.right.array .flags).length := hout
  have ye : Y.right.array 1=edgeWord E f := hxe
  have yilen : (Y.right.array 0).length=S.left.left.right.scalar .selected := by
    rw [yi,SelectArray.selectedPrefix_length _ _ binary,selected]
  have yelen : (Y.right.array 1).length=E.edges*E.frames*E.frames*2 := by rw [ye]; exact List.length_ofFn
  obtain ⟨v,hv,Z,last,hZ,hresult,_,_⟩ := NatArrayConcat.concat_runs Y.right M hY.right
    (by rwa [yilen,yelen]) di.room
  refine ⟨t+(u+(2+v)),?_,Y.left.join Z,
    firstRun.seq (secondRun.seq (copy.seq (last.right_bounded hY))),hY.left.join hZ,?_⟩
  · rw [yilen,yelen] at hv
    omega
  · simpa only [Store.right_join,yi,ye] using hresult

end GroupWL.MachinePrograms.WedgeDescriptorTables
