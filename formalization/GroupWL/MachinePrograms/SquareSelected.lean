import GroupWL.MachinePrograms.SquareIndicesLayout
import GroupWL.MachinePrograms.SelectArray
import GroupWL.MachinePrograms.LayoutFlagPrograms

/-! Executable endpoint generation followed by stable square compaction. -/
namespace GroupWL.MachinePrograms.SquareSelected
open NatArrayLanguage LayoutMetadata
set_option maxHeartbeats 2000000
abbrev Reg := SquareIndices.Reg⊕SelectArray.Reg
abbrev Arr := SquareIndices.Arr⊕SelectArray.Arr
abbrev State := Store Reg Arr
abbrev Code := NatArrayLanguage.Program Reg Arr
abbrev Endpoint := SquareIndices.Endpoint

def transfer : Atom Reg Arr := .copyArray (.inr .values) (.inl .output)
def program (which : Endpoint) : Code := .seq ((SquareIndices.program which).map Sum.inl Sum.inl)
  (.seq (.atom transfer) (SelectArray.program.map Sum.inr Sum.inr))
def word (C : ComparisonMetadata.Table) (L : ℕ) (which : Endpoint) : List ℕ :=
  SelectArray.selectedPrefix (squareFlags C L)
    (List.ofFn (fun i : Fin (linkCount C L*C.coordinates*4) => SquareIndices.layoutEntry C L which i))
    (squareFlags C L).length

structure Input (C : ComparisonMetadata.Table) (L : ℕ) (S : State) : Prop where
  context : SquareIndices.Context (SquareIndices.layoutData C L) S.left
  total : S.left.scalar .total=linkCount C L*C.coordinates*4
  flags : S.right.array .flags=squareFlags C L
  selected : S.right.scalar .selected=squareCount C L

theorem program_runs (which : Endpoint) (C : ComparisonMetadata.Table) (L M : ℕ) (S : State)
    (bounded : S.Bounded M) (input : Input C L S)
    (valid : SquareIndices.Data.Valid (SquareIndices.layoutData C L) M)
    (binary : ∀x∈C.domain,x≤1) :
    ∃t≤49*(linkCount C L*C.coordinates*4)+13,∃T,
      Runs (storageBound Reg Arr M) (program which) S t T ∧ T.Bounded M ∧
      Input C L T ∧ T.right.array .output=word C L which := by
  have room : 1≤M := by simpa [input.context.one] using bounded.left.1 SquareIndices.Reg.one
  obtain ⟨t,ht,U,run,hU,hcontext,hout⟩ := SquareIndices.layout_program_runs which C L M S.left
    bounded.left input.context valid input.total
  let V := U.join S.right
  have hV : V.Bounded M := hU.join bounded.right
  let W := transfer.apply V
  have copy := atom_runs hV transfer trivial trivial
  have hW := transfer.apply_bounded hV trivial
  have wf : W.right.array .flags=squareFlags C L := input.flags
  have ws : W.right.scalar .selected=squareCount C L := input.selected
  have wv : W.right.array .values=List.ofFn
      (fun i : Fin (linkCount C L*C.coordinates*4) => SquareIndices.layoutEntry C L which i) := hout
  obtain ⟨s,hs,X,last,hX,hresult,_⟩ := SelectArray.program_runs W.right M hW.right room
    (by rw [wf,wv];simp [squareFlags])
    (by rw [wf];exact LayoutFlagPrograms.square_binary C L binary)
    (by rw [wf,ws];rfl)
  refine ⟨t+(1+s),?_,W.left.join X,(run.left_bounded bounded).seq
    (copy.seq (last.right_bounded hW)),hW.left.join hX,?_,?_⟩
  · rw [wf] at hs;simp only [squareFlags,List.length_ofFn] at hs;omega
  · refine ⟨hcontext,?_,?_,?_⟩
    · exact (run.scalar_eq_of_not_mem .total (by cases which <;> decide)).trans input.total
    · exact (last.array_eq_of_not_mem .flags (by decide)).trans wf
    · exact (last.scalar_eq_of_not_mem .selected (by decide)).trans ws
  · simpa only [word,wf,wv] using hresult

end GroupWL.MachinePrograms.SquareSelected
