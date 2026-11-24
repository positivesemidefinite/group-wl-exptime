import GroupWL.MachinePrograms.PadRepeatedSelection

/-! Horizontal source dimensions followed by the scalar vertical dimensions. -/
namespace GroupWL.MachinePrograms.ReadoutDimensionProgram
open NatArrayLanguage
set_option maxHeartbeats 1800000
abbrev Reg := PadRepeatedSelection.Reg ⊕ ArrayPad.Reg
abbrev Arr := PadRepeatedSelection.Arr ⊕ ArrayPad.Arr
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def setup : List (Atom Reg Arr) := [
  .const (.inl (.inl .padding)) 1,.const (.inr .padding) 1]
def transfer : Atom Reg Arr := .copyArray (.inr .input) (.inl (.inr (.inr .output)))
def program : Code := .seq (atoms setup)
  (.seq (PadRepeatedSelection.program.map Sum.inl Sum.inl)
    (.seq (.atom transfer) (ArrayPad.program.map Sum.inr Sum.inr)))

def dimensions (xs flags : List ℕ) (nodes repeats total : ℕ) : List ℕ :=
  PadRepeatedSelection.padded
    (SelectArray.selectedPrefix flags
      (RepeatedSelection.repeated (PadRepeatedSelection.padded xs 1 nodes) nodes 1 repeats) flags.length)
    1 total

theorem program_runs (S : State) (M : ℕ) (bounded : S.Bounded M) (room : 1≤M)
    (flags : (S.left.right.right.array .flags).length=S.left.left.scalar .count*S.left.right.left.scalar .repeats)
    (binary : ∀x∈S.left.right.right.array .flags,x≤1)
    (selected : S.left.right.right.scalar .selected=FilterRanks.count
      (S.left.right.right.array .flags) (S.left.right.right.array .flags).length) :
    ∃ t≤7*S.left.left.scalar .count+17*(S.left.right.right.array .flags).length+7*S.right.scalar .count+37,∃ T,
      Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧
      T.right.array .output=dimensions (S.left.left.array .input) (S.left.right.right.array .flags)
        (S.left.left.scalar .count) (S.left.right.left.scalar .repeats) (S.right.scalar .count) := by
  have valid : ValidAtoms M setup S := by simp [setup,ValidAtoms,Atom.Valid,Atom.SmallResult,room]
  obtain ⟨first,hU⟩ := atoms_runs bounded setup valid
  let U := applyAtoms setup S
  obtain ⟨t,ht,V,middle,hV,hout⟩ := PadRepeatedSelection.program_runs U.left M hU.left room flags binary selected
  have middleRun := middle.left_bounded hU
  let W := V.join U.right
  have hW : W.Bounded M := hV.join hU.right
  let X := transfer.apply W
  have copy := atom_runs hW transfer trivial trivial
  have hX : X.Bounded M := transfer.apply_bounded hW trivial
  have xi : X.right.array .input=SelectArray.selectedPrefix (S.left.right.right.array .flags)
      (RepeatedSelection.repeated (PadRepeatedSelection.padded (S.left.left.array .input) 1 (S.left.left.scalar .count))
        (S.left.left.scalar .count) 1 (S.left.right.left.scalar .repeats)) (S.left.right.right.array .flags).length := hout
  have xc : X.right.scalar .count=S.right.scalar .count := rfl
  have xp : X.right.scalar .padding=1 := rfl
  obtain ⟨u,hu,Y,last,hY,hresult⟩ := ArrayPad.program_runs X.right M hX.right room
  refine ⟨2+(t+(1+u)),?_,X.left.join Y,first.seq (middleRun.seq (copy.seq (last.right_bounded hX))),hX.left.join hY,?_⟩
  · change t≤7*S.left.left.scalar .count+17*(S.left.right.right.array .flags).length+27 at ht
    rw [xc] at hu
    omega
  · simpa only [Store.right_join,xi,xc,xp,dimensions,PadRepeatedSelection.padded] using hresult

end GroupWL.MachinePrograms.ReadoutDimensionProgram
