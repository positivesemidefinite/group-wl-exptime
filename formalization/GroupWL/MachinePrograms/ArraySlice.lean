import GroupWL.MachinePrograms.ArrayTabulation
import GroupWL.MachinePrograms.NatArrayCountedLoops
import GroupWL.MachinePrograms.NatArrayFrames

/-! An explicit consecutive subarray copy with charged address arithmetic. -/
namespace GroupWL.MachinePrograms.ArraySlice
open NatArrayLanguage

inductive Reg where
  | offset | length | index | todo | sourceIndex | value | one | zero
  deriving DecidableEq,Fintype
inductive Arr where
  | input | output
  deriving DecidableEq,Fintype
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def cellAtoms : List (Atom Reg Arr) := [
  .binary .add .sourceIndex .offset .index,.read .value .input .sourceIndex,
  .write .output .index .value]
def cell : Code := atoms cellAtoms
def program : Code := .seq (atoms [.const .one 1,.const .zero 0,.allocate .output .length .zero])
  (countedLoop .index .todo .length .one cell)
def value (xs : List ℕ) (offset i : ℕ) : ℕ := xs[offset+i]?.getD 0

theorem cell_runs (S : State) (M : ℕ) (bounded : S.Bounded M)
    (input : S.scalar .offset+S.scalar .index<(S.array .input).length)
    (output : S.scalar .index<(S.array .output).length) :
    Runs (storageBound Reg Arr M) cell S 3 (applyAtoms cellAtoms S) ∧
    (applyAtoms cellAtoms S).Bounded M ∧
    (applyAtoms cellAtoms S).array .output=(S.array .output).set (S.scalar .index)
      (value (S.array .input) (S.scalar .offset) (S.scalar .index)) := by
  have valid : ValidAtoms M cellAtoms S := by
    simp [cellAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar]
    exact ⟨(Nat.le_of_lt input).trans (bounded.2.1 .input),input,output⟩
  obtain ⟨run,hT⟩ := atoms_runs bounded cellAtoms valid
  exact ⟨run,hT,by simp [applyAtoms,cellAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,value]⟩

structure Invariant (xs : List ℕ) (base n M i : ℕ) (S : State) : Prop where
  bounded : S.Bounded M
  input : S.array .input=xs
  offset : S.scalar .offset=base
  length : S.scalar .length=n
  one : S.scalar .one=1
  index : S.scalar .index=i
  todo : S.scalar .todo=n-i
  output : ArrayTabulation.Prefix (value xs base) n i (S.array .output)

theorem loop_runs (S : State) (M : ℕ) (bounded : S.Bounded M) (one : S.scalar .one=1)
    (input : S.scalar .offset+S.scalar .length≤(S.array .input).length)
    (output : S.array .output=List.replicate (S.scalar .length) 0) :
    ∃ t≤6*S.scalar .length+3,∃ T,
      Runs (storageBound Reg Arr M) (countedLoop .index .todo .length .one cell) S t T ∧
      T.Bounded M ∧ T.array .output=List.ofFn (fun i : Fin (S.scalar .length) =>
        value (S.array .input) (S.scalar .offset) i) := by
  let S₀ := S.setScalar .todo (S.scalar .length)
  let S₁ := S₀.setScalar .index 0
  let I := Invariant (S.array .input) (S.scalar .offset) (S.scalar .length) M
  have h₀ : S₀.Bounded M := bounded.setScalar _ (bounded.1 .length)
  have h₁ : S₁.Bounded M := h₀.setScalar _ (Nat.zero_le _)
  have hstart : I 0 S₁ := by
    refine ⟨h₁,rfl,?_,?_,?_,?_,?_,?_⟩
    · simp [S₁,S₀]
    · simp [S₁,S₀]
    · simpa [S₁,S₀] using one
    · simp [S₁]
    · simp [S₁,S₀]
    · simpa [S₁,S₀,output] using ArrayTabulation.Prefix.zero
        (value (S.array .input) (S.scalar .offset)) (S.scalar .length)
  have control : ∀ i≤S.scalar .length,∀ T,I i T →
      T.scalar .index=i ∧ T.scalar .todo=S.scalar .length-i ∧ T.scalar .one=1 ∧
      T.size≤storageBound Reg Arr M := by
    intro i hi T hT
    exact ⟨hT.index,hT.todo,hT.one,Store.size_le_of_bounded hT.bounded⟩
  have body : ∀ i<S.scalar .length,∀ T,I i T →
      ∃ t≤3,∃ U,Runs (storageBound Reg Arr M) cell T t U ∧
        U.scalar .index=i ∧ U.scalar .todo=S.scalar .length-i ∧ U.scalar .one=1 ∧
        (U.setScalar .index (i+1)).size≤storageBound Reg Arr M ∧ I (i+1) (advance .index .todo U) := by
    intro i hi T hT
    obtain ⟨run,hU,hout⟩ := cell_runs T M hT.bounded
      (by rw [hT.offset,hT.index,hT.input]; omega) (by rw [hT.index,hT.output.1]; exact hi)
    let U := applyAtoms cellAtoms T
    have frame (r : Reg) (hr : r≠Reg.sourceIndex ∧ r≠Reg.value) : U.scalar r=T.scalar r := by
      apply run.scalar_eq_of_not_mem
      simp [cell,cellAtoms,atoms,NatArrayLanguage.sequence,Program.scalarWrites,Atom.scalarWrites,hr.1,hr.2]
    have hx : U.scalar .index=i := (frame .index (by decide)).trans hT.index
    have ht : U.scalar .todo=S.scalar .length-i := (frame .todo (by decide)).trans hT.todo
    have ho : U.scalar .one=1 := (frame .one (by decide)).trans hT.one
    have hiM : i+1≤M := le_trans (by omega) (bounded.1 .length)
    have hmid := hU.setScalar Reg.index hiM
    have hfinal : (advance .index .todo U).Bounded M := by
      simpa only [advance,hx] using hmid.setScalar Reg.todo ((Nat.sub_le _ _).trans (hU.1 .todo))
    refine ⟨3,le_rfl,U,run,hx,ht,ho,Store.size_le_of_bounded hmid,hfinal,?_,?_,?_,?_,?_,?_,?_⟩
    · exact (run.array_eq_of_not_mem .input (by decide)).trans hT.input
    · simpa [advance,Store.setScalar] using (frame .offset (by decide)).trans hT.offset
    · simpa [advance,Store.setScalar] using (frame .length (by decide)).trans hT.length
    · simpa [advance,Store.setScalar] using ho
    · simp [advance,hx]
    · simp [advance,ht,Nat.sub_sub]
    · change ArrayTabulation.Prefix _ _ _ (U.array .output)
      rw [hout,hT.index,hT.input,hT.offset]
      exact hT.output.write hi
  obtain ⟨t,ht,T,run,hT⟩ := countedLoop_runs (storageBound Reg Arr M)
    Reg.index Reg.todo Reg.length Reg.one cell (S.scalar .length) 3 I S
    (Store.size_le_of_bounded bounded) (Store.size_le_of_bounded h₀) hstart control
    (by decide) (by decide) body
  exact ⟨t,by nlinarith,T,run,hT.bounded,hT.output.complete⟩

theorem program_runs (S : State) (M : ℕ) (bounded : S.Bounded M) (one : 1≤M)
    (input : S.scalar .offset+S.scalar .length≤(S.array .input).length) :
    ∃ t≤6*S.scalar .length+6,∃ T,
      Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧
      T.array .output=List.ofFn (fun i : Fin (S.scalar .length) =>
        value (S.array .input) (S.scalar .offset) i) := by
  let pre : List (Atom Reg Arr) := [.const .one 1,.const .zero 0,.allocate .output .length .zero]
  have valid : ValidAtoms M pre S := by simp [pre,ValidAtoms,Atom.Valid,Atom.SmallResult,one]
  obtain ⟨preRun,hU⟩ := atoms_runs bounded pre valid
  let U := applyAtoms pre S
  have hlen : U.scalar .length=S.scalar .length := by simp [U,pre,applyAtoms,Atom.apply,Store.setScalar,Store.setArray]
  have hoff : U.scalar .offset=S.scalar .offset := by simp [U,pre,applyAtoms,Atom.apply,Store.setScalar,Store.setArray]
  have hin : U.array .input=S.array .input := rfl
  obtain ⟨t,ht,T,run,hT,hout⟩ := loop_runs U M hU
    (by simp [U,pre,applyAtoms,Atom.apply,Store.setScalar,Store.setArray])
    (by rwa [hlen,hoff,hin])
    (by simp [U,pre,applyAtoms,Atom.apply,Store.setScalar,Store.setArray])
  simp only [hlen,hoff,hin] at ht hout
  exact ⟨3+t,by omega,T,.seq preRun run,hT,hout⟩

end GroupWL.MachinePrograms.ArraySlice
