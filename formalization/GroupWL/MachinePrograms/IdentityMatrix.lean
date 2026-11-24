import GroupWL.MachinePrograms.NatArrayCountedLoops
import GroupWL.MachinePrograms.NatArrayProofs
import GroupWL.MachinePrograms.NatArrayFrames

/-! Materialize an identity matrix by writing its diagonal into a zero array. -/
namespace GroupWL.MachinePrograms.IdentityMatrix
open NatArrayLanguage

inductive Reg where
  | dimension | total | index | todo | position | one | zero
  deriving DecidableEq,Fintype
inductive Arr where
  | output
  deriving DecidableEq,Fintype
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def diagonalPrefix (n : ℕ) : ℕ → List ℕ
  | 0 => List.replicate (n*n) 0
  | i+1 => (diagonalPrefix n i).set (i*n+i) 1
@[simp] theorem diagonalPrefix_length (n i : ℕ) : (diagonalPrefix n i).length=n*n := by
  induction i with
  | zero => simp [diagonalPrefix]
  | succ i ih => simp [diagonalPrefix,ih]

def cellAtoms : List (Atom Reg Arr) := [
  .binary .mul .position .index .dimension,
  .binary .add .position .position .index,
  .write .output .position .one]
def cell : Code := atoms cellAtoms
def program : Code := .seq (atoms [
  .const .one 1,.const .zero 0,.binary .mul .total .dimension .dimension,
  .allocate .output .total .zero]) (countedLoop .index .todo .dimension .one cell)

theorem diagonal_lt {n i : ℕ} (hi : i<n) : i*n+i<n*n := by
  have h := Nat.mul_le_mul_right n (show i+1≤n by omega)
  nlinarith

theorem cell_runs (S : State) (M i : ℕ) (bounded : S.Bounded M)
    (one : S.scalar .one=1) (index : S.scalar .index=i) (hi : i<S.scalar .dimension)
    (length : (S.array .output).length=S.scalar .dimension*S.scalar .dimension) :
    Runs (storageBound Reg Arr M) cell S 3 (applyAtoms cellAtoms S) ∧
    (applyAtoms cellAtoms S).Bounded M ∧
    (applyAtoms cellAtoms S).array .output=(S.array .output).set (i*S.scalar .dimension+i) 1 := by
  have hindex := diagonal_lt hi
  have hsize := bounded.2.1 Arr.output
  have valid : ValidAtoms M cellAtoms S := by
    simp [cellAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,index,length]
    exact ⟨by omega,by omega,hindex⟩
  obtain ⟨run,hT⟩ := atoms_runs bounded cellAtoms valid
  exact ⟨run,hT,by simp [applyAtoms,cellAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,index,one]⟩

structure Invariant (n M i : ℕ) (S : State) : Prop where
  bounded : S.Bounded M
  dimension : S.scalar .dimension=n
  one : S.scalar .one=1
  index : S.scalar .index=i
  todo : S.scalar .todo=n-i
  output : S.array .output=diagonalPrefix n i

theorem loop_runs (S : State) (M : ℕ) (bounded : S.Bounded M) (one : S.scalar .one=1)
    (output : S.array .output=diagonalPrefix (S.scalar .dimension) 0) :
    ∃ t≤6*S.scalar .dimension+3,∃ T,
      Runs (storageBound Reg Arr M) (countedLoop .index .todo .dimension .one cell) S t T ∧
      T.Bounded M ∧ T.array .output=diagonalPrefix (S.scalar .dimension) (S.scalar .dimension) := by
  let S₀ := S.setScalar .todo (S.scalar .dimension)
  let S₁ := S₀.setScalar .index 0
  have h₀ : S₀.Bounded M := bounded.setScalar _ (bounded.1 .dimension)
  have h₁ : S₁.Bounded M := h₀.setScalar _ (Nat.zero_le _)
  have hstart : Invariant (S.scalar .dimension) M 0 S₁ := by
    refine ⟨h₁,?_,?_,?_,?_,?_⟩ <;> simp [S₁,S₀,one,output]
  have control : ∀ i≤S.scalar .dimension,∀ T,Invariant (S.scalar .dimension) M i T →
      T.scalar .index=i ∧ T.scalar .todo=S.scalar .dimension-i ∧ T.scalar .one=1 ∧
      T.size≤storageBound Reg Arr M := by
    intro i hi T hT
    exact ⟨hT.index,hT.todo,hT.one,Store.size_le_of_bounded hT.bounded⟩
  have body : ∀ i<S.scalar .dimension,∀ T,Invariant (S.scalar .dimension) M i T →
      ∃ t≤3,∃ U,Runs (storageBound Reg Arr M) cell T t U ∧
        U.scalar .index=i ∧ U.scalar .todo=S.scalar .dimension-i ∧ U.scalar .one=1 ∧
        (U.setScalar .index (i+1)).size≤storageBound Reg Arr M ∧
        Invariant (S.scalar .dimension) M (i+1) (advance .index .todo U) := by
    intro i hi T hT
    obtain ⟨run,hU,hout⟩ := cell_runs T M i hT.bounded hT.one hT.index
      (by rwa [hT.dimension]) (by rw [hT.output,diagonalPrefix_length,hT.dimension])
    let U := applyAtoms cellAtoms T
    have frame (r : Reg) (hr : r≠Reg.position) : U.scalar r=T.scalar r := by
      apply run.scalar_eq_of_not_mem
      simp [cell,cellAtoms,atoms,NatArrayLanguage.sequence,Program.scalarWrites,Atom.scalarWrites,hr]
    have hx : U.scalar .index=i := (frame .index (by decide)).trans hT.index
    have ht : U.scalar .todo=S.scalar .dimension-i := (frame .todo (by decide)).trans hT.todo
    have ho : U.scalar .one=1 := (frame .one (by decide)).trans hT.one
    have hiM : i+1≤M := le_trans (by omega) (bounded.1 .dimension)
    have hmid := hU.setScalar Reg.index hiM
    have hfinal : (advance .index .todo U).Bounded M := by
      simpa only [advance,hx] using hmid.setScalar Reg.todo ((Nat.sub_le _ _).trans (hU.1 .todo))
    refine ⟨3,le_rfl,U,run,hx,ht,ho,Store.size_le_of_bounded hmid,hfinal,?_,?_,?_,?_,?_⟩
    · simpa [advance,Store.setScalar] using (frame .dimension (by decide)).trans hT.dimension
    · simpa [advance,Store.setScalar] using ho
    · simp [advance,hx]
    · simp [advance,ht,Nat.sub_sub]
    · change U.array .output=diagonalPrefix (S.scalar .dimension) (i+1)
      rw [hout,hT.output,hT.dimension,diagonalPrefix]
  obtain ⟨t,ht,T,run,hT⟩ := countedLoop_runs (storageBound Reg Arr M)
    Reg.index Reg.todo Reg.dimension Reg.one cell (S.scalar .dimension) 3
    (Invariant (S.scalar .dimension) M) S (Store.size_le_of_bounded bounded)
    (Store.size_le_of_bounded h₀) hstart control (by decide) (by decide) body
  exact ⟨t,by nlinarith,T,run,hT.bounded,hT.output⟩

theorem program_runs (S : State) (M : ℕ) (bounded : S.Bounded M) (one : 1≤M)
    (size : S.scalar .dimension*S.scalar .dimension≤M) :
    ∃ t≤6*S.scalar .dimension+7,∃ T,
      Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧
      T.array .output=diagonalPrefix (S.scalar .dimension) (S.scalar .dimension) := by
  let pre : List (Atom Reg Arr) := [
    .const .one 1,.const .zero 0,.binary .mul .total .dimension .dimension,
    .allocate .output .total .zero]
  have valid : ValidAtoms M pre S := by
    simp [pre,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar,one,size]
  obtain ⟨preRun,hU⟩ := atoms_runs bounded pre valid
  let U := applyAtoms pre S
  have hn : U.scalar .dimension=S.scalar .dimension := by
    simp [U,pre,applyAtoms,Atom.apply,Store.setScalar,Store.setArray]
  obtain ⟨t,ht,T,run,hT,hout⟩ := loop_runs U M hU
    (by simp [U,pre,applyAtoms,Atom.apply,Store.setScalar,Store.setArray])
    (by simp [U,pre,applyAtoms,Atom.apply,Store.setScalar,Store.setArray,BinaryOp.eval,diagonalPrefix])
  rw [hn] at ht hout
  exact ⟨4+t,by omega,T,.seq preRun run,hT,hout⟩

end GroupWL.MachinePrograms.IdentityMatrix
