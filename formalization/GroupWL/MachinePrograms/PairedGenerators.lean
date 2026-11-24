import GroupWL.MachinePrograms.ArrayTabulation
import GroupWL.MachinePrograms.NatArrayCountedLoops
import GroupWL.MachinePrograms.NatArrayFrames

/-! Materialize paired tuple indices from two numeric tuple arrays. -/
namespace GroupWL.MachinePrograms.PairedGenerators
open NatArrayLanguage ArrayTabulation
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

inductive Reg where
  | cols | length | one | zero | index | todo | left | right | value
  deriving DecidableEq,Fintype
inductive Arr where
  | left | right | output
  deriving DecidableEq,Fintype
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def value (xs ys : List ℕ) (m i : ℕ) : ℕ := xs[i]?.getD 0*m+ys[i]?.getD 0

def bodyAtoms : List (Atom Reg Arr) := [
  .read .left .left .index,.read .right .right .index,
  .binary .mul .value .left .cols,.binary .add .value .value .right,.write .output .index .value]
def body : Code := atoms bodyAtoms
def prelude : List (Atom Reg Arr) := [
  .const .one 1,.const .zero 0,.arrayLength .length .left,.allocate .output .length .zero]
def build : Code := .seq (atoms prelude) (countedLoop .index .todo .length .one body)

theorem body_runs {n m k : ℕ} (a : Fin k → Fin n) (b : Fin k → Fin m)
    (S : State) (M : ℕ) (i : Fin k) (hb : S.Bounded M)
    (hm : S.scalar .cols=m) (hi : S.scalar .index=i.val)
    (ha : S.array .left=List.ofFn (fun j => (a j).val))
    (hb' : S.array .right=List.ofFn (fun j => (b j).val))
    (hlen : (S.array .output).length=k) (hroom : n*m≤M) :
    Runs (storageBound Reg Arr M) body S 5 (applyAtoms bodyAtoms S) ∧
      (applyAtoms bodyAtoms S).Bounded M ∧
      (applyAtoms bodyAtoms S).array .output=(S.array .output).set i.val
        (value (S.array .left) (S.array .right) m i.val) := by
  have hprod : (a i).val*m≤M := by nlinarith [(a i).isLt]
  have hpair : (a i).val*m+(b i).val≤M := by nlinarith [(a i).isLt,(b i).isLt]
  have hv : ValidAtoms M bodyAtoms S := by
    simp [bodyAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,Store.setArray,hi,hm,ha,hb',hlen,hprod,hpair]
  obtain ⟨run,hT⟩ := atoms_runs hb bodyAtoms hv
  refine ⟨run,hT,?_⟩
  simp [applyAtoms,bodyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,hi,hm,value]

private structure Invariant (S : State) (M m k i : ℕ) (T : State) : Prop where
  bounded : T.Bounded M
  cols_eq : T.scalar .cols=m
  index_eq : T.scalar .index=i
  todo_eq : T.scalar .todo=k-i
  one_eq : T.scalar .one=1
  left_eq : T.array .left=S.array .left
  right_eq : T.array .right=S.array .right
  output_prefix : Prefix (value (S.array .left) (S.array .right) m) k i (T.array .output)

theorem loop_runs {n m k : ℕ} (a : Fin k → Fin n) (b : Fin k → Fin m)
    (S : State) (M : ℕ) (hb : S.Bounded M) (hm : S.scalar .cols=m)
    (hk : S.scalar .length=k) (hone : S.scalar .one=1)
    (ha : S.array .left=List.ofFn (fun j => (a j).val))
    (hb' : S.array .right=List.ofFn (fun j => (b j).val))
    (hlen : (S.array .output).length=k) (hroom : n*m≤M) :
    ∃t≤8*k+3,∃T,Runs (storageBound Reg Arr M)
      (countedLoop .index .todo .length .one body) S t T ∧ T.Bounded M ∧
      T.array .output=List.ofFn (fun i : Fin k => (finProdFinEquiv (a i,b i)).val) := by
  have hkM : k≤M := by simpa [hk] using hb.1 .length
  let I := Invariant S M m k
  have hcopy := hb.setScalar Reg.todo (show S.scalar .length≤M from hb.1 _)
  have hstart : I 0 ((S.setScalar .todo (S.scalar .length)).setScalar .index 0) := by
    refine ⟨hcopy.setScalar _ (by omega),?_,?_,?_,?_,rfl,rfl,hlen,by omega⟩
    · simp [hm]
    · simp
    · simp [hk]
    · simp [hone]
  have hcontrol : ∀i≤k,∀T,I i T → T.scalar .index=i ∧ T.scalar .todo=k-i ∧ T.scalar .one=1 ∧
      T.size≤storageBound Reg Arr M := by
    intro i hi T hT
    exact ⟨hT.index_eq,hT.todo_eq,hT.one_eq,Store.size_le_of_bounded hT.bounded⟩
  have hstep : ∀i<k,∀T,I i T → ∃t≤5,∃U,Runs (storageBound Reg Arr M) body T t U ∧
      U.scalar .index=i ∧ U.scalar .todo=k-i ∧ U.scalar .one=1 ∧
      (U.setScalar .index (i+1)).size≤storageBound Reg Arr M ∧ I (i+1) (advance .index .todo U) := by
    intro i hi T hT
    obtain ⟨run,hU,ho⟩ := body_runs a b T M ⟨i,hi⟩ hT.bounded hT.cols_eq hT.index_eq
      (hT.left_eq.trans ha) (hT.right_eq.trans hb') hT.output_prefix.1 hroom
    let U := applyAtoms bodyAtoms T
    have frame (r : Reg) (hr : r∈({.cols,.index,.todo,.one} : Finset Reg)) : U.scalar r=T.scalar r :=
      run.scalar_eq_of_not_mem r ((by decide : ∀r∈({.cols,.index,.todo,.one} : Finset Reg),r∉body.scalarWrites) r hr)
    have hui := (frame .index (by decide)).trans hT.index_eq
    have hut := (frame .todo (by decide)).trans hT.todo_eq
    have huone := (frame .one (by decide)).trans hT.one_eq
    have hmid := hU.setScalar Reg.index (show i+1≤M by omega)
    refine ⟨5,le_rfl,U,run,hui,hut,huone,Store.size_le_of_bounded hmid,?_⟩
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [advance,hui] using hmid.setScalar Reg.todo (show U.scalar .todo-1≤M by rw [hut]; omega)
    · simpa [advance] using (frame .cols (by decide)).trans hT.cols_eq
    · simp [advance,hui]
    · simp [advance,hut]; omega
    · simpa [advance] using huone
    · exact (run.array_eq_of_not_mem .left (by decide)).trans hT.left_eq
    · exact (run.array_eq_of_not_mem .right (by decide)).trans hT.right_eq
    · change Prefix _ k (i+1) (U.array .output)
      rw [ho,hT.left_eq,hT.right_eq]
      exact hT.output_prefix.write hi
  obtain ⟨t,ht,T,run,hT⟩ := countedLoop_runs (storageBound Reg Arr M)
    .index .todo .length .one body k 5 I S (Store.size_le_of_bounded hb)
    (Store.size_le_of_bounded hcopy) hstart hcontrol (by decide) (by decide) hstep
  refine ⟨t,by omega,T,run,hT.bounded,hT.output_prefix.complete.trans ?_⟩
  congr 1
  funext i
  simp [value,ha,hb',finProdFinEquiv,Nat.add_comm,Nat.mul_comm]

theorem build_runs {n m k : ℕ} (a : Fin k → Fin n) (b : Fin k → Fin m)
    (S : State) (M : ℕ) (hb : S.Bounded M) (hm : S.scalar .cols=m)
    (ha : S.array .left=List.ofFn (fun j => (a j).val))
    (hb' : S.array .right=List.ofFn (fun j => (b j).val)) (hroom : n*m≤M) (hM : 1≤M) :
    ∃t≤8*k+7,∃T,Runs (storageBound Reg Arr M) build S t T ∧ T.Bounded M ∧
      T.array .output=List.ofFn (fun i : Fin k => (finProdFinEquiv (a i,b i)).val) := by
  have hv : ValidAtoms M prelude S := by simp [prelude,ValidAtoms,Atom.Valid,Atom.SmallResult,hM]
  obtain ⟨pre,hU⟩ := atoms_runs hb prelude hv
  let U := applyAtoms prelude S
  obtain ⟨t,ht,T,run,hT,ho⟩ := loop_runs a b U M hU
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar,Store.setArray,hm])
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar,Store.setArray,ha])
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar,Store.setArray])
    (by simpa [U,applyAtoms,prelude,Atom.apply,Store.setScalar,Store.setArray] using ha)
    (by simpa [U,applyAtoms,prelude,Atom.apply,Store.setScalar,Store.setArray] using hb')
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar,Store.setArray,ha]) hroom
  exact ⟨4+t,by omega,T,.seq pre run,hT,ho⟩

end GroupWL.MachinePrograms.PairedGenerators
