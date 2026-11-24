import GroupWL.MachinePrograms.FiniteSetArrays
import GroupWL.MachinePrograms.NatArrayFrames
import GroupWL.MachinePrograms.NatArrayCountedLoops

/-! Materialize the initial subgroup mask from an explicit identity and
array of generator indices. Repeated generators are handled by array writes. -/
namespace GroupWL.MachinePrograms.GeneratorMask

open NatArrayLanguage FiniteSetArrays
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

inductive Reg where
  | order | identity | one | zero | length | index | todo | target
  deriving DecidableEq, Fintype
inductive Arr where
  | generators | output
  deriving DecidableEq, Fintype
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def bodyAtoms : List (Atom Reg Arr) := [
  .read .target .generators .index, .write .output .target .one]
def body : Code := atoms bodyAtoms
def prelude : List (Atom Reg Arr) := [
  .const .one 1,.const .zero 0,.arrayLength .length .generators,
  .allocate .output .order .zero,.write .output .identity .one]
def build : Code := .seq (atoms prelude) (countedLoop .index .todo .length .one body)

def prefixSet {n : ℕ} (identity : Fin n) (generators : List (Fin n)) (i : ℕ) : Finset (Fin n) :=
  insert identity (generators.take i).toFinset

theorem prefixSet_succ {n : ℕ} (e : Fin n) (gs : List (Fin n)) (i : ℕ) (hi : i<gs.length) :
    prefixSet e gs (i+1)=insert gs[i] (prefixSet e gs i) := by
  unfold prefixSet
  rw [List.take_succ_eq_append_getElem hi]
  simp only [List.toFinset_append,List.toFinset_cons,List.toFinset_nil,
    Finset.union_insert,Finset.union_empty,Finset.insert_comm]

theorem body_runs {n : ℕ} (S : State) (M : ℕ) (R : Finset (Fin n))
    (gs : List (Fin n)) (i : ℕ) (hi : i<gs.length)
    (hb : S.Bounded M) (hgs : S.array .generators=gs.map Fin.val)
    (hout : S.array .output=word R) (hindex : S.scalar .index=i) (hone : S.scalar .one=1) :
    Runs (storageBound Reg Arr M) body S 2 (applyAtoms bodyAtoms S) ∧
      (applyAtoms bodyAtoms S).Bounded M ∧
      (applyAtoms bodyAtoms S).array .output=word (insert gs[i] R) := by
  have hget : (S.array .generators)[i]?.getD 0=(gs[i]).val := by
    simp [hgs,List.getElem?_eq_getElem hi]
  have hv : ValidAtoms M bodyAtoms S := by
    simp [bodyAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,Store.setScalar,
      hindex,hgs,hi,hout,List.getElem?_eq_getElem hi,(gs[i]).isLt]
  obtain ⟨hr,hT⟩ := atoms_runs hb bodyAtoms hv
  exact ⟨hr,hT,by simp [applyAtoms,bodyAtoms,Atom.apply,Store.setScalar,Store.setArray,
    hindex,hget,hone,hout,word_insert]⟩

private structure ScanState {n : ℕ} (S : State) (M : ℕ) (e : Fin n) (gs : List (Fin n))
    (i : ℕ) (T : State) : Prop where
  bounded : T.Bounded M
  one_eq : T.scalar .one=1
  index_eq : T.scalar .index=i
  todo_eq : T.scalar .todo=gs.length-i
  generators_eq : T.array .generators=gs.map Fin.val
  output_eq : T.array .output=word (prefixSet e gs i)

theorem scan_runs {n : ℕ} (S : State) (M : ℕ) (e : Fin n) (gs : List (Fin n))
    (hb : S.Bounded M) (hgs : S.array .generators=gs.map Fin.val)
    (hout : S.array .output=word {e}) (hlen : S.scalar .length=gs.length)
    (hone : S.scalar .one=1) :
    ∃ t≤5*gs.length+3,∃ T,
      Runs (storageBound Reg Arr M) (countedLoop .index .todo .length .one body) S t T ∧
      T.Bounded M ∧ T.array .output=word (insert e gs.toFinset) := by
  have hlenM : gs.length≤M := by simpa [hgs] using hb.2.1 Arr.generators
  let I := ScanState S M e gs
  have hcopy := hb.setScalar Reg.todo (show S.scalar .length≤M by simpa [hlen] using hlenM)
  have hstart : I 0 ((S.setScalar .todo (S.scalar .length)).setScalar .index 0) := by
    refine ⟨hcopy.setScalar _ (by omega),?_,?_,?_,hgs,?_⟩
    · simp [hone]
    · simp
    · simp [hlen]
    · simpa [prefixSet] using hout
  have hcontrol : ∀ i≤gs.length,∀ T,I i T →
      T.scalar .index=i ∧ T.scalar .todo=gs.length-i ∧ T.scalar .one=1 ∧
        T.size≤storageBound Reg Arr M := by
    intro i hi T hT
    exact ⟨hT.index_eq,hT.todo_eq,hT.one_eq,Store.size_le_of_bounded hT.bounded⟩
  have hstep : ∀ i<gs.length,∀ T,I i T →
      ∃ t≤2,∃ U,Runs (storageBound Reg Arr M) body T t U ∧
        U.scalar .index=i ∧ U.scalar .todo=gs.length-i ∧ U.scalar .one=1 ∧
        (U.setScalar .index (i+1)).size≤storageBound Reg Arr M ∧
        I (i+1) (advance .index .todo U) := by
    intro i hi T hT
    obtain ⟨run,hU,ho⟩ := body_runs T M (prefixSet e gs i) gs i hi hT.bounded
      hT.generators_eq hT.output_eq hT.index_eq hT.one_eq
    let U := applyAtoms bodyAtoms T
    have frame (r : Reg) (hr : r≠.target) : U.scalar r=T.scalar r :=
      run.scalar_eq_of_not_mem r (by simpa [body,atoms,bodyAtoms,NatArrayLanguage.sequence,
        Program.scalarWrites,Atom.scalarWrites] using hr)
    have hix : U.scalar .index=i := (frame _ (by decide)).trans hT.index_eq
    have htodo : U.scalar .todo=gs.length-i := (frame _ (by decide)).trans hT.todo_eq
    have h1 : U.scalar .one=1 := (frame _ (by decide)).trans hT.one_eq
    have hmid := hU.setScalar Reg.index (show i+1≤M by omega)
    refine ⟨2,le_rfl,U,run,hix,htodo,h1,Store.size_le_of_bounded hmid,?_⟩
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · simpa [advance,hix] using hmid.setScalar Reg.todo (show U.scalar .todo-1≤M by rw [htodo]; omega)
    · simpa [advance] using h1
    · simp [advance,hix]
    · simp [advance,htodo]; omega
    · exact (run.array_eq_of_not_mem .generators (by decide)).trans hT.generators_eq
    · simpa only [prefixSet_succ e gs i hi] using ho
  obtain ⟨t,ht,T,run,hT⟩ := countedLoop_runs (storageBound Reg Arr M)
    .index .todo .length .one body gs.length 2 I S
    (Store.size_le_of_bounded hb) (Store.size_le_of_bounded hcopy) hstart hcontrol
    (by decide) (by decide) hstep
  exact ⟨t,by omega,T,run,hT.bounded,by simpa [prefixSet] using hT.output_eq⟩

theorem build_runs {n : ℕ} (S : State) (M : ℕ) (e : Fin n) (gs : List (Fin n))
    (hb : S.Bounded M) (hn : S.scalar .order=n) (he : S.scalar .identity=e.val)
    (hgs : S.array .generators=gs.map Fin.val) :
    ∃ t≤5*gs.length+8,∃ T,Runs (storageBound Reg Arr M) build S t T ∧
      T.Bounded M ∧ T.array .output=word (insert e gs.toFinset) := by
  have hnM : n≤M := by simpa [hn] using hb.1 Reg.order
  have hM : 1≤M := by have := e.isLt; omega
  have hv : ValidAtoms M prelude S := by
    simp [prelude,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,Store.setArray,hn,he,hM,e.isLt]
  obtain ⟨pre,hU⟩ := atoms_runs hb prelude hv
  let U := applyAtoms prelude S
  have hz : List.replicate n 0=word (∅ : Finset (Fin n)) := by simp [word,List.ofFn_const]
  have hout : U.array .output=word {e} := by
    simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar,Store.setArray,hn,he,hz,word_insert]
  obtain ⟨t,ht,T,run,hT,ho⟩ := scan_runs U M e gs hU
    (by simpa [U,applyAtoms,prelude,Atom.apply,Store.setScalar,Store.setArray] using hgs)
    hout (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar,Store.setArray,hgs])
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar,Store.setArray])
  exact ⟨5+t,by omega,T,.seq pre run,hT,ho⟩

end GroupWL.MachinePrograms.GeneratorMask
