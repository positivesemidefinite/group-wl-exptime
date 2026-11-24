import GroupWL.MachinePrograms.FiniteSetArrays
import GroupWL.MachinePrograms.NatArrayCountedLoops
import GroupWL.MachinePrograms.NatArrayFrames

/-! A complete linear scan of a Boolean characteristic array. -/
namespace GroupWL.MachinePrograms.MaskAll
open NatArrayLanguage FiniteSetArrays
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

inductive Reg where
  | length | one | index | todo | flag | result
  deriving DecidableEq,Fintype
inductive Arr where
  | input
  deriving DecidableEq,Fintype
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def bodyAtoms : List (Atom Reg Arr) := [.read .flag .input .index,.binary .mul .result .result .flag]
def body : Code := atoms bodyAtoms
def prelude : List (Atom Reg Arr) := [.const .one 1,.const .result 1,.arrayLength .length .input]
def check : Code := .seq (atoms prelude) (countedLoop .index .todo .length .one body)

def prefixAll {n : ℕ} (C : Finset (Fin n)) (i : ℕ) : Prop := ∀ j : Fin n, j.val < i → j ∈ C
instance {n : ℕ} (C : Finset (Fin n)) (i : ℕ) : Decidable (prefixAll C i) := inferInstanceAs (Decidable (∀ j : Fin n, j.val < i → j ∈ C))

theorem prefixAll_succ {n : ℕ} (C : Finset (Fin n)) (i : Fin n) :
    prefixAll C (i.val+1) ↔ prefixAll C i.val ∧ i∈C := by
  constructor
  · intro h; exact ⟨fun j hj => h j (by omega),h i (by omega)⟩
  · rintro ⟨h,hi⟩ j hj
    by_cases he : j.val=i.val
    · exact (Fin.ext he).symm ▸ hi
    · exact h j (by omega)

theorem body_runs {n : ℕ} (S : State) (M : ℕ) (C : Finset (Fin n)) (i : Fin n)
    (hb : S.Bounded M) (hi : S.scalar .index=i.val) (hinput : S.array .input=word C)
    (hresult : S.scalar .result≤1) (hM : 1≤M) :
    Runs (storageBound Reg Arr M) body S 2 (applyAtoms bodyAtoms S) ∧
      (applyAtoms bodyAtoms S).Bounded M ∧
      (applyAtoms bodyAtoms S).scalar .result=S.scalar .result*(if i∈C then 1 else 0) := by
  have hread : (S.array .input)[i.val]?.getD 0=if i∈C then 1 else 0 := by rw [hinput,read_word]
  have hv : ValidAtoms M bodyAtoms S := by
    simp [bodyAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,hi,hread,hinput,word]
    split_ifs <;> omega
  obtain ⟨run,hT⟩ := atoms_runs hb bodyAtoms hv
  refine ⟨run,hT,?_⟩
  simp [applyAtoms,bodyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,hi,hread]

private structure Invariant {n : ℕ} (C : Finset (Fin n)) (M i : ℕ) (S : State) : Prop where
  bounded : S.Bounded M
  index_eq : S.scalar .index=i
  todo_eq : S.scalar .todo=n-i
  one_eq : S.scalar .one=1
  input_eq : S.array .input=word C
  result_eq : S.scalar .result=if prefixAll C i then 1 else 0

theorem loop_runs {n : ℕ} (S : State) (M : ℕ) (C : Finset (Fin n))
    (hb : S.Bounded M) (hlen : S.scalar .length=n) (hone : S.scalar .one=1)
    (hresult : S.scalar .result=1) (hinput : S.array .input=word C) (hM : 1≤M) :
    ∃ t≤5*n+3,∃ T,Runs (storageBound Reg Arr M)
      (countedLoop .index .todo .length .one body) S t T ∧ T.Bounded M ∧
      T.scalar .result=if prefixAll C n then 1 else 0 := by
  have hnM : n≤M := by simpa [hlen] using hb.1 .length
  let I := Invariant C M
  have hcopy := hb.setScalar Reg.todo (show S.scalar .length≤M from hb.1 _)
  have hstart : I 0 ((S.setScalar .todo (S.scalar .length)).setScalar .index 0) := by
    refine ⟨hcopy.setScalar _ (by omega),?_,?_,?_,?_,?_⟩
    · simp
    · simp [hlen]
    · simp [hone]
    · exact hinput
    · simp [hresult,prefixAll]
  have hcontrol : ∀i≤n,∀T,I i T → T.scalar .index=i ∧ T.scalar .todo=n-i ∧ T.scalar .one=1 ∧
      T.size≤storageBound Reg Arr M := by
    intro i hi T hT; exact ⟨hT.index_eq,hT.todo_eq,hT.one_eq,Store.size_le_of_bounded hT.bounded⟩
  have hstep : ∀i<n,∀T,I i T → ∃t≤2,∃U,Runs (storageBound Reg Arr M) body T t U ∧
      U.scalar .index=i ∧ U.scalar .todo=n-i ∧ U.scalar .one=1 ∧
      (U.setScalar .index (i+1)).size≤storageBound Reg Arr M ∧ I (i+1) (advance .index .todo U) := by
    intro i hi T hT
    obtain ⟨run,hU,ho⟩ := body_runs T M C ⟨i,hi⟩ hT.bounded hT.index_eq hT.input_eq
      (by rw [hT.result_eq]; split_ifs <;> omega) hM
    let U := applyAtoms bodyAtoms T
    have frame (r : Reg) (hr : r∈({.index,.todo,.one} : Finset Reg)) : U.scalar r=T.scalar r :=
      run.scalar_eq_of_not_mem r ((by decide : ∀r∈({.index,.todo,.one} : Finset Reg),r∉body.scalarWrites) r hr)
    have hui := (frame .index (by decide)).trans hT.index_eq
    have hut := (frame .todo (by decide)).trans hT.todo_eq
    have huone := (frame .one (by decide)).trans hT.one_eq
    have hmid := hU.setScalar Reg.index (show i+1≤M by omega)
    refine ⟨2,le_rfl,U,run,hui,hut,huone,Store.size_le_of_bounded hmid,?_⟩
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · simpa [advance,hui] using hmid.setScalar Reg.todo (show U.scalar .todo-1≤M by rw [hut]; omega)
    · simp [advance,hui]
    · simp [advance,hut]; omega
    · simpa [advance] using huone
    · exact hT.input_eq
    · change U.scalar .result=_
      rw [ho,hT.result_eq]
      simp only [prefixAll_succ C (⟨i,hi⟩ : Fin n)]
      by_cases hp : prefixAll C i <;> by_cases hm : (⟨i,hi⟩ : Fin n)∈C <;> simp [hp,hm]
  obtain ⟨t,ht,T,run,hT⟩ := countedLoop_runs (storageBound Reg Arr M)
    .index .todo .length .one body n 2 I S (Store.size_le_of_bounded hb)
    (Store.size_le_of_bounded hcopy) hstart hcontrol (by decide) (by decide) hstep
  exact ⟨t,by omega,T,run,hT.bounded,hT.result_eq⟩

theorem check_runs {n : ℕ} (S : State) (M : ℕ) (C : Finset (Fin n))
    (hb : S.Bounded M) (hinput : S.array .input=word C) (hM : 1≤M) :
    ∃t≤5*n+6,∃T,Runs (storageBound Reg Arr M) check S t T ∧ T.Bounded M ∧
      (T.scalar .result=1 ↔ C=Finset.univ) := by
  have hv : ValidAtoms M prelude S := by
    simp [prelude,ValidAtoms,Atom.Valid,Atom.SmallResult,hM]
  obtain ⟨pre,hU⟩ := atoms_runs hb prelude hv
  let U := applyAtoms prelude S
  obtain ⟨t,ht,T,run,hT,ho⟩ := loop_runs U M C hU
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar,hinput])
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar])
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar]) hinput hM
  refine ⟨3+t,by omega,T,.seq pre run,hT,?_⟩
  rw [ho]
  have hc : prefixAll C n ↔ C=Finset.univ := by
    constructor
    · intro h; exact Finset.eq_univ_of_forall (fun j => h j j.isLt)
    · intro h j hj; simp [h]
  simpa using hc

end GroupWL.MachinePrograms.MaskAll
