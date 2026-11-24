import GroupWL.MachinePrograms.NatArrayCountedLoops
import GroupWL.MachinePrograms.NatArrayProofs
import GroupWL.MachinePrograms.NatArrayFrames

/-! A concrete linear scan for the first nonzero matrix-row coefficient. -/
namespace GroupWL.MachinePrograms.PivotSearch

open NatArrayLanguage

inductive Reg where
  | width | pivot | found | index | todo | one | value
  deriving DecidableEq,Fintype
inductive Arr where
  | row
  deriving DecidableEq,Fintype
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def first (xs : List ℕ) : ℕ → Option ℕ
  | 0 => none
  | i+1 => match first xs i with
    | some j => some j
    | none => if xs[i]?.getD 0=0 then none else some i

def flag (x : Option ℕ) : ℕ := if x.isSome then 1 else 0

def step : Code := .branch .found .skip
  (.seq (.atom (.read .value .row .index))
    (.branch .value (atoms [.copy .pivot .index,.const .found 1]) .skip))

def program : Code := .seq (atoms [
  .const .one 1,.const .found 0,.arrayLength .width .row,.copy .pivot .width])
  (countedLoop .index .todo .width .one step)

theorem step_runs (S : State) (M i : ℕ) (bounded : S.Bounded M) (one : 1≤M)
    (index : S.scalar .index=i) (valid : i<(S.array .row).length)
    (found : S.scalar .found=flag (first (S.array .row) i))
    (pivot : S.scalar .pivot=(first (S.array .row) i).getD (S.array .row).length) :
    ∃ t≤5,∃ T,Runs (storageBound Reg Arr M) step S t T ∧ T.Bounded M ∧
      T.scalar .found=flag (first (S.array .row) (i+1)) ∧
      T.scalar .pivot=(first (S.array .row) (i+1)).getD (S.array .row).length := by
  cases hx : first (S.array .row) i with
  | some j =>
      refine ⟨1,by omega,S,.branch_nonzero ?_ (.skip (Store.size_le_of_bounded bounded)),bounded,?_,?_⟩
      · simp only [hx,flag,Option.isSome_some,if_true] at found; omega
      · simpa only [first,hx] using found
      · simpa only [first,hx] using pivot
  | none =>
      have hf : S.scalar .found=0 := by simpa [hx,flag] using found
      have hp : S.scalar .pivot=(S.array .row).length := by simpa [hx] using pivot
      let a : Atom Reg Arr := .read .value .row .index
      let U := a.apply S
      have hb : U.Bounded M := a.apply_bounded bounded trivial
      have hr := atom_runs bounded a (by change S.scalar .index<(S.array .row).length; rwa [index]) trivial
      have hv : U.scalar .value=(S.array .row)[i]?.getD 0 := by simp [U,a,Atom.apply,index]
      by_cases hz : (S.array .row)[i]?.getD 0=0
      · refine ⟨3,by omega,U,.branch_zero hf (.seq hr (.branch_zero ?_ (.skip (Store.size_le_of_bounded hb)))),hb,?_,?_⟩
        · exact hv.trans hz
        · simp [U,a,Atom.apply,first,hx,hz,flag,hf]
        · simp [U,a,Atom.apply,first,hx,hz,hp]
      · let instructions : List (Atom Reg Arr) := [.copy .pivot .index,.const .found 1]
        have ha : ValidAtoms M instructions U := by simp [instructions,ValidAtoms,Atom.Valid,Atom.SmallResult,one]
        obtain ⟨last,hT⟩ := atoms_runs hb instructions ha
        let T := applyAtoms instructions U
        refine ⟨5,by omega,T,.branch_zero hf (.seq hr (.branch_nonzero ?_ last)),hT,?_,?_⟩
        · rw [hv]; exact hz
        · simp [T,applyAtoms,instructions,Atom.apply,first,hx,hz,flag]
        · simp [T,applyAtoms,instructions,U,a,Atom.apply,first,hx,hz,index,Store.setScalar]

structure Invariant (xs : List ℕ) (M i : ℕ) (S : State) : Prop where
  bounded : S.Bounded M
  row : S.array .row=xs
  width : S.scalar .width=xs.length
  one : S.scalar .one=1
  index : S.scalar .index=i
  todo : S.scalar .todo=xs.length-i
  found : S.scalar .found=flag (first xs i)
  pivot : S.scalar .pivot=(first xs i).getD xs.length

theorem loop_runs (S : State) (M : ℕ) (bounded : S.Bounded M) (one : S.scalar .one=1)
    (width : S.scalar .width=(S.array .row).length) (found : S.scalar .found=0)
    (pivot : S.scalar .pivot=(S.array .row).length) :
    ∃ t≤8*(S.array .row).length+3,∃ T,
      Runs (storageBound Reg Arr M) (countedLoop .index .todo .width .one step) S t T ∧
      T.Bounded M ∧ T.scalar .found=flag (first (S.array .row) (S.array .row).length) ∧
      T.scalar .pivot=(first (S.array .row) (S.array .row).length).getD (S.array .row).length := by
  let S₀ := S.setScalar .todo (S.scalar .width)
  let S₁ := S₀.setScalar .index 0
  have h₀ : S₀.Bounded M := bounded.setScalar _ (bounded.1 .width)
  have h₁ : S₁.Bounded M := h₀.setScalar _ (Nat.zero_le _)
  have hstart : Invariant (S.array .row) M 0 S₁ := by
    refine ⟨h₁,rfl,?_,?_,?_,?_,?_,?_⟩ <;> simp [S₁,S₀,width,one,found,pivot,first,flag]
  have control : ∀ i≤(S.array .row).length,∀ T,Invariant (S.array .row) M i T →
      T.scalar .index=i ∧ T.scalar .todo=(S.array .row).length-i ∧ T.scalar .one=1 ∧
      T.size≤storageBound Reg Arr M := by
    intro i hi T hT
    exact ⟨hT.index,hT.todo,hT.one,Store.size_le_of_bounded hT.bounded⟩
  have body : ∀ i<(S.array .row).length,∀ T,Invariant (S.array .row) M i T →
      ∃ t≤5,∃ U,Runs (storageBound Reg Arr M) step T t U ∧
        U.scalar .index=i ∧ U.scalar .todo=(S.array .row).length-i ∧ U.scalar .one=1 ∧
        (U.setScalar .index (i+1)).size≤storageBound Reg Arr M ∧
        Invariant (S.array .row) M (i+1) (advance .index .todo U) := by
    intro i hi T hT
    obtain ⟨t,ht,U,run,hU,hf,hp⟩ := step_runs T M i hT.bounded
      (by have := bounded.1 Reg.one; omega) hT.index (by simpa [hT.row] using hi)
      (by simpa [hT.row] using hT.found) (by simpa [hT.row] using hT.pivot)
    rw [hT.row] at hf hp
    have hix : U.scalar .index=i := (run.scalar_eq_of_not_mem .index (by decide)).trans hT.index
    have htodo : U.scalar .todo=(S.array .row).length-i :=
      (run.scalar_eq_of_not_mem .todo (by decide)).trans hT.todo
    have hone : U.scalar .one=1 := (run.scalar_eq_of_not_mem .one (by decide)).trans hT.one
    have hwidth : U.scalar .width=(S.array .row).length :=
      (run.scalar_eq_of_not_mem .width (by decide)).trans hT.width
    have hrow : U.array .row=S.array .row := (run.array_eq_of_not_mem .row (by decide)).trans hT.row
    have hiM : i+1≤M := le_trans (by omega) (bounded.2.1 .row)
    have hm := hU.setScalar Reg.index hiM
    have hb : (advance .index .todo U).Bounded M := by
      simpa only [advance,hix] using hm.setScalar Reg.todo ((Nat.sub_le _ _).trans (hU.1 .todo))
    refine ⟨t,ht,U,run,hix,htodo,hone,Store.size_le_of_bounded hm,
      hb,?_,?_,?_,?_,?_,?_,?_⟩ <;>
      simp [advance,Store.setScalar,hrow,hwidth,hone,hix,htodo,Nat.sub_sub,hf,hp]
  obtain ⟨t,ht,T,run,hT⟩ := countedLoop_runs (storageBound Reg Arr M)
    Reg.index Reg.todo Reg.width Reg.one step (S.array .row).length 5
    (Invariant (S.array .row) M) S (Store.size_le_of_bounded bounded)
    (Store.size_le_of_bounded h₀) hstart control (by decide) (by decide) body
  exact ⟨t,by nlinarith,T,run,hT.bounded,hT.found,hT.pivot⟩

theorem program_runs (S : State) (M : ℕ) (bounded : S.Bounded M) (one : 1≤M) :
    ∃ t≤8*(S.array .row).length+7,∃ T,
      Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧
      T.scalar .found=flag (first (S.array .row) (S.array .row).length) ∧
      T.scalar .pivot=(first (S.array .row) (S.array .row).length).getD (S.array .row).length := by
  let instructions : List (Atom Reg Arr) := [
    .const .one 1,.const .found 0,.arrayLength .width .row,.copy .pivot .width]
  have valid : ValidAtoms M instructions S := by
    simp [instructions,ValidAtoms,Atom.Valid,Atom.SmallResult,one]
  obtain ⟨pre,hU⟩ := atoms_runs bounded instructions valid
  let U := applyAtoms instructions S
  have hu : U.array .row=S.array .row := rfl
  obtain ⟨t,ht,T,run,hT,hf,hp⟩ := loop_runs U M hU
    (by simp [U,instructions,applyAtoms,Atom.apply,Store.setScalar])
    (by simp [U,instructions,applyAtoms,Atom.apply,Store.setScalar])
    (by simp [U,instructions,applyAtoms,Atom.apply,Store.setScalar])
    (by simp [U,instructions,applyAtoms,Atom.apply,Store.setScalar])
  rw [hu] at ht hf hp
  exact ⟨4+t,by omega,T,.seq pre run,hT,hf,hp⟩

theorem first_none_iff (xs : List ℕ) (i : ℕ) :
    first xs i=none ↔ ∀ j < i, xs[j]?.getD 0=0 := by
  induction i with
  | zero => simp [first]
  | succ i ih =>
      cases h : first xs i with
      | none =>
          have hz := ih.mp h
          simp only [first,h,ite_eq_left_iff,Option.some_ne_none,imp_false,not_not]
          constructor
          · intro hi j hj
            by_cases he : j=i
            · simpa [he] using hi
            · exact hz j (by omega)
          · intro h'; exact h' i (by omega)
      | some j =>
          simp only [first,h,Option.some_ne_none,false_iff]
          intro hz
          have := ih.mpr (fun k hk => hz k (by omega))
          rw [h] at this
          contradiction

theorem first_some (xs : List ℕ) (i j : ℕ) (h : first xs i=some j) :
    j < i ∧ xs[j]?.getD 0 ≠ 0 := by
  induction i with
  | zero => simp [first] at h
  | succ i ih =>
      cases hprev : first xs i with
      | some k =>
          have hj : k=j := by simpa [first,hprev] using h
          subst k
          obtain ⟨hlt,hne⟩ := ih hprev
          exact ⟨by omega,hne⟩
      | none =>
          simp only [first,hprev] at h
          split_ifs at h with hz
          have hj : i=j := Option.some.inj h
          subst j
          exact ⟨by omega,hz⟩

end GroupWL.MachinePrograms.PivotSearch
