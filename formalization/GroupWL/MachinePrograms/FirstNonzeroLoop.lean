import GroupWL.MachinePrograms.FirstNonzero

namespace GroupWL.MachinePrograms.FirstNonzero
open NatArrayLanguage
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

private def controls : Finset Reg := {.base,.length,.fallback,.one,.index,.todo}

theorem body_scalarFrame {B S T t} (h : Runs B body S t T) (r : Reg) (hr : r∈controls) :
    T.scalar r=S.scalar r :=
  h.scalar_eq_of_not_mem r ((by decide : ∀ r∈controls,r∉body.scalarWrites) r hr)

theorem body_arrayFrame {B S T t} (h : Runs B body S t T) : T.array .input=S.array .input :=
  h.array_eq_of_not_mem .input (by decide)

private structure ScanState (S : State) (M n base default i : ℕ) (T : State) : Prop where
  bounded : T.Bounded M
  base_eq : T.scalar .base=base
  one_eq : T.scalar .one=1
  index_eq : T.scalar .index=i
  todo_eq : T.scalar .todo=n-i
  input_eq : T.array .input=S.array .input
  found_eq : T.scalar .found=if (hit (S.array .input) base i).isSome then 1 else 0
  result_eq : T.scalar .result=(hit (S.array .input) base i).getD default

theorem loop_runs (S : State) (M n base default : ℕ)
    (hb : S.Bounded M) (hbase : S.scalar .base=base) (hn : S.scalar .length=n)
    (hone : S.scalar .one=1) (hfound : S.scalar .found=0) (hresult : S.scalar .result=default)
    (hinterval : base+n≤(S.array .input).length) (hM : 1≤M) :
    ∃ t≤9*n+3,∃ T,Runs (storageBound Reg Arr M) (countedLoop .index .todo .length .one body) S t T ∧
      T.Bounded M ∧ T.scalar .found=(if (hit (S.array .input) base n).isSome then 1 else 0) ∧
      T.scalar .result=(hit (S.array .input) base n).getD default := by
  have hnM : n≤M := by simpa [hn] using hb.1 Reg.length
  let I := ScanState S M n base default
  have hcopy := hb.setScalar Reg.todo (show S.scalar .length≤M from hb.1 .length)
  have hstart : I 0 ((S.setScalar .todo (S.scalar .length)).setScalar .index 0) := by
    refine ⟨hcopy.setScalar _ (by omega),?_,?_,?_,?_,?_,?_,?_⟩
    · simp [hbase]
    · simp [hone]
    · simp
    · simp [hn]
    · rfl
    · simp [hfound]
    · simp [hresult]
  have hcontrol : ∀ i≤n,∀ T,I i T →
      T.scalar .index=i ∧ T.scalar .todo=n-i ∧ T.scalar .one=1 ∧
        T.size≤storageBound Reg Arr M := by
    intro i hi T hT
    exact ⟨hT.index_eq,hT.todo_eq,hT.one_eq,Store.size_le_of_bounded hT.bounded⟩
  have hstep : ∀ i<n,∀ T,I i T →
      ∃ t≤6,∃ U,Runs (storageBound Reg Arr M) body T t U ∧
        U.scalar .index=i ∧ U.scalar .todo=n-i ∧ U.scalar .one=1 ∧
        (U.setScalar .index (i+1)).size≤storageBound Reg Arr M ∧
        I (i+1) (advance .index .todo U) := by
    intro i hi T hT
    obtain ⟨t,ht,U,run,hU,hf,hr⟩ := body_runs T M base i default hT.bounded hT.base_eq hT.index_eq
      (by rw [hT.input_eq]; omega) hM (by simpa [hT.input_eq] using hT.found_eq)
      (by simpa [hT.input_eq] using hT.result_eq)
    have frame (r : Reg) (hr : r∈controls) := body_scalarFrame run r hr
    have hix : U.scalar .index=i := (frame _ (by decide)).trans hT.index_eq
    have htodo : U.scalar .todo=n-i := (frame _ (by decide)).trans hT.todo_eq
    have h1 : U.scalar .one=1 := (frame _ (by decide)).trans hT.one_eq
    have hmid := hU.setScalar Reg.index (show i+1≤M by omega)
    refine ⟨t,ht,U,run,hix,htodo,h1,Store.size_le_of_bounded hmid,?_⟩
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [advance,hix] using hmid.setScalar Reg.todo (show U.scalar .todo-1≤M by rw [htodo]; omega)
    · simpa [advance] using (frame .base (by decide)).trans hT.base_eq
    · simpa [advance] using h1
    · simp [advance,hix]
    · simp [advance,htodo]; omega
    · exact (body_arrayFrame run).trans hT.input_eq
    · simpa [advance,hT.input_eq] using hf
    · simpa [advance,hT.input_eq] using hr
  obtain ⟨t,ht,T,run,hT⟩ := countedLoop_runs (storageBound Reg Arr M)
    .index .todo .length .one body n 6 I S
    (Store.size_le_of_bounded hb) (Store.size_le_of_bounded hcopy) hstart hcontrol
    (by decide) (by decide) hstep
  exact ⟨t,by omega,T,run,hT.bounded,hT.found_eq,hT.result_eq⟩

theorem search_runs (S : State) (M n base default : ℕ)
    (hb : S.Bounded M) (hbase : S.scalar .base=base) (hn : S.scalar .length=n)
    (hdefault : S.scalar .fallback=default) (hinterval : base+n≤(S.array .input).length) (hM : 1≤M) :
    ∃ t≤9*n+6,∃ T,Runs (storageBound Reg Arr M) search S t T ∧ T.Bounded M ∧
      T.scalar .found=(if (hit (S.array .input) base n).isSome then 1 else 0) ∧
      T.scalar .result=(hit (S.array .input) base n).getD default := by
  have hv : ValidAtoms M prelude S := by simp [prelude,ValidAtoms,Atom.Valid,Atom.SmallResult,hM]
  obtain ⟨pre,hU⟩ := atoms_runs hb prelude hv
  let U := applyAtoms prelude S
  obtain ⟨t,ht,T,run,hT,hf,hr⟩ := loop_runs U M n base default hU
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar,hbase])
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar,hn])
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar])
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar])
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar,hdefault]) hinterval hM
  exact ⟨3+t,by omega,T,.seq pre run,hT,hf,hr⟩

end GroupWL.MachinePrograms.FirstNonzero
