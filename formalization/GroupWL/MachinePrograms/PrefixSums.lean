import GroupWL.MachinePrograms.FilterRanks

/-! The same prefix-scan program handles arbitrary natural entries when
its total sum is within the store bound. -/
namespace GroupWL.MachinePrograms.FilterRanks
open NatArrayLanguage

theorem count_mono (xs : List ℕ) : Monotone (count xs) := by
  apply monotone_nat_of_le_succ
  intro i
  exact Nat.le_add_right _ _

theorem cell_runs_total (S : State) (M i : ℕ) (bounded : S.Bounded M)
    (index : S.scalar .index=i) (valid : i<(S.array .flags).length)
    (length : (S.array .ranks).length=(S.array .flags).length)
    (value : S.scalar .count=count (S.array .flags) i)
    (total : count (S.array .flags) (S.array .flags).length≤M) :
    Runs (storageBound Reg Arr M) cell S 3 (applyAtoms cellAtoms S) ∧
      (applyAtoms cellAtoms S).Bounded M ∧
      (applyAtoms cellAtoms S).scalar .count=count (S.array .flags) (i+1) ∧
      (applyAtoms cellAtoms S).array .ranks=(S.array .ranks).set i (count (S.array .flags) i) := by
  have hc := (count_mono (S.array .flags) (show i+1≤(S.array .flags).length by omega)).trans total
  have ha : ValidAtoms M cellAtoms S := by
    simp [cellAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,Store.setArray,index,value,length]
    exact ⟨valid,by simpa only [count] using hc⟩
  obtain ⟨run,hT⟩ := atoms_runs bounded cellAtoms ha
  exact ⟨run,hT,by simp [applyAtoms,cellAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,index,value,count],
    by simp [applyAtoms,cellAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,index,value]⟩

theorem loop_runs_total (S : State) (M : ℕ) (bounded : S.Bounded M)
    (one : S.scalar .one=1) (length : S.scalar .length=(S.array .flags).length)
    (zero : S.scalar .count=0) (ranks : S.array .ranks=List.replicate (S.array .flags).length 0)
    (total : count (S.array .flags) (S.array .flags).length≤M) :
    ∃ t≤6*(S.array .flags).length+3,∃ T,
      Runs (storageBound Reg Arr M) (countedLoop .index .todo .length .one cell) S t T ∧ T.Bounded M ∧
      T.scalar .count=count (S.array .flags) (S.array .flags).length ∧
      T.array .ranks=List.ofFn (fun i : Fin (S.array .flags).length => count (S.array .flags) i) := by
  let S₀ := S.setScalar .todo (S.scalar .length)
  let S₁ := S₀.setScalar .index 0
  have h₀ : S₀.Bounded M := bounded.setScalar _ (bounded.1 .length)
  have h₁ : S₁.Bounded M := h₀.setScalar _ (Nat.zero_le _)
  have hstart : Invariant (S.array .flags) M 0 S₁ := by
    refine ⟨h₁,rfl,?_,?_,?_,?_,?_,?_⟩
    · simpa [S₁,S₀] using length
    · simpa [S₁,S₀] using one
    · simp [S₁]
    · simp [S₁,S₀,length]
    · simp [S₁,S₀,zero,count]
    · simpa [S₁,S₀,ranks] using ArrayTabulation.Prefix.zero (count (S.array .flags)) (S.array .flags).length
  have control : ∀ i≤(S.array .flags).length,∀ T,Invariant (S.array .flags) M i T →
      T.scalar .index=i ∧ T.scalar .todo=(S.array .flags).length-i ∧ T.scalar .one=1 ∧
      T.size≤storageBound Reg Arr M := by
    intro i hi T hT
    exact ⟨hT.index,hT.todo,hT.one,Store.size_le_of_bounded hT.bounded⟩
  have body : ∀ i<(S.array .flags).length,∀ T,Invariant (S.array .flags) M i T →
      ∃ t≤3,∃ U,Runs (storageBound Reg Arr M) cell T t U ∧
        U.scalar .index=i ∧ U.scalar .todo=(S.array .flags).length-i ∧ U.scalar .one=1 ∧
        (U.setScalar .index (i+1)).size≤storageBound Reg Arr M ∧
        Invariant (S.array .flags) M (i+1) (advance .index .todo U) := by
    intro i hi T hT
    obtain ⟨run,hU,hcount,hranks⟩ := cell_runs_total T M i hT.bounded hT.index
      (by rwa [hT.flags]) (by rw [hT.ranks.1,hT.flags])
      (by rw [hT.flags]; exact hT.count) (by rwa [hT.flags])
    rw [hT.flags] at hcount hranks
    let U := applyAtoms cellAtoms T
    have hx : U.scalar .index=i := (run.scalar_eq_of_not_mem .index (by decide)).trans hT.index
    have ht : U.scalar .todo=(S.array .flags).length-i := (run.scalar_eq_of_not_mem .todo (by decide)).trans hT.todo
    have ho : U.scalar .one=1 := (run.scalar_eq_of_not_mem .one (by decide)).trans hT.one
    have hiM : i+1≤M := le_trans (by omega) (bounded.2.1 .flags)
    have hmid := hU.setScalar Reg.index hiM
    have hfinal : (advance .index .todo U).Bounded M := by
      simpa only [advance,hx] using hmid.setScalar Reg.todo ((Nat.sub_le _ _).trans (hU.1 .todo))
    refine ⟨3,le_rfl,U,run,hx,ht,ho,Store.size_le_of_bounded hmid,hfinal,?_,?_,?_,?_,?_,?_,?_⟩
    · exact (run.array_eq_of_not_mem .flags (by decide)).trans hT.flags
    · simpa [advance,Store.setScalar] using (run.scalar_eq_of_not_mem .length (by decide)).trans hT.length
    · simpa [advance,Store.setScalar] using ho
    · simp [advance,hx]
    · simp [advance,ht,Nat.sub_sub]
    · simpa [advance,Store.setScalar] using hcount
    · change ArrayTabulation.Prefix _ _ _ (U.array .ranks)
      rw [hranks]; exact hT.ranks.write hi
  obtain ⟨t,ht,T,run,hT⟩ := countedLoop_runs (storageBound Reg Arr M)
    Reg.index Reg.todo Reg.length Reg.one cell (S.array .flags).length 3
    (Invariant (S.array .flags) M) S (Store.size_le_of_bounded bounded)
    (Store.size_le_of_bounded h₀) hstart control (by decide) (by decide) body
  exact ⟨t,by nlinarith,T,run,hT.bounded,hT.count,hT.ranks.complete⟩

theorem program_runs_total (S : State) (M : ℕ) (bounded : S.Bounded M) (one : 1≤M)
    (total : count (S.array .flags) (S.array .flags).length≤M) :
    ∃ t≤6*(S.array .flags).length+8,∃ T,
      Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧
      T.scalar .count=count (S.array .flags) (S.array .flags).length ∧
      T.array .ranks=List.ofFn (fun i : Fin (S.array .flags).length => count (S.array .flags) i) := by
  let pre : List (Atom Reg Arr) := [.const .one 1,.const .zero 0,.arrayLength .length .flags,
    .allocate .ranks .length .zero,.const .count 0]
  have valid : ValidAtoms M pre S := by simp [pre,ValidAtoms,Atom.Valid,Atom.SmallResult,one]
  obtain ⟨preRun,hU⟩ := atoms_runs bounded pre valid
  let U := applyAtoms pre S
  have hu : U.array .flags=S.array .flags := rfl
  obtain ⟨t,ht,T,run,hT,hc,hr⟩ := loop_runs_total U M hU
    (by simp [U,pre,applyAtoms,Atom.apply,Store.setScalar,Store.setArray])
    (by simp [U,pre,applyAtoms,Atom.apply,Store.setScalar,Store.setArray])
    (by simp [U,pre,applyAtoms,Atom.apply,Store.setScalar,Store.setArray])
    (by simp [U,pre,applyAtoms,Atom.apply,Store.setScalar,Store.setArray]) (by rwa [hu])
  rw [hu] at ht hc hr
  exact ⟨5+t,by omega,T,.seq preRun run,hT,hc,hr⟩

end GroupWL.MachinePrograms.FilterRanks
