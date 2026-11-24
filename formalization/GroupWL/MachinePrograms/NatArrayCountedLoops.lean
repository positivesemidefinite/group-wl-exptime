import GroupWL.MachinePrograms.NatArrayLoops

/-! Invariant-based rules for finite executions of the array language. The
invariant occurs only in proofs; executable loops retain fixed finite syntax. -/
namespace GroupWL.MachinePrograms.NatArrayLanguage

variable {Reg Arr : Type*} [DecidableEq Reg] [DecidableEq Arr]
  [Fintype Reg] [Fintype Arr]

theorem while_runs_invariant (bound : ℕ) (flag : Reg) (body : Program Reg Arr)
    (I : ℕ → Store Reg Arr → Prop) (n c : ℕ)
    (step : ∀ i < n, ∀ S, I i S →
      ∃ t ≤ c, ∃ T, Runs bound body S t T ∧ I (i+1) T)
    (active : ∀ i < n, ∀ S, I i S → S.scalar flag ≠ 0)
    (done : ∀ S, I n S → S.scalar flag = 0 ∧ S.size ≤ bound)
    (S : Store Reg Arr) (start : I 0 S) :
    ∃ t ≤ n*(c+1)+1, ∃ T, Runs bound (.while flag body) S t T ∧ I n T := by
  induction n generalizing I S with
  | zero =>
      exact ⟨1, by omega, S, .while_zero (done S start).1 (done S start).2, start⟩
  | succ n ih =>
      obtain ⟨t, ht, T, run, hT⟩ := step 0 (by omega) S start
      obtain ⟨u, hu, U, rest, hU⟩ := ih (fun i => I (i+1))
        (fun i hi => step (i+1) (by omega))
        (fun i hi => active (i+1) (by omega)) done T hT
      exact ⟨t+u+1, by nlinarith,
        U, .while_nonzero (active 0 (by omega) S start) run rest, hU⟩

def countedLoop (index remaining limit one : Reg) (body : Program Reg Arr) :
    Program Reg Arr := sequence [
  .atom (.copy remaining limit), .atom (.const index 0),
  .while remaining (sequence [body,
    .atom (.binary .add index index one),
    .atom (.binary .sub remaining remaining one)])]

def advance (index remaining : Reg) (S : Store Reg Arr) : Store Reg Arr :=
  (S.setScalar index (S.scalar index+1)).setScalar remaining (S.scalar remaining-1)

theorem countedLoop_runs (bound : ℕ) (index remaining limit one : Reg)
    (body : Program Reg Arr) (n c : ℕ) (I : ℕ → Store Reg Arr → Prop)
    (S : Store Reg Arr)
    (initialBound : S.size ≤ bound)
    (copyBound : (S.setScalar remaining (S.scalar limit)).size ≤ bound)
    (start : I 0 ((S.setScalar remaining (S.scalar limit)).setScalar index 0))
    (control : ∀ i ≤ n, ∀ T, I i T →
      T.scalar index = i ∧ T.scalar remaining = n-i ∧ T.scalar one = 1 ∧ T.size ≤ bound)
    (distinct : index ≠ remaining)
    (different : one ≠ index)
    (step : ∀ i < n, ∀ T, I i T →
      ∃ t ≤ c, ∃ U, Runs bound body T t U ∧
        U.scalar index = i ∧ U.scalar remaining = n-i ∧ U.scalar one = 1 ∧
        (U.setScalar index (i+1)).size ≤ bound ∧
        I (i+1) (advance index remaining U)) :
    ∃ t ≤ n*(c+3)+3, ∃ T, Runs bound (countedLoop index remaining limit one body) S t T ∧ I n T := by
  let S₀ := S.setScalar remaining (S.scalar limit)
  let S₁ := S₀.setScalar index 0
  have hs₁ : S₁.size ≤ bound := (control 0 (by omega) S₁ start).2.2.2
  have hstep : ∀ i < n, ∀ T, I i T →
      ∃ t ≤ c+2, ∃ U, Runs bound (sequence [body,
        .atom (.binary .add index index one),
        .atom (.binary .sub remaining remaining one)]) T t U ∧ I (i+1) U := by
    intro i hi T hT
    obtain ⟨t, ht, U, run, hix, hrem, hone, hmid, hnext⟩ := step i hi T hT
    have hb := (control (i+1) (by omega) _ hnext).2.2.2
    have hadd : (Atom.binary BinaryOp.add index index one).apply U = U.setScalar index (i+1) := by
      simp [Atom.apply, BinaryOp.eval, hix, hone]
    have hsub : (Atom.binary BinaryOp.sub remaining remaining one).apply (U.setScalar index (i+1)) =
        advance index remaining U := by
      simp [Atom.apply, BinaryOp.eval, Store.setScalar, advance, hix, hone,
        Ne.symm distinct, different]
    have ra : Runs bound (.atom (.binary .add index index one)) U 1 (U.setScalar index (i+1)) := by
      rw [← hadd]
      exact .atom trivial run.end_bound (by rwa [hadd])
    have rs : Runs bound (.atom (.binary .sub remaining remaining one))
        (U.setScalar index (i+1)) 1 (advance index remaining U) := by
      rw [← hsub]
      exact .atom trivial hmid (by rwa [hsub])
    refine ⟨t+(1+(1+0)), by omega, advance index remaining U, ?_, hnext⟩
    exact .seq run (.seq ra (.seq rs (.skip hb)))
  obtain ⟨t, ht, T, run, hT⟩ := while_runs_invariant bound remaining _ I n (c+2)
    hstep (fun i hi U hU => by have := (control i (by omega) U hU).2.1; omega)
    (fun U hU => ⟨by have := (control n le_rfl U hU).2.1; omega,
      (control n le_rfl U hU).2.2.2⟩) S₁ start
  refine ⟨1+(1+(t+0)), by nlinarith, T, ?_, hT⟩
  exact .seq (.atom trivial initialBound copyBound)
    (.seq (.atom trivial copyBound hs₁) (.seq run (.skip run.end_bound)))

end GroupWL.MachinePrograms.NatArrayLanguage
