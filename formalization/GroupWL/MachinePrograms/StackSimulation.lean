import GroupWL.MachinePrograms.StackTape

/-! Exact tape step counts for each finite-stack instruction. -/
namespace GroupWL.MachinePrograms.Stacks

open Complexity

variable {K Q : Type*} [DecidableEq K] {a : ℕ}
variable (M : Machine K Q) (input output : K) (e : Work K ≃ Fin a)
variable (S : K → List Bool) (cells : ℤ → Symbol a) (h : Encodes e S cells)
include h

theorem push_steps (q q' : Q) (k : K) (b : Bool) (hq : M.instruction q = .push k b q') :
    (tapeProgram M input output e).run ⟨.inr (.normal q), -1, cells⟩ (2 * (S k).length + 3) =
      ⟨.inr (.normal q'), -1,
        Function.update cells ((S k).length : ℤ) (setColumn e (cells (S k).length) k (some b))⟩ := by
  let P := tapeProgram M input output e
  let n := (S k).length
  let cells' := Function.update cells (n : ℤ) (setColumn e (cells n) k (some b))
  have h0 : P.run ⟨.inr (.normal q), -1, cells⟩ 1 = ⟨.inr (.go q), 0, cells⟩ := by
    simp [P, Program.run, Program.tick, tapeProgram, tapeTransition, hq,
      Direction.offset, Function.update_eq_self]
  have hg : P.run ⟨.inr (.go q), 0, cells⟩ n = ⟨.inr (.go q), n, cells⟩ :=
    go_scan M input output e S cells h q k (by simp [hq, Instruction.stack])
  have hw : P.run ⟨.inr (.go q), n, cells⟩ 1 = ⟨.inr (.ret q'), (n : ℤ)-1, cells'⟩ := by
    simp [P, Program.run, Program.tick, tapeProgram, tapeTransition, hq,
      h.end_column k, Direction.offset, n, cells', sub_eq_add_neg]
  have hr : P.run ⟨.inr (.ret q'), (n : ℤ)-1, cells'⟩ (n+1) =
      ⟨.inr (.normal q'), -1, cells'⟩ :=
    return_scan M input output e _ _ (h.push k b) q' n
  have h01 : P.run ⟨.inr (.normal q), -1, cells⟩ (1+n) = ⟨.inr (.go q), n, cells⟩ := by
    rw [Program.run_add, h0, hg]
  have h02 : P.run ⟨.inr (.normal q), -1, cells⟩ (1+n+1) =
      ⟨.inr (.ret q'), (n : ℤ)-1, cells'⟩ := by
    rw [Program.run_add, h01, hw]
  change P.run _ (2*n+3) = _
  rw [show 2*n+3 = (1+n+1)+(n+1) by omega, Program.run_add, h02, hr]

theorem pop_nil_steps (q : Q) (k : K) (f : Option Bool → Q)
    (hq : M.instruction q = .pop k f) (hk : S k = []) :
    (tapeProgram M input output e).run ⟨.inr (.normal q), -1, cells⟩ 3 =
      ⟨.inr (.normal (f none)), -1, cells⟩ := by
  have hz : (decode e (cells 0)).2 k = none := by simpa [hk] using h.end_column k
  simp [Program.run, Program.tick, tapeProgram, tapeTransition, hq,
    hz, h.bottom, Direction.offset, Function.update_eq_self]

theorem pop_cons_steps (q : Q) (k : K) (f : Option Bool → Q) (b : Bool) (L : List Bool)
    (hq : M.instruction q = .pop k f) (hk : S k = b :: L) :
    (tapeProgram M input output e).run ⟨.inr (.normal q), -1, cells⟩ (2 * L.length + 5) =
      ⟨.inr (.normal (f (some b))), -1,
        Function.update cells (L.length : ℤ) (setColumn e (cells L.length) k none)⟩ := by
  let P := tapeProgram M input output e
  let n := L.length
  let cells' := Function.update cells (n : ℤ) (setColumn e (cells n) k none)
  have h0 : P.run ⟨.inr (.normal q), -1, cells⟩ 1 = ⟨.inr (.go q), 0, cells⟩ := by
    simp [P, Program.run, Program.tick, tapeProgram, tapeTransition, hq,
      Direction.offset, Function.update_eq_self]
  have hg : P.run ⟨.inr (.go q), 0, cells⟩ (n+1) = ⟨.inr (.go q), (n : ℤ)+1, cells⟩ := by
    simpa [hk, n] using go_scan M input output e S cells h q k (by simp [hq, Instruction.stack])
  have hend : (decode e (cells ((n : ℤ)+1))).2 k = none := by
    simpa [hk, n] using h.end_column k
  have hv : (decode e (cells n)).2 k = some b := by
    rw [h.2, hk, reverse_cons_get]
    simp [n]
  have hw : P.run ⟨.inr (.go q), (n : ℤ)+1, cells⟩ 1 =
      ⟨.inr (.access q), n, cells⟩ := by
    simp [P, Program.run, Program.tick, tapeProgram, tapeTransition, hq,
      hend, Direction.offset, Function.update_eq_self]
  have ha : P.run ⟨.inr (.access q), n, cells⟩ 1 =
      ⟨.inr (.ret (f (some b))), (n : ℤ)-1, cells'⟩ := by
    simp [P, Program.run, Program.tick, tapeProgram, tapeTransition, hq,
      hv, h.not_bottom n, Direction.offset, cells', sub_eq_add_neg]
  have hr : P.run ⟨.inr (.ret (f (some b))), (n : ℤ)-1, cells'⟩ (n+1) =
      ⟨.inr (.normal (f (some b))), -1, cells'⟩ :=
    return_scan M input output e _ _ (h.pop k b L hk) _ n
  have h01 : P.run ⟨.inr (.normal q), -1, cells⟩ (1+(n+1)) =
      ⟨.inr (.go q), (n : ℤ)+1, cells⟩ := by
    rw [Program.run_add, h0, hg]
  have h02 : P.run ⟨.inr (.normal q), -1, cells⟩ (1+(n+1)+1) =
      ⟨.inr (.access q), n, cells⟩ := by
    rw [Program.run_add, h01, hw]
  have h03 : P.run ⟨.inr (.normal q), -1, cells⟩ (1+(n+1)+1+1) =
      ⟨.inr (.ret (f (some b))), (n : ℤ)-1, cells'⟩ := by
    rw [Program.run_add, h02, ha]
  change P.run _ (2*n+5) = _
  rw [show 2*n+5 = (1+(n+1)+1+1)+(n+1) by omega, Program.run_add, h03, hr]

theorem peek_nil_steps (q : Q) (k : K) (f : Option Bool → Q)
    (hq : M.instruction q = .peek k f) (hk : S k = []) :
    (tapeProgram M input output e).run ⟨.inr (.normal q), -1, cells⟩ 3 =
      ⟨.inr (.normal (f none)), -1, cells⟩ := by
  have hz : (decode e (cells 0)).2 k = none := by simpa [hk] using h.end_column k
  simp [Program.run, Program.tick, tapeProgram, tapeTransition, hq,
    hz, h.bottom, Direction.offset, Function.update_eq_self]

theorem peek_cons_steps (q : Q) (k : K) (f : Option Bool → Q) (b : Bool) (L : List Bool)
    (hq : M.instruction q = .peek k f) (hk : S k = b :: L) :
    (tapeProgram M input output e).run ⟨.inr (.normal q), -1, cells⟩ (2 * L.length + 5) =
      ⟨.inr (.normal (f (some b))), -1, cells⟩ := by
  let P := tapeProgram M input output e
  let n := L.length
  have h0 : P.run ⟨.inr (.normal q), -1, cells⟩ 1 = ⟨.inr (.go q), 0, cells⟩ := by
    simp [P, Program.run, Program.tick, tapeProgram, tapeTransition, hq,
      Direction.offset, Function.update_eq_self]
  have hg : P.run ⟨.inr (.go q), 0, cells⟩ (n+1) = ⟨.inr (.go q), (n : ℤ)+1, cells⟩ := by
    simpa [hk, n] using go_scan M input output e S cells h q k (by simp [hq, Instruction.stack])
  have hend : (decode e (cells ((n : ℤ)+1))).2 k = none := by
    simpa [hk, n] using h.end_column k
  have hv : (decode e (cells n)).2 k = some b := by
    rw [h.2, hk, reverse_cons_get]
    simp [n]
  have hw : P.run ⟨.inr (.go q), (n : ℤ)+1, cells⟩ 1 =
      ⟨.inr (.access q), n, cells⟩ := by
    simp [P, Program.run, Program.tick, tapeProgram, tapeTransition, hq,
      hend, Direction.offset, Function.update_eq_self]
  have ha : P.run ⟨.inr (.access q), n, cells⟩ 1 =
      ⟨.inr (.ret (f (some b))), (n : ℤ)-1, cells⟩ := by
    simp [P, Program.run, Program.tick, tapeProgram, tapeTransition, hq,
      hv, h.not_bottom n, Direction.offset, Function.update_eq_self, sub_eq_add_neg]
  have hr := return_scan M input output e S cells h (f (some b)) n
  have h01 : P.run ⟨.inr (.normal q), -1, cells⟩ (1+(n+1)) =
      ⟨.inr (.go q), (n : ℤ)+1, cells⟩ := by
    rw [Program.run_add, h0, hg]
  have h02 : P.run ⟨.inr (.normal q), -1, cells⟩ (1+(n+1)+1) =
      ⟨.inr (.access q), n, cells⟩ := by
    rw [Program.run_add, h01, hw]
  have h03 : P.run ⟨.inr (.normal q), -1, cells⟩ (1+(n+1)+1+1) =
      ⟨.inr (.ret (f (some b))), (n : ℤ)-1, cells⟩ := by
    rw [Program.run_add, h02, ha]
  change P.run _ (2*n+5) = _
  rw [show 2*n+5 = (1+(n+1)+1+1)+(n+1) by omega, Program.run_add, h03, hr]

end GroupWL.MachinePrograms.Stacks
