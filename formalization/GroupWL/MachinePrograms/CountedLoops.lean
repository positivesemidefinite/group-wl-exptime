import GroupWL.MachinePrograms.Structured
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! Exact costs of finite loop traces, for executable fixed-body loops. -/
namespace GroupWL.MachinePrograms.Structured

variable {K : Type*} [DecidableEq K]

/-- A fixed structured loop follows the displayed finite trace. The trace is
proof data: the generated program contains only the finite top-symbol test and
the fixed body. Every guard is counted. -/
theorem while_runs_of_trace (counter : K) (test : Option Bool → Bool) (body : Program K)
    (n : ℕ) (states : ℕ → Store K) (cost : ℕ → ℕ)
    (hgo : ∀ i < n, test ((states i counter).head?) = true)
    (hdone : test ((states n counter).head?) = false)
    (hstep : ∀ i < n, Runs body (states i) (cost i) (states (i+1))) :
    Runs (.while counter test body) (states 0)
      ((Finset.range n).sum cost+n+1) (states n) := by
  induction n generalizing states cost with
  | zero => simpa using Runs.while_false hdone
  | succ n ih =>
    have ht := ih (fun i => states (i+1)) (fun i => cost (i+1))
      (fun i hi => hgo (i+1) (by omega)) hdone
      (fun i hi => hstep (i+1) (by omega))
    have hr := Runs.while_true (hgo 0 (by omega)) (hstep 0 (by omega)) ht
    have hsum : (Finset.range (n+1)).sum cost =
        (Finset.range n).sum (fun i => cost (i+1))+cost 0 := Finset.sum_range_succ' cost n
    convert hr using 1
    simp only [hsum]
    omega

theorem unary_while_runs_of_trace (counter : K) (body : Program K)
    (n : ℕ) (states : ℕ → Store K) (cost : ℕ → ℕ)
    (hcounter : ∀ i ≤ n, states i counter = List.replicate (n-i) true)
    (hstep : ∀ i < n, Runs body (states i) (cost i) (states (i+1))) :
    Runs (.while counter Option.isSome body) (states 0)
      ((Finset.range n).sum cost+n+1) (states n) := by
  apply while_runs_of_trace counter Option.isSome body n states cost ?_ ?_ hstep
  · intro i hi
    rw [hcounter i hi.le]
    have hn : n-i = (n-i-1)+1 := by omega
    rw [hn,List.replicate_succ]
    rfl
  · rw [hcounter n le_rfl]
    simp

theorem while_runs_bound (counter : K) (test : Option Bool → Bool) (body : Program K)
    (n B : ℕ) (states : ℕ → Store K) (cost : ℕ → ℕ)
    (hgo : ∀ i < n, test ((states i counter).head?) = true)
    (hdone : test ((states n counter).head?) = false)
    (hstep : ∀ i < n, Runs body (states i) (cost i) (states (i+1)))
    (hcost : ∀ i < n, cost i ≤ B) :
    ∃ time ≤ n*(B+1)+1, Runs (.while counter test body) (states 0) time (states n) := by
  refine ⟨(Finset.range n).sum cost+n+1,?_,while_runs_of_trace counter test body n states cost hgo hdone hstep⟩
  have hsum : (Finset.range n).sum cost ≤ n*B := by
    calc
      _ ≤ (Finset.range n).sum (fun _ => B) := Finset.sum_le_sum (fun i hi => hcost i (Finset.mem_range.mp hi))
      _ = _ := by simp
  nlinarith

end GroupWL.MachinePrograms.Structured
