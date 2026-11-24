import GroupWL.Complexity

/-! Exact-step tools for implementing the machines in `Complexity`.

These lemmas do not turn arbitrary Lean functions into machine programs.
They support explicit finite-control programs and counted local simulations.
-/
namespace GroupWL.Complexity

/-- Execute from any configuration, rather than only the input configuration. -/
def runFrom (M : Machine) (c : Configuration M) : ℕ → Configuration M
  | 0 => c
  | t + 1 => tick M (runFrom M c t)

@[simp] theorem runFrom_zero (M : Machine) (c : Configuration M) : runFrom M c 0 = c := rfl

@[simp] theorem runFrom_succ (M : Machine) (c : Configuration M) (t : ℕ) :
    runFrom M c (t + 1) = tick M (runFrom M c t) := rfl

theorem runFrom_add (M : Machine) (c : Configuration M) (s t : ℕ) :
    runFrom M c (s + t) = runFrom M (runFrom M c s) t := by
  induction t with
  | zero => simp
  | succ t ih => simpa [Nat.add_assoc, runFrom] using congrArg (tick M) ih

theorem runFrom_initial (M : Machine) (w : BitString) (t : ℕ) :
    runFrom M (initial M w) t = execute M w t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [runFrom, execute, ih]

@[simp] theorem tick_halted {M : Machine} (c : Configuration M) (b : Bool)
    (hc : c.control = .inl b) : tick M c = c := by
  simp [tick, hc]

theorem runFrom_halted {M : Machine} (c : Configuration M) (b : Bool)
    (hc : c.control = .inl b) (t : ℕ) : runFrom M c t = c := by
  induction t with
  | zero => rfl
  | succ t ih => rw [runFrom_succ, ih, tick_halted c b hc]

theorem execute_halted {M : Machine} {w : BitString} {s : ℕ} {b : Bool}
    (hc : (execute M w s).control = .inl b) (t : ℕ) :
    execute M w (s + t) = execute M w s := by
  rw [← runFrom_initial, runFrom_add, runFrom_initial]
  exact runFrom_halted _ b hc t

theorem ComputesBy.mono {M : Machine} {f : BitString → BitString}
    {a b : ℕ → ℕ} (h : ComputesBy M f a) (hab : ∀ n, a n ≤ b n) :
    ComputesBy M f b := by
  intro w
  obtain ⟨t, ht, hh, ho⟩ := h w
  exact ⟨t, ht.trans (hab _), hh, ho⟩

theorem DecidesBy.mono {M : Machine} {L : Language}
    {a b : ℕ → ℕ} (h : DecidesBy M L a) (hab : ∀ n, a n ≤ b n) :
    DecidesBy M L b := by
  intro w
  obtain ⟨t, ht, b, hh, ho⟩ := h w
  exact ⟨t, ht.trans (hab _), b, hh, ho⟩

/-- The polynomial slowdown from a linear-cost simulation of each source step.
`S` and `R` describe the actual source configurations and their tape encoding;
the simulation premise must be established for the concrete source instructions.
-/
theorem simulate_bounded_steps {S : Type*} (M : Machine) (step : S → S)
    (R : S → Configuration M → Prop) (size : S → ℕ) (a : ℕ)
    (grow : ∀ s, size (step s) ≤ size s + 1)
    (simulate : ∀ s c, R s c →
      ∃ t ≤ a * (size s + 1), R (step s) (runFrom M c t))
    (s : S) (c : Configuration M) (hsc : R s c) (n : ℕ) :
    ∃ t ≤ a * n * (size s + n + 1), R (step^[n] s) (runFrom M c t) := by
  have sizes : ∀ n, size (step^[n] s) ≤ size s + n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact (grow _).trans (by omega)
  induction n with
  | zero => exact ⟨0, by simp, by simpa using hsc⟩
  | succ n ih =>
      obtain ⟨t, ht, hr⟩ := ih
      obtain ⟨u, hu, huR⟩ := simulate _ _ hr
      refine ⟨t + u, ?_, ?_⟩
      · have hsize := sizes n
        have hu' : u ≤ a * (size s + n + 1) :=
          hu.trans (Nat.mul_le_mul_left _ (by omega))
        calc
          t + u ≤ a * n * (size s + n + 1) + a * (size s + n + 1) :=
            Nat.add_le_add ht hu'
          _ = a * (n + 1) * (size s + n + 1) := by ring
          _ ≤ a * (n + 1) * (size s + (n + 1) + 1) :=
            Nat.mul_le_mul_left _ (by omega)
      · simpa only [Function.iterate_succ_apply', runFrom_add] using huR

end GroupWL.Complexity
