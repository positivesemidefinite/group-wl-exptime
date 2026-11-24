import GroupWL.MachineCellular
import Mathlib.Data.ZMod.Basic

/-! # Finite cyclic simulation with a proved light-cone bound -/
namespace GroupWL.MachineCellular

open Complexity

/-- A radius-one computation reads only the indicated finite interval. -/
theorem run_eq_of_initial_eq_on (M : Machine) (f g : ℤ → Cell M) (t : ℕ) (x : ℤ)
    (h : ∀ y : ℤ, x - t ≤ y → y ≤ x + t → f y = g y) :
    run M f t x = run M g t x := by
  induction t generalizing x with
  | zero => exact h x (by simp) (by simp)
  | succ t ih =>
    change rule M (run M f t (x - 1)) (run M f t x) (run M f t (x + 1)) =
      rule M (run M g t (x - 1)) (run M g t x) (run M g t (x + 1))
    congr 1
    · apply ih; intro y hy hy'; apply h <;> omega
    · apply ih; intro y hy hy'; apply h <;> omega
    · apply ih; intro y hy hy'; apply h <;> omega

theorem head_ne_none_rule (M : Machine) (l c r : Cell M)
    (h : (rule M l c r).2 ≠ none) : l.2 ≠ none ∨ c.2 ≠ none ∨ r.2 ≠ none := by
  by_contra! hz
  apply h
  simp [rule, incoming, hz.1, hz.2.1, hz.2.2]

/-- A head can travel at most one cell per step, including on malformed
initial rows. No new head can appear outside every initial head's cone. -/
theorem head_ancestor (M : Machine) (f : ℤ → Cell M) (t : ℕ) (x : ℤ)
    (h : (run M f t x).2 ≠ none) :
    ∃ y : ℤ, x - t ≤ y ∧ y ≤ x + t ∧ (f y).2 ≠ none := by
  induction t generalizing x with
  | zero => exact ⟨x, by simp, by simp, h⟩
  | succ t ih =>
    obtain h | h | h := head_ne_none_rule M _ _ _ h
    · obtain ⟨y, hy, hy', hf⟩ := ih (x - 1) h
      exact ⟨y, by omega, by omega, hf⟩
    · obtain ⟨y, hy, hy', hf⟩ := ih x h
      exact ⟨y, by omega, by omega, hf⟩
    · obtain ⟨y, hy, hy', hf⟩ := ih (x + 1) h
      exact ⟨y, by omega, by omega, hf⟩

theorem incoming_eq_none_of_no_active (M : Machine) (c : Cell M) (d : Direction)
    (h : ∀ s, c.2 ≠ some (.inr s)) : incoming M c d = none := by
  cases hc : c.2 with
  | none => simp [incoming, hc]
  | some s =>
    cases s with
    | inl b => simp [incoming, hc]
    | inr s => exact False.elim (h s hc)

theorem rule_eq_center_of_no_active (M : Machine) (l c r : Cell M)
    (hl : ∀ s, l.2 ≠ some (.inr s)) (hc : ∀ s, c.2 ≠ some (.inr s))
    (hr : ∀ s, r.2 ≠ some (.inr s)) : rule M l c r = c := by
  cases hhead : c.2 with
  | none =>
    have hi := incoming_eq_none_of_no_active M l .forward hl
    have hj := incoming_eq_none_of_no_active M r .backward hr
    apply Prod.ext <;> simp [rule, hhead, hi, hj]
  | some s =>
    cases s with
    | inl b => apply Prod.ext <;> simp [rule, hhead]
    | inr s => exact False.elim (hc s hhead)

def cyclicStep (M : Machine) (n : ℕ) (f : ZMod n → Cell M) (x : ZMod n) : Cell M :=
  rule M (f (x - 1)) (f x) (f (x + 1))

def cyclicRun (M : Machine) (n : ℕ) (f : ZMod n → Cell M) : ℕ → ZMod n → Cell M
  | 0 => f
  | t + 1 => cyclicStep M n (cyclicRun M n f t)

def periodicLift (M : Machine) (n : ℕ) (f : ZMod n → Cell M) (x : ℤ) : Cell M := f x

theorem periodicLift_step (M : Machine) (n : ℕ) (f : ZMod n → Cell M) :
    periodicLift M n (cyclicStep M n f) = step M (periodicLift M n f) := by
  funext x
  simp [periodicLift, cyclicStep, step]

theorem periodicLift_run (M : Machine) (n : ℕ) (f : ZMod n → Cell M) (t : ℕ) :
    periodicLift M n (cyclicRun M n f t) = run M (periodicLift M n f) t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [cyclicRun, periodicLift_step, ih]; rfl

theorem cyclicStep_eq_of_no_active (M : Machine) (n : ℕ) (f : ZMod n → Cell M)
    (h : ∀ x s, (f x).2 ≠ some (.inr s)) : cyclicStep M n f = f := by
  funext x
  exact rule_eq_center_of_no_active M _ _ _ (h _) (h _) (h _)

theorem cyclicRun_fixed (M : Machine) (n : ℕ) (f : ZMod n → Cell M)
    (h : cyclicStep M n f = f) (t : ℕ) : cyclicRun M n f t = f := by
  induction t with
  | zero => rfl
  | succ t ih => rw [cyclicRun, ih, h]

theorem cyclicRun_add (M : Machine) (n : ℕ) (f : ZMod n → Cell M) (t s : ℕ) :
    cyclicRun M n f (t + s) = cyclicRun M n (cyclicRun M n f t) s := by
  induction s with
  | zero => rfl
  | succ s ih => rw [Nat.add_succ, cyclicRun, ih]; rfl

theorem execute_position_bound (M : Machine) (w : BitString) (t : ℕ) :
    -(t : ℤ) ≤ (execute M w t).position ∧ (execute M w t).position ≤ (t : ℤ) := by
  induction t with
  | zero => simp [execute, initial]
  | succ t ih =>
    cases hc : (execute M w t).control with
    | inl b => simp only [execute, tick, hc]; constructor <;> omega
    | inr s =>
      generalize ha : M.transition s ((execute M w t).cells (execute M w t).position) = a
      rcases a with ⟨state, sym, dir⟩
      cases dir <;> simp only [execute, tick, hc, ha, Direction.offset] <;>
        constructor <;> omega

def cyclicInitial (M : Machine) (w : BitString) (n : ℕ) (x : ZMod n) : Cell M :=
  encode M (initial M w) (x.val : ℤ)

theorem cyclicInitial_head (M : Machine) (w : BitString) (n : ℕ) (x : ZMod n) :
    (cyclicInitial M w n x).2 ≠ none ↔ x = 0 := by
  simp [cyclicInitial, encode, initial, ZMod.val_eq_zero]

/-- A circle at least four times the running-time bound has the same initial
row as the integer tape throughout every possible head's dependency cone. -/
theorem cyclicInitial_agrees (M : Machine) (w : BitString) (n T : ℕ) [NeZero n]
    (hT : 0 < T) (hn : 4 * T ≤ n) (hw : w.length ≤ T)
    (x : ℤ) (hx : -(2 * (T : ℤ)) ≤ x) (hx' : x ≤ 2 * (T : ℤ)) :
    periodicLift M n (cyclicInitial M w n) x = encode M (initial M w) x := by
  change encode M (initial M w) (((x : ZMod n).val : ℕ) : ℤ) = _
  by_cases hp : 0 ≤ x
  · have hxn : x < (n : ℤ) := by omega
    rw [ZMod.val_intCast, Int.emod_eq_of_lt hp hxn]
  · have hxneg : x < 0 := by omega
    have hpos : 0 ≤ x + (n : ℤ) := by omega
    have hlt : x + (n : ℤ) < (n : ℤ) := by omega
    have hval : (((x : ZMod n).val : ℕ) : ℤ) = x + (n : ℤ) := by
      rw [ZMod.val_intCast, ← Int.add_emod_right x (n : ℤ), Int.emod_eq_of_lt hpos hlt]
    rw [hval]
    have hlen : w.length ≤ (x + (n : ℤ)).toNat := by omega
    have hnonzero : x + (n : ℤ) ≠ 0 := by omega
    have hxzero : x ≠ 0 := by omega
    simp [encode, initial, hp, hpos, hnonzero, hxzero, List.getElem?_eq_none hlen]

/-- Up to the time bound, all cells within head reach agree exactly with the
actual machine computation on its unbounded tape. -/
theorem cyclicRun_agrees (M : Machine) (w : BitString) (n T t : ℕ) [NeZero n]
    (hT : 0 < T) (hn : 4 * T ≤ n) (hw : w.length ≤ T) (ht : t ≤ T)
    (x : ℤ) (hx : -(T : ℤ) ≤ x) (hx' : x ≤ T) :
    cyclicRun M n (cyclicInitial M w n) t (x : ZMod n) = encode M (execute M w t) x := by
  change periodicLift M n (cyclicRun M n (cyclicInitial M w n) t) x = _
  rw [periodicLift_run, encode_execute]
  apply run_eq_of_initial_eq_on
  intro y hy hy'
  apply cyclicInitial_agrees M w n T hT hn hw y <;> omega

/-- Every head on the finite circle has a representative within the true
machine's reach, where the preceding exact simulation applies. -/
theorem cyclic_head_matches (M : Machine) (w : BitString) (n T t : ℕ) [NeZero n]
    (hT : 0 < T) (hn : 4 * T ≤ n) (hw : w.length ≤ T) (ht : t ≤ T)
    (z : ZMod n) (hz : (cyclicRun M n (cyclicInitial M w n) t z).2 ≠ none) :
    ∃ x : ℤ, -(T : ℤ) ≤ x ∧ x ≤ T ∧ (x : ZMod n) = z ∧
      cyclicRun M n (cyclicInitial M w n) t z = encode M (execute M w t) x := by
  have hh : (run M (periodicLift M n (cyclicInitial M w n)) t (z.val : ℤ)).2 ≠ none := by
    rw [← periodicLift_run]
    simpa [periodicLift] using hz
  obtain ⟨y, hy, hy', hyh⟩ := head_ancestor M _ t (z.val : ℤ) hh
  have hyzero : (y : ZMod n) = 0 := (cyclicInitial_head M w n _).mp hyh
  let x : ℤ := (z.val : ℤ) - y
  have hx : -(T : ℤ) ≤ x := by dsimp [x]; omega
  have hx' : x ≤ T := by dsimp [x]; omega
  have hcast : (x : ZMod n) = z := by simp [x, hyzero]
  refine ⟨x, hx, hx', hcast, ?_⟩
  rw [← hcast]
  exact cyclicRun_agrees M w n T t hT hn hw ht x hx hx'

theorem cyclic_no_active_of_halt (M : Machine) (w : BitString) (n T t : ℕ) [NeZero n]
    (hT : 0 < T) (hn : 4 * T ≤ n) (hw : w.length ≤ T) (ht : t ≤ T)
    (b : Bool) (hb : (execute M w t).control = .inl b) :
    ∀ z s, (cyclicRun M n (cyclicInitial M w n) t z).2 ≠ some (.inr s) := by
  intro z s hs
  have hz : (cyclicRun M n (cyclicInitial M w n) t z).2 ≠ none := by rw [hs]; simp
  obtain ⟨x, _, _, _, hx⟩ := cyclic_head_matches M w n T t hT hn hw ht z hz
  rw [hx, encoded_head_iff] at hs
  rw [hb] at hs
  simp at hs

theorem cyclic_accepts_iff_of_halt (M : Machine) (w : BitString) (n T t : ℕ) [NeZero n]
    (hT : 0 < T) (hn : 4 * T ≤ n) (hw : w.length ≤ T) (ht : t ≤ T)
    (b : Bool) (hb : (execute M w t).control = .inl b) :
    (∃ z, (cyclicRun M n (cyclicInitial M w n) t z).2 = some (.inl true)) ↔ b = true := by
  constructor
  · rintro ⟨z, hz⟩
    have hzne : (cyclicRun M n (cyclicInitial M w n) t z).2 ≠ none := by rw [hz]; simp
    obtain ⟨x, _, _, _, hx⟩ := cyclic_head_matches M w n T t hT hn hw ht z hzne
    rw [hx, encoded_head_iff, hb] at hz
    exact Sum.inl.inj hz.2
  · intro h; subst b
    have hp := execute_position_bound M w t
    refine ⟨((execute M w t).position : ZMod n), ?_⟩
    rw [cyclicRun_agrees M w n T t hT hn hw ht _ (by omega) (by omega), encoded_head_iff]
    exact ⟨rfl, hb⟩

/-- Once the bounded computation halts, every later tableau row is frozen.
Thus the final-time acceptance test is exact, even beyond the simulation
time bound and before any hypothetical cyclic wrap could matter. -/
theorem cyclic_terminal_acceptance (M : Machine) (w : BitString) (n T t terminal : ℕ)
    [NeZero n] (hT : 0 < T) (hn : 4 * T ≤ n) (hw : w.length ≤ T)
    (ht : t ≤ T) (hterminal : t ≤ terminal)
    (b : Bool) (hb : (execute M w t).control = .inl b) :
    (∃ z, (cyclicRun M n (cyclicInitial M w n) terminal z).2 = some (.inl true)) ↔
      b = true := by
  have hfixed := cyclicStep_eq_of_no_active M n _
    (cyclic_no_active_of_halt M w n T t hT hn hw ht b hb)
  have he : cyclicRun M n (cyclicInitial M w n) terminal =
      cyclicRun M n (cyclicInitial M w n) t := by
    rw [← Nat.add_sub_of_le hterminal, cyclicRun_add]
    exact cyclicRun_fixed M n _ hfixed _
  rw [he]
  exact cyclic_accepts_iff_of_halt M w n T t hT hn hw ht b hb

end GroupWL.MachineCellular
