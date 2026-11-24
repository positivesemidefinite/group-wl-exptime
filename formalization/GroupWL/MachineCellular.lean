import GroupWL.Complexity

/-! # The local cellular rule of the explicit one-tape machine

This is the first semantic stage of the addressed-circuit compiler. A finite
cell alphabet records its tape symbol and, at the unique head position, the
machine control. The radius-one rule below simulates exactly one machine
step; halting configurations are frozen.
-/
namespace GroupWL.MachineCellular

open Complexity

abbrev Cell (M : Machine) := Symbol M.workSymbols × Option (Control M.states)

def encode (M : Machine) (c : Configuration M) (x : ℤ) : Cell M :=
  (c.cells x, if x = c.position then some c.control else none)

/-- The control sent by an active neighboring head moving in direction `d`. -/
def incoming (M : Machine) (cell : Cell M) (d : Direction) : Option (Control M.states) :=
  match cell.2 with
  | some (.inr q) =>
      let act := M.transition q cell.1
      if act.2.2 = d then some act.1 else none
  | _ => none

/-- Deterministic radius-one update, defined also on malformed neighborhoods.
Only configurations with their one encoded head are used in the proof. -/
def rule (M : Machine) (left center right : Cell M) : Cell M :=
  match center.2 with
  | some (.inl b) => (center.1, some (.inl b))
  | some (.inr q) =>
      let act := M.transition q center.1
      (act.2.1, if act.2.2 = .stationary then some act.1 else none)
  | none => (center.1,
      (incoming M left .forward).orElse (fun _ => incoming M right .backward))

def step (M : Machine) (cells : ℤ → Cell M) (x : ℤ) : Cell M :=
  rule M (cells (x - 1)) (cells x) (cells (x + 1))

/-- The local rule is an exact simulation of the operational tape step. -/
theorem encode_tick (M : Machine) (c : Configuration M) :
    encode M (tick M c) = step M (encode M c) := by
  funext x
  cases c with
  | mk ctrl pos tape =>
    cases ctrl with
    | inl b =>
      by_cases hc : x = pos
      · subst x; simp [encode, tick, step, rule]
      · by_cases hl : x - 1 = pos <;> by_cases hr : x + 1 = pos <;>
          simp [encode, tick, step, rule, incoming, hc, hl, hr]
    | inr q =>
      generalize hact : M.transition q (tape pos) = act
      rcases act with ⟨state, symbol, motion⟩
      cases motion <;>
        by_cases hc : x = pos <;>
        by_cases hl : x - 1 = pos <;>
        by_cases hr : x + 1 = pos <;>
        simp_all [encode, tick, step, rule, incoming, Direction.offset]
      all_goals omega

def run (M : Machine) (initialCells : ℤ → Cell M) : ℕ → ℤ → Cell M
  | 0 => initialCells
  | t + 1 => step M (run M initialCells t)

/-- Every finite computation is reproduced pointwise by the finite-alphabet
radius-one cellular dynamics. -/
theorem encode_execute (M : Machine) (w : BitString) (t : ℕ) :
    encode M (execute M w t) = run M (encode M (initial M w)) t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [execute, encode_tick, ih]; rfl

/-- The cellular representation has precisely one head, with the actual
machine's control at its actual tape position. -/
theorem encoded_head_iff (M : Machine) (c : Configuration M) (x : ℤ) (s : Control M.states) :
    (encode M c x).2 = some s ↔ x = c.position ∧ c.control = s := by
  simp [encode]

/-- Acceptance is read by the accepting head letter anywhere in the row. -/
theorem accepting_cell_iff (M : Machine) (w : BitString) (t : ℕ) :
    (∃ x, (run M (encode M (initial M w)) t x).2 = some (.inl true)) ↔
      (execute M w t).control = .inl true := by
  rw [← encode_execute]
  simp [encoded_head_iff]

end GroupWL.MachineCellular
