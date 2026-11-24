import Mathlib.Data.List.OfFn
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-!
# Explicit deterministic time classes

Every step reads and writes one tape cell and moves the head by at most one.
The machine has a fixed finite alphabet and a fixed finite set of active
states. Its tape does not have an input oracle. These definitions are used
to state the computational target; defining a class does not establish
membership of the WL language in that class.
-/
namespace GroupWL.Complexity

abbrev BitString := List Bool
abbrev Language := Set BitString

inductive Direction where
  | backward | stationary | forward
  deriving DecidableEq

def Direction.offset : Direction → ℤ
  | .backward => -1
  | .stationary => 0
  | .forward => 1

/-- Blank, input bits, and a fixed finite collection of work symbols. -/
abbrev Symbol (a : ℕ) := Option Bool ⊕ Fin a
/-- A Boolean return value or an active state. -/
abbrev Control (q : ℕ) := Bool ⊕ Fin q

structure Machine where
  workSymbols : ℕ
  states : ℕ
  start : Fin states
  transition : Fin states → Symbol workSymbols →
    Control states × Symbol workSymbols × Direction

structure Configuration (M : Machine) where
  control : Control M.states
  position : ℤ
  cells : ℤ → Symbol M.workSymbols

@[ext] theorem Configuration.ext {M : Machine} {c d : Configuration M}
    (hc : c.control = d.control) (hp : c.position = d.position)
    (ht : c.cells = d.cells) : c = d := by cases c; cases d; cases hc; cases hp; cases ht; rfl

def initial (M : Machine) (input : BitString) : Configuration M where
  control := .inr M.start
  position := 0
  cells i := if 0 ≤ i then .inl input[i.toNat]? else .inl none

def tick (M : Machine) (c : Configuration M) : Configuration M :=
  match c.control with
  | .inl _ => c
  | .inr q =>
    let action := M.transition q (c.cells c.position)
    { control := action.1
      position := c.position + action.2.2.offset
      cells := Function.update c.cells c.position action.2.1 }

def execute (M : Machine) (input : BitString) : ℕ → Configuration M
  | 0 => initial M input
  | t + 1 => tick M (execute M input t)

def DecidesBy (M : Machine) (L : Language) (budget : ℕ → ℕ) : Prop :=
  ∀ w, ∃ t ≤ budget w.length, ∃ b : Bool,
    (execute M w t).control = .inl b ∧ (b = true ↔ w ∈ L)

def InEXPTIME (L : Language) : Prop :=
  ∃ (M : Machine) (c d : ℕ), DecidesBy M L (fun n => 2 ^ (c * (n + 1) ^ d))

/-- The output is the uninterrupted bit string at the tape origin, followed by a blank. -/
def Outputs {M : Machine} (c : Configuration M) (word : BitString) : Prop :=
  (∀ i : Fin word.length, c.cells (i.val : ℤ) = .inl (some word[i])) ∧
    c.cells (word.length : ℤ) = .inl none

def ComputesBy (M : Machine) (f : BitString → BitString) (budget : ℕ → ℕ) : Prop :=
  ∀ w, ∃ t ≤ budget w.length,
    (execute M w t).control = .inl true ∧ Outputs (execute M w t) (f w)

def PolynomialReduction (L S : Language) : Prop :=
  ∃ (M : Machine) (f : BitString → BitString) (c d : ℕ),
    ComputesBy M f (fun n => c * (n + 1) ^ d) ∧ ∀ w, w ∈ L ↔ f w ∈ S

def EXPTIMEHard (S : Language) : Prop :=
  ∀ L, InEXPTIME L → PolynomialReduction L S

def EXPTIMEComplete (S : Language) : Prop := InEXPTIME S ∧ EXPTIMEHard S

private def flipControl {q : ℕ} : Control q → Control q := Sum.map Bool.not id

/-- Complementing the halting output changes no tape operation or running time. -/
def complement (M : Machine) : Machine where
  workSymbols := M.workSymbols
  states := M.states
  start := M.start
  transition q a :=
    let act := M.transition q a
    (flipControl act.1, act.2)

private def flipConfiguration {M : Machine} (c : Configuration M) :
    Configuration (complement M) where
  control := flipControl c.control
  position := c.position
  cells := c.cells

private theorem tick_flip (M : Machine) (c : Configuration M) :
    tick (complement M) (flipConfiguration c) = flipConfiguration (tick M c) := by
  cases c with
  | mk s pos tape =>
    cases s <;> rfl

private theorem execute_complement (M : Machine) (w : BitString) (t : ℕ) :
    execute (complement M) w t = flipConfiguration (execute M w t) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [execute, ih, tick_flip]; rfl

theorem DecidesBy.complement {M : Machine} {L : Language} {budget : ℕ → ℕ}
    (h : DecidesBy M L budget) : DecidesBy (complement M) Lᶜ budget := by
  intro w
  obtain ⟨t, ht, b, hb, hL⟩ := h w
  refine ⟨t, ht, !b, ?_, ?_⟩
  · rw [execute_complement]
    change flipControl (execute M w t).control = Sum.inl (!b)
    rw [hb]
    rfl
  · cases b <;> simp_all

theorem inEXPTIME_complement {L : Language} (h : InEXPTIME L) : InEXPTIME Lᶜ := by
  obtain ⟨M, c, d, h⟩ := h
  exact ⟨complement M, c, d, h.complement⟩

theorem inEXPTIME_complement_iff (L : Language) : InEXPTIME Lᶜ ↔ InEXPTIME L := by
  constructor
  · intro h
    simpa using inEXPTIME_complement h
  · exact inEXPTIME_complement

end GroupWL.Complexity
