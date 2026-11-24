import GroupWL.Operational
import Mathlib.Data.Fintype.EquivFin

/-! Finite algebraic control states for the explicit one-tape machine model.

Each source step reads/writes one cell and moves by at most one. Translation
only numbers the finitely many control states; it has exactly unit slowdown.
-/
namespace GroupWL.MachinePrograms

open Complexity

structure Program (Q : Type*) (a : ℕ) where
  start : Q
  transition : Q → Symbol a → (Bool ⊕ Q) × Symbol a × Direction

structure Config (Q : Type*) (a : ℕ) where
  control : Bool ⊕ Q
  position : ℤ
  cells : ℤ → Symbol a

@[ext] theorem Config.ext {Q : Type*} {a : ℕ} {c d : Config Q a}
    (hc : c.control = d.control) (hp : c.position = d.position)
    (ht : c.cells = d.cells) : c = d := by
  cases c; cases d; cases hc; cases hp; cases ht; rfl

namespace Program

variable {Q : Type*} {a : ℕ} (P : Program Q a)

def initial (w : BitString) : Config Q a where
  control := .inr P.start
  position := 0
  cells i := if 0 ≤ i then .inl w[i.toNat]? else .inl none

def tick (c : Config Q a) : Config Q a :=
  match c.control with
  | .inl _ => c
  | .inr q =>
    let act := P.transition q (c.cells c.position)
    ⟨act.1, c.position + act.2.2.offset, Function.update c.cells c.position act.2.1⟩

def run (c : Config Q a) : ℕ → Config Q a
  | 0 => c
  | t+1 => P.tick (run c t)

def execute (w : BitString) (t : ℕ) := P.run (P.initial w) t

theorem run_add (c : Config Q a) (s t : ℕ) :
    P.run c (s + t) = P.run (P.run c s) t := by
  induction t with
  | zero => simp [run]
  | succ t ih => simpa [Nat.add_assoc, run] using congrArg P.tick ih

theorem run_halted (c : Config Q a) (b : Bool) (hc : c.control = .inl b) (t : ℕ) :
    P.run c t = c := by
  induction t with
  | zero => rfl
  | succ t ih => simp [run, ih, tick, hc]

/-- A scan whose transition leaves the inspected symbol unchanged performs
exactly one tape step per inspected cell. -/
theorem run_scan (q : Q) (pos : ℤ) (cells : ℤ → Symbol a) (dir : Direction)
    (n : ℕ)
    (h : ∀ i < n, P.transition q (cells (pos + (i : ℤ) * dir.offset)) =
      (.inr q, cells (pos + (i : ℤ) * dir.offset), dir)) :
    P.run ⟨.inr q, pos, cells⟩ n = ⟨.inr q, pos + (n : ℤ) * dir.offset, cells⟩ := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
      rw [run, ih (fun i hi => h i (by omega))]
      simp only [tick, h n (by omega), Function.update_eq_self]
      congr 1
      push_cast
      ring

def compileWith {q : ℕ} (e : Q ≃ Fin q) : Machine where
  workSymbols := a
  states := q
  start := e P.start
  transition l s :=
    let act := P.transition (e.symm l) s
    (Sum.map id e act.1, act.2)

def compileConfig {q : ℕ} (e : Q ≃ Fin q) (c : Config Q a) :
    Configuration (P.compileWith e) where
  control := Sum.map id e c.control
  position := c.position
  cells := c.cells

@[simp] theorem compileConfig_initial {q : ℕ} (e : Q ≃ Fin q) (w : BitString) :
    P.compileConfig e (P.initial w) = Complexity.initial (P.compileWith e) w := rfl

@[simp] theorem compileConfig_tick {q : ℕ} (e : Q ≃ Fin q) (c : Config Q a) :
    P.compileConfig e (P.tick c) = Complexity.tick (P.compileWith e) (P.compileConfig e c) := by
  cases c with
  | mk ctrl pos cells =>
    cases ctrl with
    | inl b => rfl
    | inr l => simp [compileConfig, tick, compileWith, Complexity.tick]

@[simp] theorem compileConfig_run {q : ℕ} (e : Q ≃ Fin q) (c : Config Q a) (t : ℕ) :
    P.compileConfig e (P.run c t) = runFrom (P.compileWith e) (P.compileConfig e c) t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [run, runFrom, ih]

@[simp] theorem compileConfig_execute {q : ℕ} (e : Q ≃ Fin q) (w : BitString) (t : ℕ) :
    P.compileConfig e (P.execute w t) = Complexity.execute (P.compileWith e) w t := by
  simp [execute, runFrom_initial]

def Outputs (c : Config Q a) (w : BitString) : Prop :=
  (∀ i : Fin w.length, c.cells (i.val : ℤ) = .inl (some w[i])) ∧
    c.cells (w.length : ℤ) = .inl none

theorem computesBy_compileWith {q : ℕ} (e : Q ≃ Fin q) (f : BitString → BitString)
    (budget : ℕ → ℕ)
    (h : ∀ w, ∃ t ≤ budget w.length,
      (P.execute w t).control = .inl true ∧ Outputs (P.execute w t) (f w)) :
    ComputesBy (P.compileWith e) f budget := by
  intro w
  obtain ⟨t, ht, hh, ho⟩ := h w
  refine ⟨t, ht, ?_, ?_⟩
  · rw [← compileConfig_execute]
    simp [compileConfig, hh]
  · rw [← compileConfig_execute]
    exact ho

theorem decidesBy_compileWith {q : ℕ} (e : Q ≃ Fin q) (L : Language)
    (budget : ℕ → ℕ)
    (h : ∀ w, ∃ t ≤ budget w.length, ∃ b : Bool,
      (P.execute w t).control = .inl b ∧ (b = true ↔ w ∈ L)) :
    DecidesBy (P.compileWith e) L budget := by
  intro w
  obtain ⟨t, ht, b, hh, ho⟩ := h w
  refine ⟨t, ht, b, ?_, ho⟩
  rw [← compileConfig_execute]
  simp [compileConfig, hh]

/-- Arbitrary finite control types may be numbered once and for all. The
choice of this finite numbering is independent of the input word. -/
noncomputable def compile [Fintype Q] : Machine := P.compileWith (Fintype.equivFin Q)

end Program
end GroupWL.MachinePrograms
