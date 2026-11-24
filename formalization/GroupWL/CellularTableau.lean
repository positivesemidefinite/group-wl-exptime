import GroupWL.CyclicCellular
import GroupWL.AddressedCircuit

/-! # The finite monotone circuit of a cellular computation

Each cell letter has a scalar gate. For each triple of letters, two AND
gates test the previous row's three neighboring letters. The first tests the
left and center letters; the second adds the right letter and feeds the
scalar gate selected by the local rule. Time never wraps.
-/
namespace GroupWL.CellularTableau

inductive Gate (Alphabet : Type*) where
  | scalar (a : Alphabet)
  | pair (a b c : Alphabet)
  | triple (a b c : Alphabet)
  deriving DecidableEq, Fintype

variable {Alphabet : Type*} (f : Alphabet → Alphabet → Alphabet → Alphabet) (initial : ℤ → Alphabet)

def run : ℕ → ℤ → Alphabet
  | 0 => initial
  | t + 1 => fun x => f (run t (x - 1)) (run t x) (run t (x + 1))

section Finite
variable {n time : ℕ} (rule : Alphabet → Alphabet → Alphabet → Alphabet) (seed : ZMod n → Alphabet)

def cyclicRun : ℕ → ZMod n → Alphabet
  | 0 => seed
  | t + 1 => fun x => rule (cyclicRun t (x - 1)) (cyclicRun t x) (cyclicRun t (x + 1))

abbrev Node (Alphabet : Type*) (time n : ℕ) := Gate Alphabet × Fin (time + 1) × ZMod n

/-- The expanded finite monotone circuit. The `pair` and `triple`
constructors are exactly its two AND gates. -/
inductive True : Node Alphabet time n → Prop
  | seed (x : ZMod n) : True (.scalar (seed x), 0, x)
  | pair (t : Fin time) (x : ZMod n) (a b c : Alphabet)
      (hl : True (.scalar a, t.castSucc, x - 1))
      (hc : True (.scalar b, t.castSucc, x)) : True (.pair a b c, t.succ, x)
  | triple (t : Fin time) (x : ZMod n) (a b c : Alphabet)
      (hp : True (.pair a b c, t.succ, x))
      (hr : True (.scalar c, t.castSucc, x + 1)) : True (.triple a b c, t.succ, x)
  | scalar (t : Fin (time + 1)) (x : ZMod n) (a b c : Alphabet)
      (ht : True (.triple a b c, t, x)) : True (.scalar (rule a b c), t, x)

def Meaning : Node Alphabet time n → Prop
  | (.scalar a, t, x) => a = cyclicRun rule seed t.val x
  | (.pair a b _, t, x) => ∃ s : ℕ, t.val = s + 1 ∧
      a = cyclicRun rule seed s (x - 1) ∧ b = cyclicRun rule seed s x
  | (.triple a b c, t, x) => ∃ s : ℕ, t.val = s + 1 ∧
      a = cyclicRun rule seed s (x - 1) ∧ b = cyclicRun rule seed s x ∧
      c = cyclicRun rule seed s (x + 1)

/-- No false letter can become true in the monotone circuit. -/
theorem sound {v : Node Alphabet time n} (h : True rule seed v) : Meaning rule seed v := by
  induction h with
  | seed x => rfl
  | pair t x a b c _ _ ihl ihc => exact ⟨t.val, rfl, ihl, ihc⟩
  | triple t x a b c _ _ ihp ihr =>
    obtain ⟨s, hs, ha, hb⟩ := ihp
    have hst : s = t.val := by simpa using hs.symm
    subst s
    exact ⟨t.val, rfl, ha, hb, ihr⟩
  | scalar t x a b c _ iht =>
    obtain ⟨s, hs, ha, hb, hc⟩ := iht
    change rule a b c = cyclicRun rule seed t.val x
    rw [hs, cyclicRun, ha, hb, hc]

/-- The true letter at every finite tableau position is derived by its
explicit pair and triple gates. -/
theorem complete (t : Fin (time + 1)) (x : ZMod n) :
    True rule seed (.scalar (cyclicRun rule seed t.val x), t, x) := by
  induction t using Fin.induction generalizing x with
  | zero => exact .seed x
  | succ t ih =>
    apply True.scalar t.succ x
      (cyclicRun rule seed t.val (x - 1))
      (cyclicRun rule seed t.val x)
      (cyclicRun rule seed t.val (x + 1))
    apply True.triple
    · exact .pair t x _ _ _ (ih (x - 1)) (ih x)
    · exact ih (x + 1)

theorem scalar_iff (a : Alphabet) (t : Fin (time + 1)) (x : ZMod n) :
    True rule seed (.scalar a, t, x) ↔ a = cyclicRun rule seed t.val x := by
  constructor
  · exact sound rule seed
  · intro h; subst a; exact complete rule seed t x

/-- Rank strictly increases along each of the circuit's directed wires. -/
def rank : Node Alphabet time n → ℕ
  | (.pair _ _ _, t, _) => 3 * t.val
  | (.triple _ _ _, t, _) => 3 * t.val + 1
  | (.scalar _, t, _) => 3 * t.val + 2

theorem scalar_to_pair_rank (t : Fin time) (x y : ZMod n) (a b c d : Alphabet) :
    rank (.scalar a, t.castSucc, x) < rank (.pair b c d, t.succ, y) := by
  simp [rank]; omega

theorem pair_to_triple_rank (t : Fin (time + 1)) (x : ZMod n) (a b c : Alphabet) :
    rank (.pair a b c, t, x) < rank (.triple a b c, t, x) := by simp [rank]

theorem scalar_to_triple_rank (t : Fin time) (x y : ZMod n) (a b c d : Alphabet) :
    rank (.scalar a, t.castSucc, x) < rank (.triple b c d, t.succ, y) := by
  simp [rank]; omega

theorem triple_to_scalar_rank (t : Fin (time + 1)) (x : ZMod n) (a b c d : Alphabet) :
    rank (.triple a b c, t, x) < rank (.scalar d, t, x) := by simp [rank]

end Finite

section Machines
open Complexity MachineCellular

theorem machine_run_eq (M : Machine) (n : ℕ) (f : ZMod n → Cell M) (t : ℕ) :
    cyclicRun (MachineCellular.rule M) f t = MachineCellular.cyclicRun M n f t := by
  induction t with
  | zero => rfl
  | succ t ih => funext x; simp only [cyclicRun, MachineCellular.cyclicRun,
      MachineCellular.cyclicStep, ih]

/-- The accepting gates of the fully expanded finite monotone tableau agree
with the halt bit of the actual time-bounded operational machine. -/
theorem machine_tableau_acceptance (M : Machine) (w : BitString)
    (n T t terminal : ℕ) [NeZero n]
    (hT : 0 < T) (hn : 4 * T ≤ n) (hw : w.length ≤ T)
    (ht : t ≤ T) (hterminal : t ≤ terminal)
    (b : Bool) (hb : (execute M w t).control = .inl b) :
    (∃ z : ZMod n, ∃ c : Cell M, c.2 = some (.inl true) ∧
      True (MachineCellular.rule M) (cyclicInitial M w n)
        (.scalar c, Fin.last terminal, z)) ↔ b = true := by
  rw [← cyclic_terminal_acceptance M w n T t terminal hT hn hw ht hterminal b hb]
  constructor
  · rintro ⟨z, c, hc, htrue⟩
    have he := (scalar_iff (MachineCellular.rule M) (cyclicInitial M w n) c (Fin.last terminal) z).mp htrue
    rw [machine_run_eq] at he
    simp only [Fin.val_last] at he
    exact ⟨z, by rw [← he]; exact hc⟩
  · rintro ⟨z, hz⟩
    refine ⟨z, MachineCellular.cyclicRun M n (cyclicInitial M w n) terminal z, ?_⟩
    exact ⟨hz, by rw [scalar_iff, machine_run_eq]; rfl⟩

end Machines

end GroupWL.CellularTableau
