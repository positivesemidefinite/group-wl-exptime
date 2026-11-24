import GroupWL.MachinePrograms.Core

/-! Finite-control Boolean stack instructions, with a fixed finite set of stacks.
Input starts on the designated stack in reverse order; this convention matches
the left-to-right input tape without an uncharged preprocessing reversal.
-/
namespace GroupWL.MachinePrograms.Stacks

open Complexity
open scoped BigOperators

inductive Instruction (K Q : Type*)
  | push : K → Bool → Q → Instruction K Q
  | pop : K → (Option Bool → Q) → Instruction K Q
  | peek : K → (Option Bool → Q) → Instruction K Q
  | halt : Bool → Instruction K Q

structure Machine (K Q : Type*) where
  start : Q
  instruction : Q → Instruction K Q

structure Config (K Q : Type*) where
  control : Bool ⊕ Q
  «stacks» : K → List Bool

@[ext] theorem Config.ext {K Q : Type*} {c d : Config K Q}
    (hc : c.control = d.control) (hs : c.stacks = d.stacks) : c = d := by
  cases c; cases d; cases hc; cases hs; rfl

variable {K Q : Type*} [DecidableEq K]

def initial (M : Machine K Q) (input : K) (w : BitString) : Config K Q :=
  ⟨.inr M.start, Function.update (fun _ => []) input w.reverse⟩

def step (M : Machine K Q) (c : Config K Q) : Config K Q :=
  match c.control with
  | .inl _ => c
  | .inr q => match M.instruction q with
    | .push k b l => ⟨.inr l, Function.update c.stacks k (b :: c.stacks k)⟩
    | .pop k f => ⟨.inr (f (c.stacks k).head?), Function.update c.stacks k (c.stacks k).tail⟩
    | .peek k f => ⟨.inr (f (c.stacks k).head?), c.stacks⟩
    | .halt b => ⟨.inl b, c.stacks⟩

def execute (M : Machine K Q) (input : K) (w : BitString) (t : ℕ) : Config K Q :=
  (step M)^[t] (initial M input w)

def size [Fintype K] (c : Config K Q) : ℕ := ∑ k, (c.stacks k).length

theorem length_update (S : K → List Bool) (k : K) (L : List Bool) (j : K) :
    (Function.update S k L j).length =
      Function.update (fun i => (S i).length) k L.length j := by
  by_cases h : j = k <;> simp [Function.update_apply, h]

theorem size_initial [Fintype K] (M : Machine K Q) (input : K) (w : BitString) :
    size (initial M input w) = w.length := by
  classical
  simp only [size, initial, length_update, List.length_nil, List.length_reverse]
  rw [Finset.sum_update_of_mem (Finset.mem_univ input)]
  simp

theorem size_step [Fintype K] (M : Machine K Q) (c : Config K Q) :
    size (step M c) ≤ size c + 1 := by
  classical
  cases hc : c.control with
  | inl b => simp [step, hc]
  | inr q =>
    cases hi : M.instruction q with
    | push k b q' =>
        simp only [step, hc, hi, size, length_update]
        rw [Finset.sum_update_of_mem (Finset.mem_univ k)]
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k)]
        simp only [Finset.sdiff_singleton_eq_erase, List.length_cons]
        omega
    | pop k f =>
        simp only [step, hc, hi, size, length_update]
        rw [Finset.sum_update_of_mem (Finset.mem_univ k)]
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k)]
        simp only [Finset.sdiff_singleton_eq_erase, List.length_tail]
        omega
    | peek k f => simp [step, hc, hi, size]
    | halt b => simp [step, hc, hi, size]

end GroupWL.MachinePrograms.Stacks
