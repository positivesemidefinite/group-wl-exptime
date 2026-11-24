import GroupWL.MachinePrograms.StackSimulation
import GroupWL.MachinePrograms.StackIO
import GroupWL.MachinePrograms.StackBudgets

/-! Quantitative compilation of finite-stack programs to the exact one-tape
machine model used by the theorem statement. -/
namespace GroupWL.MachinePrograms.Stacks

open Complexity
open scoped BigOperators

variable {K Q : Type*} [DecidableEq K] {a : ℕ}

def Represents (output : K) (e : Work K ≃ Fin a) (c : Config K Q)
    (d : MachinePrograms.Config (TapeControl Q) a) : Prop :=
  match c.control with
  | .inr q => d.control = .inr (.normal q) ∧ d.position = -1 ∧ Encodes e c.stacks d.cells
  | .inl b => d.control = .inl b ∧ Program.Outputs d (c.stacks output).reverse

theorem stack_length_le_size [Fintype K] (c : Config K Q) (k : K) :
    (c.stacks k).length ≤ size c := by
  exact Finset.single_le_sum (fun i _ => Nat.zero_le (c.stacks i).length) (Finset.mem_univ k)

theorem simulate_step [Fintype K] (M : Machine K Q) (input output : K) (e : Work K ≃ Fin a)
    (c : Config K Q) (d : MachinePrograms.Config (TapeControl Q) a)
    (hr : Represents output e c d) :
    ∃ t ≤ 3 * (size c + 1),
      Represents output e (step M c) ((tapeProgram M input output e).run d t) := by
  cases c with
  | mk ctrl S =>
    cases ctrl with
    | inl b => exact ⟨0, Nat.zero_le _, hr⟩
    | inr q =>
      cases d with
      | mk dctrl pos cells =>
        rcases hr with ⟨rfl, rfl, h⟩
        cases hi : M.instruction q with
        | push k b q' =>
          refine ⟨2 * (S k).length + 3, ?_, ?_⟩
          · have hk := stack_length_le_size (⟨.inr q,S⟩ : Config K Q) k
            dsimp only at hk
            omega
          · rw [push_steps M input output e S cells h q q' k b hi]
            simpa [Represents, step, hi] using h.push k b
        | pop k f =>
          have hk := stack_length_le_size (⟨.inr q,S⟩ : Config K Q) k
          cases hs : S k with
          | nil =>
            refine ⟨3, by omega, ?_⟩
            rw [pop_nil_steps M input output e S cells h q k f hi hs]
            have hu : Function.update S k [] = S := by rw [← hs, Function.update_eq_self]
            simpa [Represents, step, hi, hs, hu] using h
          | cons b L =>
            refine ⟨2 * L.length + 5, ?_, ?_⟩
            · simp only [hs, List.length_cons] at hk
              omega
            · rw [pop_cons_steps M input output e S cells h q k f b L hi hs]
              simpa [Represents, step, hi, hs] using h.pop k b L hs
        | peek k f =>
          have hk := stack_length_le_size (⟨.inr q,S⟩ : Config K Q) k
          cases hs : S k with
          | nil =>
            refine ⟨3, by omega, ?_⟩
            rw [peek_nil_steps M input output e S cells h q k f hi hs]
            simpa [Represents, step, hi, hs] using h
          | cons b L =>
            refine ⟨2 * L.length + 5, ?_, ?_⟩
            · simp only [hs, List.length_cons] at hk
              omega
            · rw [peek_cons_steps M input output e S cells h q k f b L hi hs]
              simpa [Represents, step, hi, hs] using h
        | halt b =>
          obtain ⟨final, hf, hctrl, hout⟩ := cleanup_tape M input output e S cells h b
          have h0 : (tapeProgram M input output e).run
              ⟨.inr (.normal q), -1, cells⟩ 1 = ⟨.inr (.clean b),0,cells⟩ := by
            simp [Program.run, Program.tick, tapeProgram, tapeTransition, hi,
              Direction.offset, Function.update_eq_self]
          refine ⟨1 + ((S output).length+1), ?_, ?_⟩
          · have hk := stack_length_le_size (⟨.inr q,S⟩ : Config K Q) output
            dsimp only at hk
            omega
          · rw [Program.run_add, h0, hf]
            simpa only [Represents, step, hi] using And.intro hctrl hout

variable (M : Machine K Q) (input output : K) (e : Work K ≃ Fin a)
variable {q : ℕ} (eq : TapeControl Q ≃ Fin q)

def CompiledRep (c : Config K Q)
    (d : Configuration ((tapeProgram M input output e).compileWith eq)) : Prop :=
  ∃ t, d = (tapeProgram M input output e).compileConfig eq t ∧ Represents output e c t

theorem simulate_compiled_step [Fintype K]
    (c : Config K Q) (d : Configuration ((tapeProgram M input output e).compileWith eq))
    (hr : CompiledRep M input output e eq c d) :
    ∃ t ≤ 3 * (size c + 1), CompiledRep M input output e eq (step M c)
      (runFrom ((tapeProgram M input output e).compileWith eq) d t) := by
  obtain ⟨d, rfl, hr⟩ := hr
  obtain ⟨t, ht, hR⟩ := simulate_step M input output e c d hr
  refine ⟨t, ht, (tapeProgram M input output e).run d t, ?_, hR⟩
  rw [Program.compileConfig_run]

theorem simulate_input [Fintype K] (w : BitString) (T : ℕ) :
    ∃ t ≤ simulationBudget (fun _ => T) w.length,
      CompiledRep M input output e eq (execute M input w T)
        (Complexity.execute ((tapeProgram M input output e).compileWith eq) w t) := by
  let P := tapeProgram M input output e
  let C := P.compileWith eq
  let t₀ := 2*w.length+4
  obtain ⟨cells, hi, henc⟩ := initialize_tape M input output e w
  have hinit : CompiledRep M input output e eq (initial M input w)
      (Complexity.execute C w t₀) := by
    refine ⟨⟨.inr (.normal M.start),-1,cells⟩, ?_, ?_⟩
    · rw [← Program.compileConfig_execute]
      change P.compileConfig eq (P.execute w (2*w.length+4)) = _
      rw [hi]
    · exact ⟨rfl, rfl, henc⟩
  obtain ⟨t, ht, hR⟩ := simulate_bounded_steps C (step M)
    (CompiledRep M input output e eq) size 3 (size_step M)
    (simulate_compiled_step M input output e eq)
    (initial M input w) (Complexity.execute C w t₀) hinit T
  refine ⟨t₀+t, ?_, ?_⟩
  · simp only [size_initial] at ht
    unfold simulationBudget
    exact Nat.add_le_add_left ht t₀
  · have hh : runFrom C (Complexity.execute C w t₀) t = Complexity.execute C w (t₀+t) := by
      rw [← runFrom_initial C w t₀, ← runFrom_add, runFrom_initial]
    rw [hh] at hR
    exact hR

def ComputesIn (f : BitString → BitString) (B : ℕ → ℕ) : Prop :=
  ∀ w, ∃ t ≤ B w.length, (execute M input w t).control = .inl true ∧
    ((execute M input w t).stacks output).reverse = f w

def DecidesIn (L : Language) (B : ℕ → ℕ) : Prop :=
  ∀ w, ∃ t ≤ B w.length, ∃ b : Bool,
    (execute M input w t).control = .inl b ∧ (b = true ↔ w ∈ L)

theorem computesBy_with [Fintype K] (f : BitString → BitString) (B : ℕ → ℕ)
    (h : ComputesIn M input output f B) :
    ComputesBy ((tapeProgram M input output e).compileWith eq) f (simulationBudget B) := by
  intro w
  obtain ⟨T, hT, hhalt, hout⟩ := h w
  obtain ⟨t, ht, d, hd, hr⟩ := simulate_input M input output e eq w T
  have hb : simulationBudget (fun _ => T) w.length ≤ simulationBudget B w.length := by
    unfold simulationBudget
    gcongr
  simp only [Represents, hhalt] at hr
  refine ⟨t, ht.trans hb, ?_, ?_⟩
  · rw [hd]
    simp [Program.compileConfig, hr.1]
  · rw [hd]
    simpa only [hout] using hr.2

theorem decidesBy_with [Fintype K] (L : Language) (B : ℕ → ℕ)
    (h : DecidesIn M input L B) :
    DecidesBy ((tapeProgram M input output e).compileWith eq) L (simulationBudget B) := by
  intro w
  obtain ⟨T, hT, b, hhalt, hL⟩ := h w
  obtain ⟨t, ht, d, hd, hr⟩ := simulate_input M input output e eq w T
  have hb : simulationBudget (fun _ => T) w.length ≤ simulationBudget B w.length := by
    unfold simulationBudget
    gcongr
  refine ⟨t, ht.trans hb, b, ?_, hL⟩
  simp only [Represents, hhalt] at hr
  rw [hd]
  simp [Program.compileConfig, hr.1]

end GroupWL.MachinePrograms.Stacks
