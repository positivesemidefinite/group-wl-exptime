import GroupWL.MachinePrograms.Structured
import GroupWL.MachinePrograms.StackComplexity

/-! Exact one-tape complexity consequences of concrete structured programs. -/
namespace GroupWL.MachinePrograms.Structured

open Complexity

variable {K : Type*} [DecidableEq K] [Fintype K]

theorem computesBy_polynomial (p : Program K) (input output : K)
    (f : BitString → BitString) (c d : ℕ)
    (h : ∀ w, ∃ (S : Store K) (t : ℕ), t ≤ c*(w.length+1)^d ∧
      Runs p (Function.update (fun _ => []) input w.reverse) t S ∧
      (S output).reverse = f w) :
    ComputesBy (Stacks.compiled (compile p true) input output) f
      (fun n => (10*(c+2)^2) * (n+1)^(2*(d+1))) := by
  apply Stacks.computesBy_polynomial (compile p true) input output f (c+1) d
  intro w
  obtain ⟨S, t, ht, hr, ho⟩ := h w
  refine ⟨t+1, ?_, ?_, ?_⟩
  · have hp : 1 ≤ (w.length+1)^d := one_le_pow₀ (by omega)
    nlinarith
  · rw [compile_executes input w hr true]
  · simpa only [compile_executes input w hr true] using ho

theorem inEXPTIME (p : Program K) (input result : K) (test : Option Bool → Bool)
    (L : Language) (c d : ℕ)
    (h : ∀ w, ∃ (S : Store K) (t : ℕ), t ≤ 2^(c*(w.length+1)^d) ∧
      Runs p (Function.update (fun _ => []) input w.reverse) t S ∧
      (test (S result).head? = true ↔ w ∈ L)) : InEXPTIME L := by
  apply Stacks.inEXPTIME (compileTest p result test) input L (c+2) d
  intro w
  obtain ⟨S, t, ht, hr, hL⟩ := h w
  refine ⟨t+2, ?_, test (S result).head?, ?_, hL⟩
  · have hp : 1 ≤ (w.length+1)^d := one_le_pow₀ (by omega)
    have hpow : 1 ≤ 2^(c*(w.length+1)^d) := one_le_pow₀ (by decide)
    calc
      t+2 ≤ 4 * 2^(c*(w.length+1)^d) := by omega
      _ = 2^(c*(w.length+1)^d+2) := by rw [pow_add]; ring
      _ ≤ 2^((c+2)*(w.length+1)^d) := pow_le_pow_right' (by decide) (by nlinarith)
  · rw [compileTest_executes input w hr result test]

end GroupWL.MachinePrograms.Structured
