import Mathlib.Tactic

/-! Natural polynomial bounds for finite compositions of register programs. -/
namespace GroupWL.MachinePrograms
def PolynomialBudget (f : ℕ → ℕ) : Prop := ∃ c d : ℕ, ∀ n, f n ≤ c*(n+1)^d

namespace PolynomialBudget
theorem const (a : ℕ) : PolynomialBudget (fun _ => a) := ⟨a,0,by simp⟩
theorem input : PolynomialBudget (fun n => n) := ⟨1,1,by simp⟩

theorem add {f g : ℕ → ℕ} (hf : PolynomialBudget f) (hg : PolynomialBudget g) :
    PolynomialBudget (fun n => f n + g n) := by
  obtain ⟨a,d,hd⟩ := hf
  obtain ⟨b,e,he⟩ := hg
  refine ⟨a+b,max d e,fun n => ?_⟩
  rw [Nat.add_mul]
  exact Nat.add_le_add ((hd n).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (le_max_left d e))))
    ((he n).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (le_max_right d e))))

theorem mul {f g : ℕ → ℕ} (hf : PolynomialBudget f) (hg : PolynomialBudget g) :
    PolynomialBudget (fun n => f n * g n) := by
  obtain ⟨a,d,hd⟩ := hf
  obtain ⟨b,e,he⟩ := hg
  refine ⟨a*b,d+e,fun n => (Nat.mul_le_mul (hd n) (he n)).trans_eq ?_⟩
  rw [pow_add]; ring

theorem pow {f : ℕ → ℕ} (hf : PolynomialBudget f) (d : ℕ) :
    PolynomialBudget (fun n => (f n)^d) := by
  obtain ⟨a,e,he⟩ := hf
  refine ⟨a^d,e*d,fun n => (Nat.pow_le_pow_left (he n) d).trans_eq ?_⟩
  rw [mul_pow,pow_mul]

theorem mono {f g : ℕ → ℕ} (hg : PolynomialBudget g) (h : ∀n, f n ≤ g n) :
    PolynomialBudget f := by
  obtain ⟨c,d,hd⟩ := hg
  exact ⟨c,d,fun n => (h n).trans (hd n)⟩
end PolynomialBudget
end GroupWL.MachinePrograms
