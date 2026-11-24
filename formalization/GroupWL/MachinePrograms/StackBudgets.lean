import GroupWL.Operational

/-! Numerical bounds for the proved single-tape simulation overhead. -/
namespace GroupWL.MachinePrograms.Stacks

def simulationBudget (B : ℕ → ℕ) (n : ℕ) : ℕ :=
  2*n + 4 + 3 * B n * (n + B n + 1)

theorem simulationBudget_mono {B C : ℕ → ℕ} (h : ∀ n, B n ≤ C n) (n : ℕ) :
    simulationBudget B n ≤ simulationBudget C n := by
  have hn := h n
  unfold simulationBudget
  exact Nat.add_le_add_left (Nat.mul_le_mul (Nat.mul_le_mul_left 3 (h n)) (by omega)) _

theorem simulationBudget_le_square (B : ℕ → ℕ) (n R : ℕ)
    (hB : B n ≤ R) (hn : n+1 ≤ R) : simulationBudget B n ≤ 10*R^2 := by
  have h1 : 1 ≤ R := by omega
  have hR : R ≤ R^2 := by nlinarith
  have hm : B n * (n + B n + 1) ≤ R * (2*R) :=
    Nat.mul_le_mul hB (by omega)
  unfold simulationBudget
  nlinarith

theorem simulationBudget_polynomial (c d n : ℕ) :
    simulationBudget (fun n => c*(n+1)^d) n ≤
      (10*(c+1)^2) * (n+1)^(2*(d+1)) := by
  have hp : (n+1)^d ≤ (n+1)^(d+1) := pow_le_pow_right' (by omega) (by omega)
  have hn : n+1 ≤ (n+1)^(d+1) := le_self_pow (by omega) (by omega)
  have hB : c*(n+1)^d ≤ (c+1)*(n+1)^(d+1) :=
    Nat.mul_le_mul (by omega) hp
  have hn' : n+1 ≤ (c+1)*(n+1)^(d+1) := by
    calc
      n+1 ≤ (n+1)^(d+1) := hn
      _ ≤ (c+1)*(n+1)^(d+1) := by nlinarith
  have h := simulationBudget_le_square (fun n => c*(n+1)^d) n
    ((c+1)*(n+1)^(d+1)) hB hn'
  convert h using 1 <;> ring

theorem simulationBudget_exponential (c d n : ℕ) :
    simulationBudget (fun n => 2^(c*(n+1)^d)) n ≤
      2^((2*c+6)*(n+1)^(d+1)) := by
  have hp : (n+1)^d ≤ (n+1)^(d+1) := pow_le_pow_right' (by omega) (by omega)
  have hx : n+1 ≤ (n+1)^(d+1) := le_self_pow (by omega) (by omega)
  have he : c*(n+1)^d ≤ (c+1)*(n+1)^(d+1) := Nat.mul_le_mul (by omega) hp
  have he' : n+1 ≤ (c+1)*(n+1)^(d+1) := by nlinarith
  let R := 2^((c+1)*(n+1)^(d+1))
  have hB : 2^(c*(n+1)^d) ≤ R := pow_le_pow_right' (by decide) he
  have hn : n+1 ≤ R :=
    (Nat.le_of_lt (show n+1 < 2^(n+1) from Nat.lt_two_pow_self)).trans
      (pow_le_pow_right' (by decide) he')
  have h := simulationBudget_le_square (fun n => 2^(c*(n+1)^d)) n R hB hn
  have hx1 : 1 ≤ (n+1)^(d+1) := one_le_pow₀ (by omega)
  calc
    simulationBudget (fun n => 2^(c*(n+1)^d)) n ≤ 10*R^2 := h
    _ ≤ 16*R^2 := Nat.mul_le_mul_right _ (by decide)
    _ = 2^(4+2*((c+1)*(n+1)^(d+1))) := by
      rw [pow_add]
      change 16 * (2^((c+1)*(n+1)^(d+1)))^2 =
        16 * 2^(2*((c+1)*(n+1)^(d+1)))
      congr 1
      rw [← pow_mul]
      congr 1
      omega
    _ ≤ 2^((2*c+6)*(n+1)^(d+1)) :=
      pow_le_pow_right' (by decide) (by nlinarith)

end GroupWL.MachinePrograms.Stacks
