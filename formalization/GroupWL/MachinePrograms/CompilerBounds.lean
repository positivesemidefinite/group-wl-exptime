import GroupWL.MachinePrograms.CompilerStreams

/-! Polynomial bounds for the actual compiler's primitive instruction counts. -/
namespace GroupWL.MachinePrograms.Structured

open CellularTableau MachineCellular Complexity

def setupCoefficient (c e : ℕ) := (28*e+9*c+22)*2^(e+1)+7

theorem setupSteps_le (n c e : ℕ) :
    setupSteps n c e ≤ setupCoefficient c e*(n+1)^(e+1) := by
  let P := (n+1)^(e+1)
  have hP : 1 ≤ P := Nat.one_le_pow _ _ (by omega)
  have hn : n ≤ P := (by omega : n ≤ n+1).trans (Nat.le_pow (by omega))
  have he : (n+1)^e ≤ P := Nat.pow_le_pow_right (by omega) (by omega)
  have hbase : (n+2)^(e+1) ≤ 2^(e+1)*P := by
    simpa only [Nat.mul_pow,P] using Nat.pow_le_pow_left (by omega : n+2 ≤ 2*(n+1)) (e+1)
  have hdim := (dimensionSteps_le n c e).trans (Nat.mul_le_mul_left (28*e+9*c+22) hbase)
  dsimp [setupSteps,setupCoefficient]
  change 3*n+1+dimensionSteps n c e+(2*(n+1)^e+1) ≤ ((28*e+9*c+22)*2^(e+1)+7)*P
  nlinarith

theorem compilerSeedBound_le (M : Machine) (n d : ℕ) :
    compilerSeedBound M n d ≤ (2*FiniteCode.size (Gate (Cell M))+700)*(n+d+2)^3 := by
  let B := n+d+2
  let N := FiniteCode.size (Gate (Cell M))
  have hB : 1 ≤ B := by dsimp [B]; omega
  have h12 : B ≤ B^2 := by nlinarith
  have h23 : B^2 ≤ B^3 := by nlinarith [Nat.mul_le_mul_left B h12]
  have h13 : B ≤ B^3 := h12.trans h23
  have h03 : 1 ≤ B^3 := hB.trans h13
  have hn : n+1 ≤ B := by dsimp [B]; omega
  have hnd : n+d+1 ≤ B := by dsimp [B]; omega
  have first : (n+1)*(N+260*(n+d+1)^2) ≤ (N+260)*B^3 := by
    calc
      _ ≤ B*(N+260*B^2) := Nat.mul_le_mul hn
        (Nat.add_le_add_left (Nat.mul_le_mul_left 260 (Nat.pow_le_pow_left hnd 2)) N)
      _ ≤ _ := by nlinarith [Nat.mul_le_mul_left N h13]
  have hrest : (N+400)*B^2+9*n+6 ≤ (N+415)*B^3 := by
    have hmain := Nat.mul_le_mul_left (N+400) h23
    have hn3 : n ≤ B^3 := (by omega : n ≤ B).trans h13
    nlinarith
  change (n+1)*(N+260*(n+d+1)^2)+((N+400)*B^2+9*n+6) ≤ (2*N+700)*B^3
  nlinarith

theorem compilerTestBound_le (M : Machine) (n d : ℕ) :
    FiniteCode.size (Symbol M.workSymbols)*(FiniteCode.size (Gate (Cell M))+22*d+6) ≤
      FiniteCode.size (Symbol M.workSymbols)*(FiniteCode.size (Gate (Cell M))+28)*(n+d+2)^3 := by
  let B := n+d+2
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hB3 : B ≤ B^3 := by nlinarith [Nat.mul_le_mul_left B (show B ≤ B^2 by nlinarith)]
  have hd : d ≤ B^3 := (by dsimp [B]; omega : d ≤ B).trans hB3
  have h1 : 1 ≤ B^3 := hB.trans hB3
  have hN := Nat.mul_le_mul_left (FiniteCode.size (Gate (Cell M))) h1
  have h : FiniteCode.size (Gate (Cell M))+22*d+6 ≤
      (FiniteCode.size (Gate (Cell M))+28)*B^3 := by nlinarith
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (FiniteCode.size (Symbol M.workSymbols)) h

theorem compilerBudget_le (n c e : ℕ) :
    n+MachineCircuit.addressBits c e n+2 ≤ (c+6)*(n+1)^(e+1) := by
  have hd := MachineCircuit.addressBits_polynomial c e n
  have hn : n+1 ≤ (n+1)^(e+1) := Nat.le_pow (by omega)
  have hp : 1 ≤ (n+1)^(e+1) := Nat.one_le_pow _ _ (by omega)
  nlinarith

theorem compilerInput_lt (n c e : ℕ) : n+1 < 2^(MachineCircuit.addressBits c e n) := by
  have hnd : n+1 < MachineCircuit.addressBits c e n := by
    simp only [MachineCircuit.addressBits]
    omega
  exact hnd.trans Nat.lt_two_pow_self

end GroupWL.MachinePrograms.Structured
