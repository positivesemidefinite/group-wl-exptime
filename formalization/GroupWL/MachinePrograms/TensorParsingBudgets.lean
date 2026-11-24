import GroupWL.MachinePrograms.ValidatedTensorProgram
import GroupWL.MachinePrograms.TensorGroupMaterialize

/-! Explicit single-exponential magnitudes for parsing and tensor group tables. -/
namespace GroupWL.MachinePrograms.TensorParsingBudgets
open NatArrayLanguage

def base (p N : ℕ) : ℕ := 2^((p+1)*(N+1))
def magnitude (p N : ℕ) : ℕ := (base p N)^4

theorem base_positive (p N : ℕ) : 1≤base p N := one_le_pow₀ (by decide)

theorem length_le_base (p N : ℕ) : N+1≤base p N := by
  calc
    N+1 ≤ 2^(N+1) := Nat.le_of_lt Nat.lt_two_pow_self
    _ ≤ _ := pow_le_pow_right' (by decide) (by nlinarith)

theorem field_le_base (p N : ℕ) : p+1≤base p N := by
  calc
    p+1 ≤ 2^(p+1) := Nat.le_of_lt Nat.lt_two_pow_self
    _ ≤ _ := pow_le_pow_right' (by decide) (by nlinarith)

theorem field_power_le_base (p N : ℕ) : p^N≤base p N := by
  calc
    p^N ≤ (2^p)^N := Nat.pow_le_pow_left (Nat.le_of_lt Nat.lt_two_pow_self) _
    _ = 2^(p*N) := (pow_mul ..).symm
    _ ≤ _ := pow_le_pow_right' (by decide) (by nlinarith)

theorem length_cube_le_magnitude (p N : ℕ) : (N+1)^3≤magnitude p N := by
  exact (Nat.pow_le_pow_left (length_le_base p N) _).trans
    (pow_le_pow_right' (base_positive p N) (by decide))

theorem field_room (p N : ℕ) : p^3+3*p≤magnitude p N := by
  have hp := field_le_base p N
  have hb := base_positive p N
  unfold magnitude
  have hc : p^3+3*p≤(p+1)^4 := by nlinarith [sq_nonneg (p*p)]
  exact hc.trans (Nat.pow_le_pow_left hp _)

theorem binary_room (p N : ℕ) : 2^(N+1)≤magnitude p N := by
  calc
    _ ≤ base p N := pow_le_pow_right' (by decide) (by nlinarith)
    _ ≤ _ := by simpa only [magnitude,pow_one] using pow_le_pow_right' (base_positive p N) (by decide : 1≤4)

theorem field_power_room (p N : ℕ) : p^N≤magnitude p N :=
  (field_power_le_base p N).trans (by simpa only [magnitude,pow_one] using pow_le_pow_right' (base_positive p N) (by decide : 1≤4))

theorem table_room (p n m N : ℕ) (dimensions : n+m≤N) :
    (p^(n+m))^2≤magnitude p N := by
  have hp : p^(n+m)≤base p N := by
    calc
      p^(n+m) ≤ (2^p)^(n+m) := Nat.pow_le_pow_left (Nat.le_of_lt Nat.lt_two_pow_self) _
      _ = 2^(p*(n+m)) := (pow_mul ..).symm
      _ ≤ _ := pow_le_pow_right' (by decide) (by nlinarith)
  exact (Nat.pow_le_pow_left hp _).trans (pow_le_pow_right' (base_positive p N) (by decide : 2≤4))

theorem scanCost_le (p N : ℕ) : ValidatedTensorProgram.scanCost p N≤256*(base p N)^4 := by
  let R := base p N
  have hR : 1≤R := base_positive p N
  have hN : N+1≤R := length_le_base p N
  have hP : p^N≤R := field_power_le_base p N
  have hN' : N≤R := by omega
  have h2 : R≤R^2 := by simpa only [pow_one] using pow_le_pow_right' hR (by decide : 1≤2)
  have h3 : R^2≤R^3 := pow_le_pow_right' hR (by decide : 2≤3)
  have h4 : R^3≤R^4 := pow_le_pow_right' hR (by decide : 3≤4)
  have nsquare : N^2≤R^2 := Nat.pow_le_pow_left hN' _
  have header : 14*N^2+9*N+11≤34*R^2 := by nlinarith
  have perVector : N*(14*N^2+9*N+11)+7≤41*R^3 := by
    calc
      _ ≤ R*(34*R^2)+7 := Nat.add_le_add_right (Nat.mul_le_mul hN' header) _
      _ ≤ _ := by nlinarith
  have vector : p^N*(N*(14*N^2+9*N+11)+7)≤41*R^4 := by
    calc
      _ ≤ R*(41*R^3) := Nat.mul_le_mul hP perVector
      _ = _ := by ring
  have parse : (N+1)^3*(7*N+19)≤26*R^4 := by
    calc
      _ ≤ R^3*(26*R) := Nat.mul_le_mul (Nat.pow_le_pow_left hN _) (by omega)
      _ = _ := by ring
  unfold ValidatedTensorProgram.scanCost ValidatedTensorProgram.validationCost
  change _≤256*R^4
  nlinarith

theorem tableCost_le (p n m N : ℕ) (dimensions : n+m≤N) :
    TensorGroupProgram.tableCost p n m≤256*(base p N)^5 := by
  let R := base p N
  have hR : 1≤R := base_positive p N
  have hN : N+1≤R := length_le_base p N
  have hd : n+m≤R := by omega
  have hn : n≤R := by omega
  have hp : p^(n+m)≤R := by
    calc
      p^(n+m) ≤ (2^p)^(n+m) := Nat.pow_le_pow_left (Nat.le_of_lt Nat.lt_two_pow_self) _
      _ = 2^(p*(n+m)) := (pow_mul ..).symm
      _ ≤ _ := pow_le_pow_right' (by decide) (by change p*(n+m)≤(p+1)*(N+1);nlinarith)
  have h2 : R≤R^2 := by simpa only [pow_one] using pow_le_pow_right' hR (by decide : 1≤2)
  have h3 : R^2≤R^3 := pow_le_pow_right' hR (by decide : 2≤3)
  have h5 : R^3≤R^5 := pow_le_pow_right' hR (by decide : 3≤5)
  have nsquare : n^2≤R^2 := Nat.pow_le_pow_left hn _
  have header : 14*n^2+9*n+23≤46*R^2 := by nlinarith
  have perPair : (n+m)*(14*n^2+9*n+23)+15≤61*R^3 := by
    calc
      _ ≤ R*(46*R^2)+15 := Nat.add_le_add_right (Nat.mul_le_mul hd header) _
      _ ≤ _ := by nlinarith
  have pairs : (p^(n+m))^2*((n+m)*(14*n^2+9*n+23)+15)≤61*R^5 := by
    calc
      _ ≤ R^2*(61*R^3) := Nat.mul_le_mul (Nat.pow_le_pow_left hp _) perPair
      _ = _ := by ring
  unfold TensorGroupProgram.tableCost
  change _≤256*R^5
  nlinarith

end GroupWL.MachinePrograms.TensorParsingBudgets
