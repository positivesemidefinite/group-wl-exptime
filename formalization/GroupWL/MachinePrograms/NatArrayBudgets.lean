import GroupWL.MachinePrograms.NatArrayLowering

/-! Explicit polynomial and exponential bounds for encoded natural-array
programs, including input decoding and output encoding. -/
namespace GroupWL.MachinePrograms.NatArrayLowering

def ioBudget (n B T : ℕ) : ℕ := 4*n+2+10000*(B+1)^4*T+4*B

theorem ioBudget_le_common {n B T R : ℕ} (hn : n+1 ≤ R) (hB : B ≤ R) (hT : T ≤ R) :
    ioBudget n B T ≤ 200000*R^5 := by
  have hR : 1 ≤ R := by omega
  have hp : R ≤ R^5 := by
    simpa only [pow_one] using pow_le_pow_right' hR (by decide : 1 ≤ 5)
  have hmain : 10000*(B+1)^4*T ≤ 160000*R^5 := by
    calc
      10000*(B+1)^4*T ≤ 10000*(2*R)^4*R := by gcongr; omega
      _ = 160000*R^5 := by ring
  unfold ioBudget
  nlinarith

theorem ioBudget_le_polynomial {n B T c d : ℕ}
    (hB : B ≤ c*(n+1)^d) (hT : T ≤ c*(n+1)^d) :
    ioBudget n B T ≤ 200000*(c+1)^5*(n+1)^(5*(d+1)) := by
  have hp : 1 ≤ (n+1)^d := one_le_pow₀ (by omega)
  have hn : n+1 ≤ (c+1)*(n+1)^(d+1) := by
    rw [pow_succ]
    nlinarith
  have hs : c*(n+1)^d ≤ (c+1)*(n+1)^(d+1) := by
    rw [pow_succ]
    nlinarith
  have h := ioBudget_le_common hn (hB.trans hs) (hT.trans hs)
  simpa only [mul_pow, ← pow_mul, Nat.mul_comm (d+1) 5, Nat.mul_assoc] using h

theorem ioBudget_le_exponential {n B T c d : ℕ}
    (hB : B ≤ 2^(c*(n+1)^d)) (hT : T ≤ 2^(c*(n+1)^d)) :
    ioBudget n B T ≤ 2^((5*c+23)*(n+1)^(d+1)) := by
  let N := (n+1)^(d+1)
  have hN : 1 ≤ N := one_le_pow₀ (by omega)
  have hp : 1 ≤ (n+1)^d := one_le_pow₀ (by omega)
  have hnN : n+1 ≤ N := by dsimp [N]; rw [pow_succ]; nlinarith
  have hpn : (n+1)^d ≤ N := by
    dsimp [N]
    rw [pow_succ]
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hexp : c*(n+1)^d ≤ (c+1)*N := by nlinarith
  have hn : n+1 ≤ 2^((c+1)*N) :=
    (Nat.le_of_lt (show n+1 < 2^(n+1) from Nat.lt_two_pow_self)).trans
      (pow_le_pow_right' (by decide) (by nlinarith))
  have hs : 2^(c*(n+1)^d) ≤ 2^((c+1)*N) := pow_le_pow_right' (by decide) hexp
  calc
    ioBudget n B T ≤ 200000*(2^((c+1)*N))^5 :=
      ioBudget_le_common hn (hB.trans hs) (hT.trans hs)
    _ ≤ 2^18*(2^((c+1)*N))^5 := Nat.mul_le_mul_right _ (by norm_num)
    _ = 2^(18+((c+1)*N)*5) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2^((5*c+23)*N) := pow_le_pow_right' (by decide) (by nlinarith)

end GroupWL.MachinePrograms.NatArrayLowering
