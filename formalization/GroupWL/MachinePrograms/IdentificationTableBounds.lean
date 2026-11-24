import GroupWL.MachinePrograms.IdentificationTableClient

namespace GroupWL.MachinePrograms.IdentificationTableClient
set_option maxHeartbeats 1500000

theorem cost_le {p D B : ℕ} (hp : p ≤ B) (hD : D ≤ B) (hn : p^D ≤ B)
    (hpow : (p^D)^D ≤ B) (hcount : p^(D^3) ≤ B) (hcube : D^3 ≤ B) :
    cost p D B ≤ 5000*(B+1)^8 := by
  have hdec := CandidateExtend.decode_time_le hp hn hD hpow
  have hiso := IsomorphismClient.time_le hn hn hD hpow
  change IdentificationCandidate.isoCost (p^D) D ≤ 200*(B+1)^7 at hiso
  have hcand : IdentificationCandidate.cost p D ≤ 720*(B+1)^7 := by
    unfold IdentificationCandidate.cost
    have h1 : 1 ≤ (B+1)^7 := one_le_pow₀ (by omega)
    omega
  have htest : IdentificationTest.testCost p D B+9 ≤ 1800*(B+1)^7 := by
    unfold IdentificationTest.testCost IdentificationTest.wlCost
    have h1 : 1 ≤ (B+1)^7 := one_le_pow₀ (by omega)
    omega
  have hgen : (p^D)^D*(10*(p^D)^3+13*(p^D)+11*D+35)+9*D+25 ≤ 103*(B+1)^4 := by
    have h1 : 1 ≤ B+1 := by omega
    have h0 : 1 ≤ (B+1)^4 := one_le_pow₀ h1
    have hB : B+1 ≤ (B+1)^4 := by simpa using Nat.pow_le_pow_right h1 (by decide : 1 ≤ 4)
    have hB2 : (B+1)^2 ≤ (B+1)^4 := Nat.pow_le_pow_right h1 (by decide)
    calc
      _ ≤ (B+1)*(10*(B+1)^3+13*(B+1)+11*(B+1)+35)+9*(B+1)+25 := by gcongr <;> omega
      _ = 10*(B+1)^4+24*(B+1)^2+44*(B+1)+25 := by ring
      _ ≤ 103*(B+1)^4 := by omega
  have henum : IdentificationEnumeration.cost p D B ≤ 1820*(B+1)^8 := by
    have hm := Nat.mul_le_mul hcount htest
    have h1 : 1 ≤ B+1 := by omega
    have h0 : 1 ≤ (B+1)^8 := one_le_pow₀ h1
    have hB : B+1 ≤ (B+1)^8 := by simpa using Nat.pow_le_pow_right h1 (by decide : 1 ≤ 8)
    have heq : (B+1)*(1800*(B+1)^7)=1800*(B+1)^8 := by ring
    unfold IdentificationEnumeration.cost
    nlinarith
  have h48 : (B+1)^4 ≤ (B+1)^8 := Nat.pow_le_pow_right (by omega) (by decide)
  unfold cost
  omega
end GroupWL.MachinePrograms.IdentificationTableClient
