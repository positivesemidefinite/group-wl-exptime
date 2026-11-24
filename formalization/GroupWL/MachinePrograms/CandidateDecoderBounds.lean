import GroupWL.MachinePrograms.CandidateExtend

namespace GroupWL.MachinePrograms.CandidateExtend

theorem budget_mono {p n N d D : ℕ} (hn : n≤N) (hd : d≤D) (hN : 1≤N) :
    budget p n d≤budget p N D := by
  have hp : n^d≤N^D := (Nat.pow_le_pow_left hn d).trans (Nat.pow_le_pow_right hN hd)
  unfold budget CandidateImages.choiceBudget CandidateImages.imageBudget
  gcongr

theorem budget_le {p n d M : ℕ} (hp : p≤M) (hn : n≤M) (hd : d≤M) (hpow : n^d≤M) :
    budget p n d≤400*(M+1)^6 := by
  let B := M+1
  have hpB : p≤B := by dsimp [B]; omega
  have hnB : n≤B := by dsimp [B]; omega
  have hdB : d≤B := by dsimp [B]; omega
  have hpowB : n^d≤B := by dsimp [B]; omega
  have hB : 1≤B := by dsimp [B]; omega
  have h0 : 1≤B^6 := one_le_pow₀ hB
  have h1 : B≤B^6 := by simpa using Nat.pow_le_pow_right hB (by decide : 1≤6)
  have h2 : B^2≤B^6 := Nat.pow_le_pow_right hB (by decide)
  have h4 : B^4≤B^6 := Nat.pow_le_pow_right hB (by decide)
  have h5 : B^5≤B^6 := Nat.pow_le_pow_right hB (by decide)
  unfold budget CandidateImages.choiceBudget CandidateImages.imageBudget
  calc
    _ ≤ B*(10*B^3+13*B+11*B+35)+9*B+20+6*B+17+
      (10*(B*B)^3+15*((B*B)*(B*B))+8*(B*B)+13*B+B*(9*B+13)+44)+
      (36*(B*B)^3+(B*B)*(B*B)*(4*B+23)+18) := by gcongr
    _ = 46*B^6+4*B^5+48*B^4+41*B^2+76*B+99 := by ring
    _ ≤ 400*B^6 := by omega

theorem decode_time_le {p n D M : ℕ} (hp : p≤M) (hn : n≤M) (hD : D≤M) (hpow : n^D≤M) :
    D*(budget p n D+3*D+20)+9≤500*(M+1)^7 := by
  have hb := budget_le hp hn hD hpow
  let B := M+1
  have hDB : D≤B := by dsimp [B]; omega
  have hB : 1≤B := by dsimp [B]; omega
  have h0 : 1≤B^7 := one_le_pow₀ hB
  have h1 : B≤B^7 := by simpa using Nat.pow_le_pow_right hB (by decide : 1≤7)
  have h2 : B^2≤B^7 := Nat.pow_le_pow_right hB (by decide)
  calc
    _ ≤ B*(400*B^6+3*B+20)+9 := by gcongr
    _ = 400*B^7+3*B^2+20*B+9 := by ring
    _ ≤ 500*B^7 := by omega

end GroupWL.MachinePrograms.CandidateExtend
