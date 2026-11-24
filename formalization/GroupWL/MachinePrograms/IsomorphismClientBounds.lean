import GroupWL.MachinePrograms.IsomorphismClient

namespace GroupWL.MachinePrograms.IsomorphismClient
open NatArrayLanguage
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192

theorem time_le {n m k M : ℕ} (hn : n≤M) (hm : m≤M) (hk : k≤M) (hpow : m^k≤M) :
    m^k*(10*(n*m)^3+8*(n*m)+19*k+n*(9*m+13)+19*n*n+49)+15*((n*m)*(n*m))+3*k+34≤
      200*(M+1)^7 := by
  let B := M+1
  have hnB : n≤B := by dsimp [B]; omega
  have hmB : m≤B := by dsimp [B]; omega
  have hkB : k≤B := by dsimp [B]; omega
  have hpB : m^k≤B := by dsimp [B]; omega
  have hB : 1≤B := by dsimp [B]; omega
  have h0 : 1≤B^7 := one_le_pow₀ hB
  have h1 : B≤B^7 := by simpa using Nat.pow_le_pow_right hB (by decide : 1≤7)
  have h2 : B^2≤B^7 := Nat.pow_le_pow_right hB (by decide)
  have h3 : B^3≤B^7 := Nat.pow_le_pow_right hB (by decide)
  have h4 : B^4≤B^7 := Nat.pow_le_pow_right hB (by decide)
  calc
    _ ≤ B*(10*(B*B)^3+8*(B*B)+19*B+B*(9*B+13)+19*B*B+49)+15*((B*B)*(B*B))+3*B+34 := by gcongr
    _ = 10*B^7+15*B^4+36*B^3+32*B^2+52*B+34 := by ring
    _ ≤ 200*B^7 := by omega

theorem storage_le (M : ℕ) : storageBound Reg Arr M≤1000*(M+1)^7 := by
  have hc : Fintype.card Reg+3*Fintype.card Arr≤1000 := by decide
  calc
    _ ≤1000*(M+1)^2 := Nat.mul_le_mul_right _ hc
    _ ≤1000*(M+1)^7 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega : 1≤M+1) (by decide))

variable {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H]

theorem compare_correct_polynomial {n m k : ℕ} (eG : Fin n≃G) (eH : Fin m≃H)
    (op : Fin n→Fin n→Fin n) (op' : Fin m→Fin m→Fin m)
    (hop : ∀x y,eG (op x y)=eG x*eG y) (hop' : ∀x y,eH (op' x y)=eH x*eH y)
    (identity : Fin n) (identity' : Fin m) (hid : eG identity=1) (hid' : eH identity'=1)
    (a : Fin k→Fin n) (haGen : Refinement.Generates (eG ∘ a)) (hnm : n=m)
    (S : State) (M : ℕ) (hb : S.Bounded M) (hn : S.scalar (.inl 0)=n) (hm : S.scalar (.inl 1)=m)
    (hk : S.scalar (decoderReg .arity)=k)
    (hi : S.scalar identityReg=identity.val) (hi' : S.scalar identityReg'=identity'.val)
    (hs : S.array (.inl 0)=GroupInitial.tableWord op) (ht : S.array (.inl 1)=GroupInitial.tableWord op')
    (ha : S.array sourceTuple=GroupInitial.tupleWord a)
    (hroom : (n*m)*(n*m)≤M) (hpow : m^k≤M) :
    ∃t≤1000*(M+1)^7,∃T,Runs (1000*(M+1)^7) compare S t T ∧ T.Bounded M ∧
      T.scalar resultReg≤1 ∧ (T.scalar resultReg=1 ↔ Nonempty (G≃*H)) := by
  have hnM : n≤M := by simpa [hn] using hb.1 (.inl 0)
  have hmM : m≤M := by simpa [hm] using hb.1 (.inl 1)
  have hkM : k≤M := by simpa [hk] using hb.1 (decoderReg .arity)
  obtain ⟨t,htime,T,run,hT,hbit,hcorrect⟩ := compare_correct eG eH op op' hop hop' identity identity' hid hid' a haGen hnm
    S M hb hn hm hk hi hi' hs ht ha hroom hpow
  exact ⟨t,(htime.trans (time_le hnM hmM hkM hpow)).trans
    (Nat.mul_le_mul_right _ (by decide : 200≤1000)),T,run.mono (storage_le M),hT,hbit,hcorrect⟩

end GroupWL.MachinePrograms.IsomorphismClient
