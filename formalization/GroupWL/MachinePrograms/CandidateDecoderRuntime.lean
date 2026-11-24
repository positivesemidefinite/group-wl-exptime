import GroupWL.MachinePrograms.CandidateDecoderLoop

/-! Uniform polynomial magnitude bound for the complete compact-candidate
runtime, including every generator search and every group-law check. -/
namespace GroupWL.MachinePrograms.CandidateDecoder
open NatArrayLanguage
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192

theorem decode_runs_polynomial {p : ℕ} [Fact p.Prime] (S : State) (M D q : ℕ)
    (hb : S.Bounded M) (hd : S.scalar (.inr .dimension)=D) (hq : S.scalar (.inr .code)=q)
    (hroom : ((p^D)*(p^D))*((p^D)*(p^D))≤M) (hpow : (p^D)^D≤M) (hexp : 2*p≤M) :
    ∃t≤1000*(M+1)^7,∃T,Runs (1000*(M+1)^7) (decode p) S t T ∧ T.Bounded M ∧ Data p D q T ∧
      T.scalar (.inr .order)=p^D ∧ T.scalar (.inr .code)=q/NumericCandidateCodes.radix p D := by
  have hD : D≤M := by simpa [hd] using hb.1 (.inr .dimension)
  have hn : p^D≤M := (Nat.le_mul_self _).trans ((Nat.le_mul_self _).trans hroom)
  have hp : p≤M := by omega
  obtain ⟨t,ht,T,run,hT,hdata,hnT,hqT⟩ := decode_runs S M D q hb hd hq hroom hpow hexp
  have htime := CandidateExtend.decode_time_le hp hn hD hpow
  have hcard : Fintype.card Reg+3*Fintype.card Arr≤1000 := by decide
  have hspace : storageBound Reg Arr M≤1000*(M+1)^7 := by
    calc
      _ ≤1000*(M+1)^2 := Nat.mul_le_mul_right _ hcard
      _ ≤1000*(M+1)^7 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega : 1≤M+1) (by decide))
  exact ⟨t,(ht.trans htime).trans (Nat.mul_le_mul_right _ (by decide : 500≤1000)),T,run.mono hspace,
    hT,hdata,hnT,hqT⟩

end GroupWL.MachinePrograms.CandidateDecoder
