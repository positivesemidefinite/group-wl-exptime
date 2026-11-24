import GroupWL.MachinePrograms.RawIdentification

/-! Actual one-tape EXPTIME membership for I/II identification. -/
namespace GroupWL.MachinePrograms.RawIdentification
open NatArrayLanguage RawIdentificationTables
set_option maxRecDepth 16000
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 2000000

theorem input_bounded (w : List Bool) (B : ℕ) (hlen : w.length≤B) (one : 1≤B) :
    (NatArrayLowering.inputStore (Reg:=Reg) input w).Bounded B := by
  refine ⟨fun _=>Nat.zero_le _,?_,?_⟩
  · intro a
    by_cases h : a=input
    · subst a;simpa [NatArrayLowering.inputStore] using hlen
    · simp [NatArrayLowering.inputStore,h]
  · intro a x hx
    by_cases h : a=input
    · subst a
      simp only [NatArrayLowering.inputStore,Function.update_self] at hx
      obtain ⟨b,_,rfl⟩ := List.mem_map.mp hx
      cases b <;> simp [NatArrayLowering.bitNat] <;> omega
    · simp [NatArrayLowering.inputStore,h] at hx

theorem inEXPTIME (p : ℕ) [Fact p.Prime] [NeZero (2:ZMod p)]
    (encoding : Statement.DimensionEncoding) (word : Bool) :
    Complexity.InEXPTIME (Statement.identificationLanguage p (version word) encoding) := by
  let K := max 20000 (Fintype.card Reg+3*Fintype.card Arr)
  let c := K+8*(WLExponentialBudgets.coefficient p+1)
  apply NatArrayLowering.inEXPTIME (program p encoding word) input result _ c 4
  intro w
  let B := WLExponentialBudgets.budget p w.length
  have cap := (WLExponentialBudgets.parser_room p w.length).2
  have lengthRoom : w.length≤B := by dsimp [B];omega
  have one : 1≤B := by dsimp [B];omega
  let S : State := NatArrayLowering.inputStore input w
  have hS : S.Bounded B := input_bounded w B lengthRoom one
  obtain ⟨t,ht,T,run,hT,correct⟩ := program_runs p encoding word w S hS
    (by simp [S,NatArrayLowering.inputStore])
  have poly := WLExponentialBudgets.polynomial_bound p w.length K 8
  have time : t≤2^(c*(w.length+1)^4) :=
    ht.trans ((Nat.mul_le_mul_right _ (show 20000≤K from Nat.le_max_left _ _)).trans poly)
  have space : storageBound Reg Arr B≤2^(c*(w.length+1)^4) := by
    have power : (B+1)^2≤(B+1)^8 := pow_le_pow_right' (by omega) (by decide)
    exact (Nat.mul_le_mul (show Fintype.card Reg+3*Fintype.card Arr≤K from Nat.le_max_right _ _) power).trans poly
  exact ⟨storageBound Reg Arr B,t,T,space,time,run,correct⟩

theorem versionI_inEXPTIME (p : ℕ) [Fact p.Prime] [NeZero (2:ZMod p)]
    (encoding : Statement.DimensionEncoding) : Complexity.InEXPTIME (Statement.identificationLanguage p .one encoding) :=
  inEXPTIME p encoding false

theorem versionII_inEXPTIME (p : ℕ) [Fact p.Prime] [NeZero (2:ZMod p)]
    (encoding : Statement.DimensionEncoding) : Complexity.InEXPTIME (Statement.identificationLanguage p .two encoding) :=
  inEXPTIME p encoding true

end GroupWL.MachinePrograms.RawIdentification
