import GroupWL.MachinePrograms.RawTableEquivalence
import GroupWL.MachinePrograms.WLExponentialBudgets

/-! Actual one-tape EXPTIME membership for the first two manuscript versions. -/
namespace GroupWL.MachinePrograms.RawTableEquivalence
open NatArrayLanguage TensorPairTables
set_option maxRecDepth 8192
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 2000000

 theorem budget_room (p N : ℕ) : Room p N (WLExponentialBudgets.budget p N) := by
  obtain ⟨parser,cap⟩ := WLExponentialBudgets.parser_room p N
  refine ⟨parser,cap,?_⟩
  intro n m k hn hm hnB hmB hk
  obtain ⟨ln,rn,kc,one,matrix,product,target,pair,arity,width,vectors⟩ := WLExponentialBudgets.room p N n m k hnB hmB hk
  exact ⟨⟨hn,hm,ln,rn,kc,one,by simpa only [pow_two] using matrix⟩,product,
    ⟨by simpa only [pow_two] using matrix,target,pair,arity,width,one,vectors⟩⟩

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
    Complexity.InEXPTIME (Statement.equivalenceLanguage p (version word) encoding) := by
  let K := max 5000 (Fintype.card Reg+3*Fintype.card Arr)
  let c := K+7*(WLExponentialBudgets.coefficient p+1)
  apply NatArrayLowering.inEXPTIME (program p encoding word) input result _ c 4
  intro w
  let B := WLExponentialBudgets.budget p w.length
  have room : Room p w.length B := budget_room p w.length
  have lengthRoom : w.length≤B := by have := room.cap;omega
  have one : 1≤B := by have := room.cap;omega
  let S : State := NatArrayLowering.inputStore input w
  have hS : S.Bounded B := input_bounded w B lengthRoom one
  obtain ⟨t,ht,T,run,hT,correct⟩ := program_runs p encoding word w S B hS room
    (by simp [S,NatArrayLowering.inputStore])
  have poly := WLExponentialBudgets.polynomial_bound p w.length K 7
  have time : t≤2^(c*(w.length+1)^4) := by
    apply ht.trans
    exact (Nat.mul_le_mul_right _ (show 5000≤K from Nat.le_max_left _ _)).trans poly
  have space : storageBound Reg Arr B≤2^(c*(w.length+1)^4) := by
    have power : (B+1)^2≤(B+1)^7 := pow_le_pow_right' (by omega) (by decide)
    exact (Nat.mul_le_mul (show Fintype.card Reg+3*Fintype.card Arr≤K from Nat.le_max_right _ _) power).trans poly
  exact ⟨storageBound Reg Arr B,t,T,space,time,run,correct⟩

theorem versionI_inEXPTIME (p : ℕ) [Fact p.Prime] [NeZero (2:ZMod p)]
    (encoding : Statement.DimensionEncoding) :
    Complexity.InEXPTIME (Statement.equivalenceLanguage p .one encoding) :=
  inEXPTIME p encoding false

theorem versionII_inEXPTIME (p : ℕ) [Fact p.Prime] [NeZero (2:ZMod p)]
    (encoding : Statement.DimensionEncoding) :
    Complexity.InEXPTIME (Statement.equivalenceLanguage p .two encoding) :=
  inEXPTIME p encoding true

end GroupWL.MachinePrograms.RawTableEquivalence
