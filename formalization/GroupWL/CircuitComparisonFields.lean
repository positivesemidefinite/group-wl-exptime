import GroupWL.CircuitConnectionFields

/-! Numeric comparison records agree entrywise with the source comparison system. -/
namespace GroupWL.CircuitMetadataValues
open CircuitComparisons CircuitComparisonCodes AddressedCircuit MachinePrograms.CircuitRecordParser
open MachinePrograms.NatArrayLowering (bitNat)
set_option maxHeartbeats 3000000
variable {T : Type} [FiniteCode T] {r : ℕ} (C : Circuit T r)

theorem real_dimension (t : RealType C) :
    (ofCircuit C).dimension (FiniteCode.equiv t).val=dimension C t := by
  cases t with
  | inl t=>cases t with
    | gate t=>
      simp only [real_primary,primary_gate,Data.dimension,ofCircuit]
      rw [if_pos (FiniteCode.equiv t).isLt,kind_read]
      simp [dimension,primaryDim,gateDim]
      split_ifs <;> rfl
    | broadcast=>simp [Data.dimension,ofCircuit,real_primary,primary_broadcast,dimension,primaryDim]
    | dummy=>simp [Data.dimension,ofCircuit,real_primary,primary_dummy,dimension,primaryDim]
  | inr e=>simp [Data.dimension,ofCircuit,real_buffer,dimension]; omega

theorem comparison_source (e : Comparison C) :
    (ofCircuit C).source (FiniteCode.equiv e).val=(FiniteCode.equiv (e.source C)).val := by
  cases e with
  | seed i=>
    simp only [comparison_seed,Data.source,ofCircuit,if_pos i.isLt,Data.requestStride]
    rw [seedRecords,request_read_gate C.seed i]
    rfl
  | sum e=>
    simp only [comparison_sum,Data.source,ofCircuit,Nat.add_sub_cancel_left]
    rw [if_neg (by omega),Nat.mul_div_left _ (by decide : 0<3)]
    try simp only [Nat.mul_mod,Nat.mod_self,Nat.mul_zero,Nat.zero_mod,↓reduceIte]
    rfl
  | copy e b=>
    rw [comparison_copy,Data.source]
    have hseed : ¬C.seedCount+(FiniteCode.equiv e).val*3+(if b then 2 else 1)<C.seedCount := by omega
    have hd : (C.seedCount+(FiniteCode.equiv e).val*3+(if b then 2 else 1)-C.seedCount)/3=(FiniteCode.equiv e).val := by cases b <;> simp only [Bool.false_eq_true,↓reduceIte] <;> omega
    have hm : ¬(C.seedCount+(FiniteCode.equiv e).val*3+(if b then 2 else 1)-C.seedCount)%3=0 := by cases b <;> simp only [Bool.false_eq_true,↓reduceIte] <;> omega
    change (if C.seedCount+(FiniteCode.equiv e).val*3+(if b then 2 else 1)<C.seedCount then _ else _)=_
    rw [if_neg hseed]
    dsimp only [ofCircuit]
    rw [hd,if_neg hm]
    exact connection_source C e

theorem comparison_target (e : Comparison C) :
    (ofCircuit C).target (FiniteCode.equiv e).val=(FiniteCode.equiv (e.target C)).val := by
  cases e with
  | seed i=>
    simp only [comparison_seed,Data.target,ofCircuit,if_pos i.isLt]
    rfl
  | sum e=>
    rw [comparison_sum,Data.target]
    change (if C.seedCount+(FiniteCode.equiv e).val*3<C.seedCount then _ else _)=_
    rw [if_neg (by omega)]
    dsimp only [ofCircuit]
    simp only [Nat.add_sub_cancel_left,Nat.mul_div_left _ (by decide : 0<3)]
    simp only [Nat.mul_mod,Nat.mod_self,Nat.mul_zero,Nat.zero_mod,↓reduceIte]
    exact connection_target C e
  | copy e b=>
    rw [comparison_copy,Data.target]
    have hseed : ¬C.seedCount+(FiniteCode.equiv e).val*3+(if b then 2 else 1)<C.seedCount := by omega
    have hd : (C.seedCount+(FiniteCode.equiv e).val*3+(if b then 2 else 1)-C.seedCount)/3=(FiniteCode.equiv e).val := by cases b <;> simp only [Bool.false_eq_true,↓reduceIte] <;> omega
    have hm : ¬(C.seedCount+(FiniteCode.equiv e).val*3+(if b then 2 else 1)-C.seedCount)%3=0 := by cases b <;> simp only [Bool.false_eq_true,↓reduceIte] <;> omega
    change (if C.seedCount+(FiniteCode.equiv e).val*3+(if b then 2 else 1)<C.seedCount then _ else _)=_
    rw [if_neg hseed]
    dsimp only [ofCircuit]
    rw [hd,if_neg hm]
    rfl

end GroupWL.CircuitMetadataValues
