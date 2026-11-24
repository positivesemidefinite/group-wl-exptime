import GroupWL.CircuitComparisonFields

namespace GroupWL.CircuitMetadataValues
open CircuitComparisons CircuitComparisonCodes AddressedCircuit MachinePrograms.CircuitRecordParser
open MachinePrograms.NatArrayLowering (bitNat)
set_option maxHeartbeats 3000000
variable {T : Type} [FiniteCode T] {r : ℕ} (C : Circuit T r)

theorem sum_decode (j s : ℕ) : ¬s+j*3<s ∧ (s+j*3-s)/3=j ∧ (s+j*3-s)%3=0 := by omega
theorem copy_decode (j s : ℕ) (b : Bool) :
    ¬s+j*3+(if b then 2 else 1)<s ∧
    (s+j*3+(if b then 2 else 1)-s)/3=j ∧
    (s+j*3+(if b then 2 else 1)-s)%3=(if b then 2 else 1) := by
  cases b <;> simp only [Bool.false_eq_true,↓reduceIte] <;> omega

theorem comparison_domain (e : Comparison C) (i : Fin r) (a : Fin 2) :
    (ofCircuit C).domain (FiniteCode.equiv e).val i.val a.val=
      if finTwoEquiv a∈(e.domain C).coordinate i then 1 else 0 := by
  cases e with
  | seed j=>
    simp only [comparison_seed,Data.domain,ofCircuit,if_pos j.isLt,Data.requestStride]
    rw [seedRecords,request_read_domain C.seed j i a]
    simp [Comparison.domain,bitNat]
  | sum e=>
    obtain ⟨hn,hd,hm⟩ := sum_decode (FiniteCode.equiv e).val C.seedCount
    simp only [comparison_sum,Data.domain,show (ofCircuit C).seeds=C.seedCount from rfl,if_neg hn,hd]
    exact connection_domain C e i a
  | copy e b=>
    obtain ⟨hn,hd,hm⟩ := copy_decode (FiniteCode.equiv e).val C.seedCount b
    simp only [comparison_copy,Data.domain,show (ofCircuit C).seeds=C.seedCount from rfl,if_neg hn,hd]
    exact connection_domain C e i a

theorem comparison_permutation (e : Comparison C) (i : Fin r) :
    (ofCircuit C).permutation (FiniteCode.equiv e).val i.val=bitNat (e.permutation C i false) := by
  cases e with
  | seed j=>
    simp only [comparison_seed,Data.permutation,show (ofCircuit C).seeds=C.seedCount from rfl,if_pos j.isLt]
    rfl
  | sum e=>
    obtain ⟨hn,hd,hm⟩ := sum_decode (FiniteCode.equiv e).val C.seedCount
    simp only [comparison_sum,Data.permutation,show (ofCircuit C).seeds=C.seedCount from rfl,if_neg hn,hd,hm,↓reduceIte]
    exact connection_permutation C e i
  | copy e b=>
    obtain ⟨hn,hd,hm⟩ := copy_decode (FiniteCode.equiv e).val C.seedCount b
    simp only [comparison_copy,Data.permutation,show (ofCircuit C).seeds=C.seedCount from rfl,if_neg hn,hm]
    cases b <;> rfl

variable (p : ℕ) [Fact p.Prime]
theorem comparison_sourceForm (e : Comparison C) (k : Fin 2) :
    (ofCircuit C).sourceForm (FiniteCode.equiv e).val k.val=
      (e.sourceForm C (ZMod p) (unit2 (ZMod p) (dimension C (e.source C)) k)).val := by
  cases e with
  | seed j=>
    simp only [comparison_seed,Data.sourceForm,ofCircuit,if_pos j.isLt,Data.requestStride]
    simp only [seedRecords,request_read_gate C.seed j,Option.getD_some]
    exact (gateOutput_unit C p (C.seed j).gate k).symm
  | sum e=>
    obtain ⟨hn,hd,hm⟩ := sum_decode (FiniteCode.equiv e).val C.seedCount
    simp only [comparison_sum,Data.sourceForm,show (ofCircuit C).seeds=C.seedCount from rfl,if_neg hn,hd,hm,↓reduceIte]
    change 1=((if (0:ℕ)=k.val then (1:ZMod p) else 0)+(if (1:ℕ)=k.val then 1 else 0)).val
    have hp : 1<p := (Fact.out : p.Prime).one_lt
    fin_cases k <;> simp [ZMod.val_one,Nat.mod_eq_of_lt hp]
  | copy e b=>
    obtain ⟨hn,hd,hm⟩ := copy_decode (FiniteCode.equiv e).val C.seedCount b
    simp only [comparison_copy,Data.sourceForm,show (ofCircuit C).seeds=C.seedCount from rfl,if_neg hn,hd,hm]
    have hb : ¬(if b then 2 else 1)=0 := by cases b <;> decide
    rw [if_neg hb]
    exact connection_sourceForm C p e k

theorem comparison_targetForm (e : Comparison C) (k : Fin 2) :
    (ofCircuit C).targetForm (FiniteCode.equiv e).val k.val=
      (e.targetForm C (ZMod p) (unit2 (ZMod p) (dimension C (e.target C)) k)).val := by
  cases e with
  | seed j=>
    simp only [comparison_seed,Data.targetForm,show (ofCircuit C).seeds=C.seedCount from rfl,if_pos j.isLt]
    simp [Comparison.targetForm]
  | sum e=>
    obtain ⟨hn,hd,hm⟩ := sum_decode (FiniteCode.equiv e).val C.seedCount
    simp only [comparison_sum,Data.targetForm,show (ofCircuit C).seeds=C.seedCount from rfl,if_neg hn,hd,hm,↓reduceIte]
    exact connection_targetForm C p e k
  | copy e b=>
    obtain ⟨hn,hd,hm⟩ := copy_decode (FiniteCode.equiv e).val C.seedCount b
    simp only [comparison_copy,Data.targetForm,show (ofCircuit C).seeds=C.seedCount from rfl,if_neg hn,hd,hm]
    have hb : ¬(if b then 2 else 1)=0 := by cases b <;> decide
    rw [if_neg hb]
    cases b with
    | false=>exact (proj_unit2 p 2 0 k).symm
    | true=>exact (proj_unit2 p 2 1 k).symm

end GroupWL.CircuitMetadataValues
