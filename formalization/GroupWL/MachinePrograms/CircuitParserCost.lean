import GroupWL.MachinePrograms.CircuitParserProgram

/-! The parser's actual execution bound is quadratic in its input word length. -/
namespace GroupWL.MachinePrograms.CircuitParserStages
open NatArrayLanguage CircuitRecordParser AddressedCircuit CircuitDescription
open NatArrayLowering (bitNat)
variable {T : Type*} [FiniteCode T] {r : ℕ}

theorem tokens_length_le_stream (xs : List Token) : xs.length≤(stream xs).length := by
  induction xs with
  | nil => simp [stream]
  | cons x xs ih =>
    have hx : 1≤x.word.length := by cases x <;> simp [Token.word,natWord]
    simpa only [List.length_cons,stream,List.flatMap_cons,List.length_append,Nat.add_comm] using
      Nat.add_le_add hx ih

theorem tokenCount_le_length (C : Circuit T r) : tokenCount C≤(circuitWord C).length := by
  have h₀ := tokens_length_le_stream (headerTokens C)
  have h₁ := tokens_length_le_stream (kindTokens C)
  have h₂ := tokens_length_le_stream (schemaRecords C)
  have h₃ := tokens_length_le_stream (seedRecords C)
  have h₄ := tokens_length_le_stream (testRecords C)
  rw [headerTokens_length,headerTokens_stream] at h₀
  rw [kindTokens_length,kindTokens_stream] at h₁
  have sl : (schemaRecords C).length=C.edges*(3+3*r) := by simp [schemaRecords,records]; omega
  have sel : (seedRecords C).length=C.seedCount*(1+2*r) := by simp [seedRecords,records]
  have tl : (testRecords C).length=C.testCount*(1+2*r) := by simp [testRecords,records]
  rw [sl] at h₂
  rw [sel] at h₃
  rw [tl] at h₄
  rw [circuitWord_records]
  simp only [List.length_append,tokenCount]
  omega

theorem coordinate_le_length (C : Circuit T r) : r≤(circuitWord C).length := by
  simp only [circuitWord,List.length_append,length_natWord]
  omega

theorem budget_of_length (C : Circuit T r) (M : ℕ)
    (hM : 3*(circuitWord C).length+5≤M) : Budget C M := by
  have ht := tokenCount_le_length C
  have hr := coordinate_le_length C
  unfold tokenCount at ht
  constructor <;> omega

theorem program_runs_quadratic (C : Circuit T r) (S : State) (M : ℕ)
    (bounded : S.Bounded M) (room : 3*(circuitWord C).length+5≤M)
    (input : S.array (ca .input)=(circuitWord C).map bitNat) :
    ∃t≤110*((circuitWord C).length+1)^2,∃U,
      Runs (storageBound Reg Arr M) program S t U ∧ U.Bounded M ∧
      Parsed C U ∧ Ready (circuitWord C) U ∧
      (circuitWord C).drop (U.scalar (cr .cursor))=[] := by
  obtain ⟨t,ht,U,run,hU,out,ready,rest⟩ := program_runs C S M bounded (budget_of_length C M room) input
  refine ⟨t,?_,U,run,hU,out,ready,rest⟩
  have hc := tokenCount_le_length C
  have hm := Nat.mul_le_mul_right (7*(circuitWord C).length+18) hc
  nlinarith

end GroupWL.MachinePrograms.CircuitParserStages
