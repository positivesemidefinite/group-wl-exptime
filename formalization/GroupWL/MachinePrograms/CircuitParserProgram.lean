import GroupWL.MachinePrograms.CircuitParserSections

/-! A single fixed array program decodes the canonical addressed-circuit word.
All loops inspect the input word; the theorem includes their instruction count. -/
namespace GroupWL.MachinePrograms.CircuitParserStages
open NatArrayLanguage CircuitRecordParser AddressedCircuit CircuitDescription
open NatArrayLowering (bitNat)
set_option maxHeartbeats 4000000
variable {T : Type*} [FiniteCode T] {r : ℕ}

def program : Code := .seq opening
  (.seq (sectionCode kindAtoms .kinds)
    (.seq (sectionCode schemaAtoms .schemas)
      (.seq (sectionCode (requestAtoms .seeds) .seeds)
        (sectionCode (requestAtoms .tests) .tests))))

structure Parsed (C : Circuit T r) (S : State) : Prop where
  metadata : Metadata C S
  header : S.array (wa .header)=List.ofFn (headerValues C)
  kinds : S.array (wa .kinds)=(kindWord C).map bitNat
  schemas : S.array (wa .schemas)=(schemaRecords C).map Token.value
  seeds : S.array (wa .seeds)=(seedRecords C).map Token.value
  tests : S.array (wa .tests)=(testRecords C).map Token.value

def tokenCount (C : Circuit T r) : ℕ :=
  5+FiniteCode.size T+C.edges*(3+3*r)+C.seedCount*(1+2*r)+C.testCount*(1+2*r)

theorem program_runs (C : Circuit T r) (S : State) (M : ℕ)
    (bounded : S.Bounded M) (budget : Budget C M)
    (input : S.array (ca .input)=(circuitWord C).map bitNat) :
    ∃t≤tokenCount C*(7*(circuitWord C).length+18)+85,∃U,
      Runs (storageBound Reg Arr M) program S t U ∧ U.Bounded M ∧
      Parsed C U ∧ Ready (circuitWord C) U ∧
      (circuitWord C).drop (U.scalar (cr .cursor))=[] := by
  have room : 1≤M := by have h := budget.room; omega
  have sl : (schemaRecords C).length=C.edges*(3+3*r) := by
    simp [schemaRecords,records]; congr 1; omega
  have sel : (seedRecords C).length=C.seedCount*(1+2*r) := by simp [seedRecords,records]
  have tl : (testRecords C).length=C.testCount*(1+2*r) := by simp [testRecords,records]
  obtain ⟨t₀,ht₀,U₀,run₀,b₀,ready₀,data₀,header₀,rest₀⟩ := opening_runs C S M bounded budget.room input
  obtain ⟨v₁,s₁,u₁,c₁⟩ := kind_prepared C U₀ M data₀
  obtain ⟨t₁,ht₁,U₁,run₁,b₁,ready₁,data₁,out₁,rest₁,frame₁⟩ :=
    section_runs C kindAtoms .kinds (kindTokens C) (circuitWord C)
      (stream (schemaRecords C)++stream (seedRecords C)++stream (testRecords C))
      M (FiniteCode.size T) 0 U₀ b₀ room ready₀ data₀ kind_pure v₁ s₁ u₁
      (by simpa using c₁)
      (by rw [kindTokens_stream]; simpa only [List.append_assoc] using rest₀)
      (by simp) (kindTokens_kind C)
  obtain ⟨v₂,s₂,u₂,c₂⟩ := schema_prepared C (circuitWord C) U₁ M data₁ ready₁ budget
  obtain ⟨t₂,ht₂,U₂,run₂,b₂,ready₂,data₂,out₂,rest₂,frame₂⟩ :=
    section_runs C schemaAtoms .schemas (schemaRecords C) (circuitWord C)
      (stream (seedRecords C)++stream (testRecords C)) M (3+3*r) 2 U₁ b₁ room ready₁ data₁
      schema_pure v₂ s₂ u₂ (by rwa [sl])
      (by simpa only [List.append_assoc] using rest₁) (by omega)
      (fun i => by simpa only [show 2+(1+3*r)=3+3*r by omega] using
        records_kind (fun i => schemaValues (C.schema i)) (fun i => schemaBits (C.schema i)) i)
  obtain ⟨v₃,s₃,u₃,c₃⟩ := request_prepared C (circuitWord C) U₂ M C.seedCount .seeds
    data₂.seeds (by decide) data₂ ready₂ budget budget.seeds
  obtain ⟨t₃,ht₃,U₃,run₃,b₃,ready₃,data₃,out₃,rest₃,frame₃⟩ :=
    section_runs C (requestAtoms .seeds) .seeds (seedRecords C) (circuitWord C)
      (stream (testRecords C)) M (1+2*r) 1 U₂ b₂ room ready₂ data₂
      (request_pure .seeds) v₃ s₃ u₃ (by rwa [sel]) rest₂ (by omega)
      (records_kind (fun i => requestValues (C.seed i)) (fun i => requestBits (C.seed i)))
  obtain ⟨v₄,s₄,u₄,c₄⟩ := request_prepared C (circuitWord C) U₃ M C.testCount .tests
    data₃.tests (by decide) data₃ ready₃ budget budget.tests
  obtain ⟨t₄,ht₄,U₄,run₄,b₄,ready₄,data₄,out₄,rest₄,frame₄⟩ :=
    section_runs C (requestAtoms .tests) .tests (testRecords C) (circuitWord C)
      [] M (1+2*r) 1 U₃ b₃ room ready₃ data₃
      (request_pure .tests) v₄ s₄ u₄ (by rwa [tl])
      (by simpa only [List.append_nil] using rest₃) (by omega)
      (records_kind (fun i => requestValues (C.test i)) (fun i => requestBits (C.test i)))
  refine ⟨t₀+(t₁+(t₂+(t₃+t₄))),?_,U₄,.seq run₀ (.seq run₁ (.seq run₂ (.seq run₃ run₄))),
    b₄,?_,ready₄,rest₄⟩
  · simp only [kindTokens_length,sl,sel,tl,kindAtoms,schemaAtoms,requestAtoms,List.length_cons,List.length_nil] at ht₁ ht₂ ht₃ ht₄
    unfold tokenCount
    nlinarith
  · refine ⟨data₄,?_,?_,?_,?_,out₄⟩
    · rw [frame₄ .header (by decide),frame₃ .header (by decide),frame₂ .header (by decide),frame₁ .header (by decide)]
      exact header₀
    · rw [frame₄ .kinds (by decide),frame₃ .kinds (by decide),frame₂ .kinds (by decide)]
      exact out₁.trans (kindTokens_values C)
    · rw [frame₄ .schemas (by decide),frame₃ .schemas (by decide)]
      exact out₂
    · rw [frame₄ .seeds (by decide)]
      exact out₃

end GroupWL.MachinePrograms.CircuitParserStages
