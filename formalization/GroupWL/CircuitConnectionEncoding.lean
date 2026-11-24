import GroupWL.CircuitMetadataValues

/-! The numeric connection decoder agrees with canonical constructor codes. -/
namespace GroupWL.CircuitMetadataValues
open CircuitComparisons CircuitComparisonCodes AddressedCircuit MachinePrograms.CircuitRecordParser
variable {T : Type} [FiniteCode T] {r : ℕ} (C : Circuit T r)

def connectionKind : Connection C → ℕ
  | .circuit _=>0 | .test _=>1 | .flip _=>2 | .broadcast _ _=>3 | .identity _ _=>4 | .broadcastIdentity _=>5

def connectionIndex : Connection C → ℕ
  | .circuit i=>i.val | .test i=>i.val | .flip i=>i.val
  | .broadcast t k=>(FiniteCode.equiv (⟨t,k⟩ : gatePorts C)).val
  | .identity t k=>(FiniteCode.equiv (⟨t,k⟩ : gatePorts C)).val
  | .broadcastIdentity b=>if b then 1 else 0

theorem connection_case (e : Connection C) :
    (ofCircuit C).connectionCase (FiniteCode.equiv e).val=(connectionKind C e,connectionIndex C e) := by
  have hp (t : T) (k : Fin (gateDim C t)) : (FiniteCode.equiv (⟨t,k⟩ : gatePorts C)).val<portCount C :=
    (FiniteCode.equiv (⟨t,k⟩ : gatePorts C)).isLt
  cases e with
  | circuit i =>
    simp only [connection_circuit,connectionKind,connectionIndex,Data.connectionCase,ofCircuit]
    split_ifs <;> first | omega | (apply Prod.ext <;> omega)
  | test i =>
    simp only [connection_test,connectionKind,connectionIndex,Data.connectionCase,ofCircuit]
    split_ifs <;> first | omega | (apply Prod.ext <;> omega)
  | flip i =>
    simp only [connection_flip,connectionKind,connectionIndex,Data.connectionCase,ofCircuit]
    split_ifs <;> first | omega | (apply Prod.ext <;> omega)
  | broadcast t k =>
    have hh := hp t k
    simp only [connection_broadcast,connectionKind,connectionIndex,Data.connectionCase,ofCircuit]
    split_ifs <;> first | omega | (apply Prod.ext <;> omega)
  | identity t k =>
    have hh := hp t k
    simp only [connection_identity,connectionKind,connectionIndex,Data.connectionCase,ofCircuit]
    split_ifs <;> first | omega | (apply Prod.ext <;> omega)
  | broadcastIdentity b =>
    simp only [connection_broadcastIdentity,connectionKind,connectionIndex,Data.connectionCase,ofCircuit]
    split_ifs <;> first | omega | (apply Prod.ext <;> omega)

theorem connection_source (e : Connection C) :
    (ofCircuit C).connectionSource (FiniteCode.equiv e).val=(FiniteCode.equiv (e.source C)).val := by
  rw [Data.connectionSource,connection_case]
  cases e with
  | circuit i =>
    simp only [connectionKind,connectionIndex,show 0<2 by decide,↓reduceIte,Data.sourceGate,ofCircuit,Data.schemaStride]
    rw [schema_read_source]
    rfl
  | test i =>
    simp only [connectionKind,connectionIndex,show 1<2 by decide,show ¬(1=0) by decide,↓reduceIte,Data.sourceGate,ofCircuit,Data.requestStride]
    rw [testRecords,request_read_gate C.test i]
    rfl
  | flip i => rfl
  | broadcast t k => rfl
  | identity t k =>
    simp only [connectionKind,connectionIndex,show ¬4<2 by decide,↓reduceIte,ofCircuit]
    rw [packed_read]
    rfl
  | broadcastIdentity b => rfl

theorem connection_target (e : Connection C) :
    (ofCircuit C).connectionTarget (FiniteCode.equiv e).val=(FiniteCode.equiv (e.target C)).val := by
  rw [Data.connectionTarget,connection_case]
  cases e with
  | circuit i =>
    simp only [connectionKind,connectionIndex,↓reduceIte,ofCircuit,Data.schemaStride]
    rw [schema_read_target]
    rfl
  | test i => rfl
  | flip i => rfl
  | broadcast t k =>
    simp only [connectionKind,connectionIndex,show ¬(3=0) by decide,show 3=3 ∨ 3=4 by decide,↓reduceIte,ofCircuit]
    rw [packed_read]
    rfl
  | identity t k =>
    simp only [connectionKind,connectionIndex,show ¬(4=0) by decide,show 4=3 ∨ 4=4 by decide,↓reduceIte,ofCircuit]
    rw [packed_read]
    rfl
  | broadcastIdentity b => rfl

end GroupWL.CircuitMetadataValues
