import GroupWL.MachinePrograms.CircuitRecordPipelinePacked
import GroupWL.MachinePrograms.CircuitRecordPipelineTables

namespace GroupWL.MachinePrograms.CircuitRecordPipeline.Decode
open NatArrayLanguage AddressedCircuit CircuitComparisonCodes CircuitMetadataValues CircuitDescription
open NatArrayLowering (bitNat)
set_option maxRecDepth 8192
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 1200000

abbrev FirstReg := CircuitParserStages.Reg ⊕ Packed.Reg
abbrev FirstArr := CircuitParserStages.Arr ⊕ Packed.Arr
abbrev Reg := FirstReg ⊕ Packed.Reg
abbrev Arr := FirstArr ⊕ Packed.Arr
abbrev inputArray : Arr := .inl (.inl (CircuitParserStages.ca .input))

def portInput {A : Type} (a : A) (i : Packed.Arr) : Option A :=
  if i=Packed.kindsArray then some a else none

noncomputable def first : NatArrayLanguage.Program FirstReg FirstArr :=
  Ports.thenRun CircuitParserStages.program (fun _=>.literal 0) (portInput (CircuitParserStages.wa .kinds)) (Packed.program .owner)
noncomputable def program : NatArrayLanguage.Program Reg Arr :=
  Ports.thenRun first (fun _=>.literal 0) (portInput (.inl (CircuitParserStages.wa .kinds))) (Packed.program .port)

def initialTime (n : ℕ) := 110*(n+1)^2
def stageTime (n : ℕ) := Fintype.card Packed.Reg + Fintype.card Packed.Arr + Packed.time n
def time (n s : ℕ) := initialTime n + stageTime s + stageTime s

variable {T : Type} [FiniteCode T] {r : ℕ}
structure Output (C : Circuit T r) (S : Store Reg Arr) : Prop where
  parsed : CircuitParserStages.Parsed C S.left.left
  owners : S.left.right.array Packed.output=packed C .owner
  ports : S.right.array Packed.output=packed C .port

theorem program_runs (C : Circuit T r) (S : Store Reg Arr) (M : ℕ) (hs : S.Bounded M)
    (room : 3*(circuitWord C).length+5≤M) (hin : S.array inputArray=(circuitWord C).map bitNat) :
    ∃ t ≤ time (circuitWord C).length (FiniteCode.size T),∃U,
      Runs (storageBound Reg Arr M) program S t U ∧ U.Bounded M ∧ Output C U := by
  have ht := CircuitParserStages.tokenCount_le_length C
  unfold CircuitParserStages.tokenCount at ht
  have gateBound : 2*FiniteCode.size T≤M := by omega
  have low := Packed.chain CircuitParserStages.program (fun _=>.literal 0) (portInput (CircuitParserStages.wa .kinds))
    (Packed.program .owner) S.left M (initialTime (circuitWord C).length) (Packed.time (FiniteCode.size T))
    (CircuitParserStages.Parsed C) (fun P => P.array Packed.output=packed C .owner) hs.left
    (by intro i k h; cases h; omega) ?_ ?_
  · have high := Packed.chain first (fun _=>.literal 0) (portInput (.inl (CircuitParserStages.wa .kinds)))
      (Packed.program .port) S M _ (Packed.time (FiniteCode.size T))
      (fun P => CircuitParserStages.Parsed C P.left ∧ P.right.array Packed.output=packed C .owner)
      (fun P => P.array Packed.output=packed C .port) hs (by intro i k h; cases h; omega) low ?_
    · obtain ⟨t,ht,U,run,b,⟨hp,ho⟩,hv⟩ := high
      exact ⟨t,ht,U,run,b,hp,ho,hv⟩
    · intro P hP hX
      apply Packed.program_runs C .port _ M hX (by omega) gateBound
      simpa [Ports.target,portInput,kinds] using hP.1.kinds
  · obtain ⟨t,ht',P,run,b,hp,_,_⟩ := CircuitParserStages.program_runs_quadratic C S.left.left M hs.left.left room hin
    exact ⟨t,ht',P,run,b,hp⟩
  · intro P hP hX
    apply Packed.program_runs C .owner _ M hX (by omega) gateBound
    simpa [Ports.target,portInput,kinds] using hP.kinds
end GroupWL.MachinePrograms.CircuitRecordPipeline.Decode
