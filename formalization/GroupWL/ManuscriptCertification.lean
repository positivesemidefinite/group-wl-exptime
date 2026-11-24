import GroupWL.Completeness
import GroupWL.MachinePrograms.CircuitTensorPipelineBounded

/-! The full dense-input group Weisfeiler–Leman complexity theorem. -/
namespace GroupWL.Statement
open MachinePrograms.CircuitWriterReduction
open MachinePrograms.CircuitTensorPipeline

/-- For each odd prime, identification and equivalence are EXPTIME-complete
in all three versions and both dimension encodings, with the stated output
restrictions on the polynomial-time many-one reductions. -/
theorem manuscriptClaim_proved : ManuscriptClaim := by
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  intro odd
  apply fullClaim_of_writers p hp odd
  intro v enc
  let writer := writerOfArrays p v (program p v) input output (coefficient p) degree (canonical_run p v)
  exact ⟨⟨writer .identification enc⟩,⟨writer .equivalence enc⟩⟩

end GroupWL.Statement
