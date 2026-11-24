import GroupWL.MachinePrograms.CircuitTensorPipelineInterface
import GroupWL.CircuitComparisonCodes

namespace GroupWL.MachinePrograms.CircuitTensorPipeline
open NatArrayLanguage CircuitComparisons CircuitGroupReduction AddressedCircuit
set_option synthInstance.maxSize 65536
set_option maxRecDepth 16384
set_option quotPrecheck false
variable {R A : Type} (f : FrontPorts R A) {X : Type} [FiniteCode X] {n : ℕ}
  (C : Circuit X (n+3)) (p : ℕ) [Fact p.Prime] (v : Refinement.Version)

local notation "D" => comparisons C (ZMod p)
local notation "L" => wireLength n
local notation "q" => Parameters.frameWidth (n+3)
local notation "β" => ((comparisons C (ZMod p)).sourceShift (rejectingConstant C (ZMod p)) : (comparisons C (ZMod p)).Block (wireLength n) → ZMod p)

structure CircuitRecords (S : Store R A) : Prop extends HeaderPorts.Written f p D L q S where
  dim : S.scalar f.dimension=dimension v (n+3)
  charge : S.array f.charge=ChargedWriter.chargeWord p β

theorem circuitRecords_of_layout (S : Store R A) (W : LayoutRecordPrograms.State)
    (out : LayoutRecordPrograms.Output (ComparisonMetadata.ofComparison p D) L
      (FiniteCode.size (Comparison C)-3) W)
    (coefficients : ∀ a,S.array (f.coefficients a)=W.array (LayoutRecordPrograms.coefficientArray a))
    (dims : S.array f.readouts=W.array LayoutRecordPrograms.dimensionArray)
    (charge : S.array f.charge=W.array LayoutRecordPrograms.chargeArray)
    (horizontal : S.scalar f.horizontal=W.scalar (LayoutRecordPrograms.oldr (LayoutIncidencePrograms.hreg .count)))
    (frames : S.scalar f.frames=q) (dim : S.scalar f.dimension=dimension v (n+3)) :
    CircuitRecords f C p v S := by
  have hc : S.array f.charge=ChargedWriter.chargeWord p β :=
    charge.trans (out.rejecting_charge p L C)
  exact {
    coefficients := fun a => (coefficients a).trans (out.coefficients p D L _ a)
    readouts := dims.trans (out.dimension_correct p D L _)
    blocks := by rw [hc]; exact List.length_ofFn
    horizontal := horizontal.trans (out.forms.incidence.metadata.ranks.horizontalCount.trans
      (LayoutMetadata.horizontalCount_correct p D L))
    frames := frames
    dim := dim
    charge := hc }

end GroupWL.MachinePrograms.CircuitTensorPipeline
