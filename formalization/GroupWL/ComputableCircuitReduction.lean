import GroupWL.ConstructiveSourceTensor
import GroupWL.CircuitGroupReduction
import GroupWL.InputParsing

/-! Executable circuit-to-group words. Every coordinate choice in these
outputs is made by the proved finite Gaussian algorithm. -/
namespace GroupWL.ComputableCircuitReduction

open AddressedCircuit CircuitComparisons CircuitGroupReduction Statement

variable (p : ℕ) [Fact p.Prime]
variable {T : Type} [FiniteCode T] {n : ℕ} (C : Circuit T (n+3))

def baseDescription : TensorDescription p :=
  ConstructiveSourceTensor.zeroDescription (wireLength n) p (comparisons C (ZMod p))
    (Parameters.frameWidth (n+3)) (by have := frameWidth_ge_two (n+3); omega)

def mateDescription : TensorDescription p :=
  ConstructiveSourceTensor.chargedDescription (wireLength n) p (comparisons C (ZMod p))
    (Parameters.frameWidth (n+3)) (frameWidth_ge_two (n+3))
    ((comparisons C (ZMod p)).sourceShift (rejectingConstant C (ZMod p)))

def identificationOutput (version : Refinement.Version) (encoding : DimensionEncoding) :
    Complexity.BitString :=
  identificationWord p encoding (baseDescription p C) (dimension version (n+3))

def equivalenceOutput (version : Refinement.Version) (encoding : DimensionEncoding) :
    Complexity.BitString :=
  equivalenceWord p encoding (baseDescription p C) (mateDescription p C)
    (dimension version (n+3))

end GroupWL.ComputableCircuitReduction
