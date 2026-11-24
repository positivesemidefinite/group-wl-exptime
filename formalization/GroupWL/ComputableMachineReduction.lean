import GroupWL.ComputableCircuitCorrectness
import GroupWL.MachineReductionSemantics
import GroupWL.CircuitDescription

set_option maxHeartbeats 1000000

/-! Executable per-machine reductions with exact target-language semantics.
Operational polynomial bounds are supplied by the concrete program clients. -/
namespace GroupWL.ComputableMachineReduction

open Complexity Statement Refinement ComputableCircuitReduction
open MachineReduction (circuit circuit_accepts_iff)

variable (p : ℕ) [Fact p.Prime] [NeZero (2 : ZMod p)]

def identificationMap (M : Machine) (c e : ℕ)
    (version : Version) (encoding : DimensionEncoding) (w : BitString) : BitString :=
  identificationOutput p (circuit M c e w) version encoding

def equivalenceMap (M : Machine) (c e : ℕ)
    (version : Version) (encoding : DimensionEncoding) (w : BitString) : BitString :=
  equivalenceOutput p (circuit (complement M) c e w) version encoding

theorem identificationMap_correct (hodd : Odd p) (M : Machine) (L : Language) (c e : ℕ)
    (hM : DecidesBy M L (fun n => 2^(c*(n+1)^e)))
    (version : Version) (encoding : DimensionEncoding) (w : BitString) :
    w ∈ L ↔ identificationMap p M c e version encoding w ∈
      identificationLanguage p version encoding :=
  ((identificationOutput_mem_iff p (circuit M c e w) hodd version encoding).trans
    (circuit_accepts_iff M L c e hM w)).symm

theorem equivalenceMap_correct (hodd : Odd p) (M : Machine) (L : Language) (c e : ℕ)
    (hM : DecidesBy M L (fun n => 2^(c*(n+1)^e)))
    (version : Version) (encoding : DimensionEncoding) (w : BitString) :
    w ∈ L ↔ equivalenceMap p M c e version encoding w ∈
      equivalenceLanguage p version encoding := by
  change w ∈ L ↔ equivalenceOutput p (circuit (complement M) c e w) version encoding ∈ _
  rw [equivalenceOutput_mem_iff p _ hodd version encoding,
    circuit_accepts_iff (complement M) Lᶜ c e hM.complement w]
  simp

theorem identificationMap_hard (M : Machine) (c e : ℕ)
    (version : Version) (encoding : DimensionEncoding) (w : BitString) :
    identificationMap p M c e version encoding w ∈ hardIdentificationInputs p encoding :=
  identificationOutput_hard p (circuit M c e w) version encoding

theorem equivalenceMap_nonisomorphic (M : Machine) (c e : ℕ)
    (version : Version) (encoding : DimensionEncoding) (w : BitString) :
    equivalenceMap p M c e version encoding w ∈ nonisomorphicPairInputs p encoding :=
  equivalenceOutput_nonisomorphic p (circuit (complement M) c e w) version encoding

end GroupWL.ComputableMachineReduction
