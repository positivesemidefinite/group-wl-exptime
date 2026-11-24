import GroupWL.ComputableCircuitReduction
import GroupWL.ConstructiveTensorSize
import GroupWL.CircuitReductionWords

/-! Explicit polynomial bounds for the executable circuit-reduction output.
All bound expressions use only addition and multiplication of the circuit's
schema parameters; no expanded address cube occurs in these bounds. -/
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

namespace GroupWL.CircuitOutputSize

open SourceLayout CircuitComparisons ConstructiveSourceTensor
open CircuitGroupReduction
variable {T : Type} [FiniteCode T] {r : ℕ} (C : AddressedCircuit.Circuit T r)

local instance : Fintype T := FiniteCode.fintype T

def connectionBound : ℕ := C.edges + C.testCount + r + 4*FiniteCode.size T + 2
def realBound : ℕ := FiniteCode.size T + 2 + connectionBound C
def comparisonBound : ℕ := C.seedCount + 3*connectionBound C
def sourceBound (L : ℕ) : ℕ :=
  4*r*(realBound C + comparisonBound C*(L+1)) + 4*r*comparisonBound C*(L+2)

theorem connection_card_le : Fintype.card (Connection C) ≤ connectionBound C := by
  simpa only [connectionBound,FiniteCode.card_eq_size] using SourceSize.card_connection_le C

theorem real_card_le : Fintype.card (RealType C) ≤ realBound C := by
  rw [SourceSize.card_realType,FiniteCode.card_eq_size]
  exact Nat.add_le_add_left (connection_card_le C) _

theorem comparison_card_le : Fintype.card (Comparison C) ≤ comparisonBound C := by
  rw [SourceSize.card_comparison]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left 3 (connection_card_le C)) _

variable (F : Type) [Field F] (L : ℕ)

theorem block_card_le :
    Fintype.card ((comparisons C F).Block L) ≤ sourceBound C L := by
  refine (SourceSize.card_block_le (comparisons C F) L).trans ?_
  exact Nat.add_le_add
    (Nat.mul_le_mul_left (4*r)
      (Nat.add_le_add (real_card_le C) (Nat.mul_le_mul_right (L+1) (comparison_card_le C))))
    (Nat.mul_le_mul_right (L+2) (Nat.mul_le_mul_left (4*r) (comparison_card_le C)))

theorem readout_card_le :
    Fintype.card ((comparisons C F).Readout L) ≤ sourceBound C L := by
  refine (SourceSize.card_readout_le (comparisons C F) L).trans ?_
  apply Nat.add_le_add
  · exact Nat.mul_le_mul_left (4*r)
      (Nat.add_le_add (real_card_le C) (Nat.mul_le_mul_right (L+1) (comparison_card_le C)))
  · exact Nat.mul_le_mul_right (L+2)
      (Nat.mul_le_mul (by omega : 2*r ≤ 4*r) (comparison_card_le C))

/-- A common bound on the two source index sets yields polynomial bounds
on both padded incidence coordinate spaces. -/
def coordinateInputBound (s q : ℕ) : ℕ :=
  q*(2*s*(s+2)) + q*q*(2*s*(s+2)+2*s*s)

def coordinateOutputBound (s q : ℕ) : ℕ :=
  q*q*(2*s*(s+2)+2*s*s) + coordinateInputBound s q

def tensorInputBound (s q : ℕ) : ℕ :=
  coordinateInputBound s q + coordinateInputBound s q*coordinateOutputBound s q

def tensorWordBound (p s q : ℕ) : ℕ :=
  tensorInputBound s q + coordinateOutputBound s q + 2 +
    tensorInputBound s q * (tensorInputBound s q * (coordinateOutputBound s q * p))

section Uniform
variable {K I J : Type} [Field K] [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J]
  {V : J → Type} [∀j, AddCommGroup (V j)] [∀j, Module K (V j)]
  (A : AffineSystem K I J V) {s q : ℕ}
  (hi : Fintype.card I ≤ s) (hj : Fintype.card J ≤ s)

include hi hj

private theorem vertexBound_le : IncidenceSize.vertexBound A ≤ 2*s*(s+2) := by
  exact Nat.mul_le_mul (by omega : Fintype.card I+Fintype.card J ≤ 2*s)
    (Nat.add_le_add_right hi 2)

private theorem oldOutputBound_le :
    IncidenceSize.oldOutputBound A q ≤ q*q*(2*s*(s+2)+2*s*s) := by
  exact Nat.mul_le_mul_left (q*q) (Nat.add_le_add (vertexBound_le A hi hj)
    (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hi) hj))

theorem coordinateInputBound_le : IncidenceSize.inputBound A q ≤ coordinateInputBound s q :=
  Nat.add_le_add (Nat.mul_le_mul_left q (vertexBound_le A hi hj)) (oldOutputBound_le A hi hj)

theorem coordinateOutputBound_le : IncidenceSize.outputBound A q ≤ coordinateOutputBound s q :=
  Nat.add_le_add (oldOutputBound_le A hi hj) (coordinateInputBound_le A hi hj)

end Uniform

section Actual
variable (p : ℕ) [Fact p.Prime] {n : ℕ} (D : AddressedCircuit.Circuit T (n+3))

local notation "L₀" => wireLength n
local notation "q₀" => Parameters.frameWidth (n+3)
local notation "S₀" => sourceBound D L₀
local notation "Cmp" => comparisons D (ZMod p)
local notation "A₀" => ConstructiveSourceTensor.system Cmp L₀
local notation "R₀" => ConstructiveSourceTensor.radicalCoordinates Cmp L₀
local instance : Fintype ((Cmp).Block L₀) := FiniteCode.fintype _
local instance : Fintype ((Cmp).Readout L₀) := FiniteCode.fintype _
local instance : DecidableEq ((Cmp).Block L₀) := (FiniteCode.equiv (α := (Cmp).Block L₀)).decidableEq
local instance : DecidableEq ((Cmp).Readout L₀) := (FiniteCode.equiv (α := (Cmp).Readout L₀)).decidableEq

private theorem source_block_le : Fintype.card ((Cmp).Block L₀) ≤ S₀ := by
  simpa only [← Nat.card_eq_fintype_card] using block_card_le D (ZMod p) L₀
private theorem source_readout_le : Fintype.card ((Cmp).Readout L₀) ≤ S₀ := by
  simpa only [← Nat.card_eq_fintype_card] using readout_card_le D (ZMod p) L₀

private theorem source_input_le : IncidenceSize.inputBound A₀ q₀ ≤ coordinateInputBound S₀ q₀ :=
  coordinateInputBound_le A₀ (source_block_le p D) (source_readout_le p D)
private theorem source_output_le : IncidenceSize.outputBound A₀ q₀ ≤ coordinateOutputBound S₀ q₀ :=
  coordinateOutputBound_le A₀ (source_block_le p D) (source_readout_le p D)

private theorem description_input_le (hq : 0 < q₀)
    (ε : AlternatingBilinearMap (ZMod p) (IncidenceTensor.PaddedInput A₀ q₀)
      (IncidenceTensor.PaddedOutput A₀ q₀)) :
    (ConstructiveTensor.description q₀ p A₀ R₀ hq ε).inputDimension ≤ tensorInputBound S₀ q₀ :=
  (ConstructiveTensorSize.description_inputDimension_le q₀ p A₀ R₀ hq ε).trans
    (Nat.add_le_add (source_input_le p D)
      (Nat.mul_le_mul (source_input_le p D) (source_output_le p D)))

private theorem description_output_le (hq : 0 < q₀)
    (ε : AlternatingBilinearMap (ZMod p) (IncidenceTensor.PaddedInput A₀ q₀)
      (IncidenceTensor.PaddedOutput A₀ q₀)) :
    (ConstructiveTensor.description q₀ p A₀ R₀ hq ε).outputDimension ≤ coordinateOutputBound S₀ q₀ :=
  (ConstructiveTensorSize.description_outputDimension_le q₀ p A₀ R₀ hq ε).trans (source_output_le p D)

theorem base_input_le : (ComputableCircuitReduction.baseDescription p D).inputDimension ≤
    tensorInputBound S₀ q₀ := description_input_le p D _ _
theorem base_output_le : (ComputableCircuitReduction.baseDescription p D).outputDimension ≤
    coordinateOutputBound S₀ q₀ := description_output_le p D _ _
theorem mate_input_le : (ComputableCircuitReduction.mateDescription p D).inputDimension ≤
    tensorInputBound S₀ q₀ := description_input_le p D _ _
theorem mate_output_le : (ComputableCircuitReduction.mateDescription p D).outputDimension ≤
    coordinateOutputBound S₀ q₀ := description_output_le p D _ _

private theorem word_length_le {U : Statement.TensorDescription p}
    (hx : U.inputDimension ≤ tensorInputBound S₀ q₀)
    (hz : U.outputDimension ≤ coordinateOutputBound S₀ q₀) :
    (U.denseWord p).length ≤ tensorWordBound p S₀ q₀ :=
  (Statement.denseWord_length_le p U).trans
    (Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add hx hz) 2)
      (Nat.mul_le_mul hx (Nat.mul_le_mul hx (Nat.mul_le_mul_right p hz))))

theorem base_word_length_le :
    ((ComputableCircuitReduction.baseDescription p D).denseWord p).length ≤ tensorWordBound p S₀ q₀ :=
  word_length_le p D (base_input_le p D) (base_output_le p D)
theorem mate_word_length_le :
    ((ComputableCircuitReduction.mateDescription p D).denseWord p).length ≤ tensorWordBound p S₀ q₀ :=
  word_length_le p D (mate_input_le p D) (mate_output_le p D)

theorem identification_length_le (v : Refinement.Version) (e : Statement.DimensionEncoding) :
    (ComputableCircuitReduction.identificationOutput p D v e).length ≤
      tensorWordBound p S₀ q₀ + 146*(n+4)^2 := by
  unfold ComputableCircuitReduction.identificationOutput Statement.identificationWord
  rw [List.length_append]
  exact Nat.add_le_add (base_word_length_le p D) (dimensionWord_length_le_quadratic v e (n+3))

theorem equivalence_length_le (v : Refinement.Version) (e : Statement.DimensionEncoding) :
    (ComputableCircuitReduction.equivalenceOutput p D v e).length ≤
      2*tensorWordBound p S₀ q₀ + 146*(n+4)^2 := by
  unfold ComputableCircuitReduction.equivalenceOutput Statement.equivalenceWord
  simp only [List.length_append]
  have h := Nat.add_le_add (Nat.add_le_add (base_word_length_le p D) (mate_word_length_le p D))
    (dimensionWord_length_le_quadratic v e (n+3))
  simpa only [two_mul] using h

end Actual
end GroupWL.CircuitOutputSize
