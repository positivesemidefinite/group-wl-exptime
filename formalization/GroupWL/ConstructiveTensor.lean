import GroupWL.ConstructiveIncidence
import GroupWL.GeneratedCoordinates
import GroupWL.DenseTensorEncoding

/-! The dense incidence tensor computed from explicit radical coordinates and
finite Gaussian kernels, including the operator orthogonal complement. -/
namespace GroupWL.ConstructiveTensor

open IncidenceTensor IncidenceGroup ConstructiveCoordinates
open ObstructionDuality
variable {F I J : Type} [Field F] [DecidableEq F]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [FiniteCode I] [FiniteCode J]
variable {V : J → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module F (V j)]
variable (A : AffineSystem F I J V) (R : ∀ j, Coordinates F (ReadoutRadical A j)) (q : ℕ)

local notation "XIndex" => ConstructiveIncidence.InputIndex A R q
local notation "ZIndex" => ConstructiveIncidence.OutputIndex A R q

def operatorCoordinateEquiv :
    (PaddedInput A q →ₗ[F] PaddedOutput A q) ≃ₗ[F] MatrixSpace F XIndex ZIndex :=
  ((ConstructiveIncidence.inputEquiv A R q).arrowCongr
    (ConstructiveIncidence.outputEquiv A R q)).trans GeneratedCoordinates.matrixEquiv.symm

theorem operatorCoordinateEquiv_eq : operatorCoordinateEquiv A R q =
    IncidenceGroup.operatorCoordinates A q (ConstructiveIncidence.inputEquiv A R q)
      (ConstructiveIncidence.outputEquiv A R q) := by
  unfold operatorCoordinateEquiv
  rw [GeneratedCoordinates.matrixEquiv_eq]
  rfl

/-- A finite generating map for the actual obstruction matrix space. -/
def obstructionMap (hq : 0 < q) : chosenSpace A q hq →ₗ[F] MatrixSpace F XIndex ZIndex :=
  (operatorCoordinateEquiv A R q).toLinearMap.comp
    ((sliceMap A q).comp (chosenSpace A q hq).subtype)

theorem obstructionMap_range (hq : 0 < q) :
    (obstructionMap A R q hq).range = coordinateObstruction A q hq
      (ConstructiveIncidence.inputEquiv A R q) (ConstructiveIncidence.outputEquiv A R q) := by
  unfold obstructionMap
  rw [LinearMap.range_comp,LinearMap.range_comp,Submodule.range_subtype,
    operatorCoordinateEquiv_eq]
  rfl

def operatorCoordinates (hq : 0 < q) : Coordinates F
    (MatrixEvaluationGroup.operatorSpace (obstructionMap A R q hq).range) :=
  GeneratedCoordinates.operatorCoordinates
    (ConstructiveIncidence.chosenCoordinates A R q hq) (obstructionMap A R q hq)

def groupInputCoordinates (hq : 0 < q) : Coordinates F
    ((XIndex → F) × MatrixEvaluationGroup.operatorSpace (obstructionMap A R q hq).range) :=
  (Coordinates.pi XIndex).prod (operatorCoordinates A R q hq)

def tensor (hq : 0 < q)
    (ε : AlternatingBilinearMap F (PaddedInput A q) (PaddedOutput A q)) :
    AlternatingBilinearMap F
      (Fin (groupInputCoordinates A R q hq).dimension → F)
      (Fin (FiniteCode.size ZIndex) → F) :=
  DenseTensorEncoding.transport
    (evaluationTwist (MatrixEvaluationGroup.operatorSpace (obstructionMap A R q hq).range)
      (twistCoordinates A q (ConstructiveIncidence.inputEquiv A R q)
        (ConstructiveIncidence.outputEquiv A R q) ε))
    (groupInputCoordinates A R q hq).equiv (Coordinates.pi ZIndex).equiv

noncomputable def tensorMulEquiv (hq : 0 < q)
    (ε : AlternatingBilinearMap F (PaddedInput A q) (PaddedOutput A q)) :
    ConstructedGroup A q hq (ConstructiveIncidence.inputEquiv A R q)
      (ConstructiveIncidence.outputEquiv A R q) ε ≃* TensorGroup (tensor A R q hq ε) := by
  let e := DenseTensorEncoding.transportMulEquiv
    (evaluationTwist (MatrixEvaluationGroup.operatorSpace (obstructionMap A R q hq).range)
      (twistCoordinates A q (ConstructiveIncidence.inputEquiv A R q)
        (ConstructiveIncidence.outputEquiv A R q) ε))
    (groupInputCoordinates A R q hq).equiv (Coordinates.pi ZIndex).equiv
  change TensorGroup (evaluationTwist (MatrixEvaluationGroup.operatorSpace
    (coordinateObstruction A q hq (ConstructiveIncidence.inputEquiv A R q)
      (ConstructiveIncidence.outputEquiv A R q)))
    (twistCoordinates A q (ConstructiveIncidence.inputEquiv A R q)
      (ConstructiveIncidence.outputEquiv A R q) ε)) ≃* _
  rw [← obstructionMap_range A R q hq]
  exact e

section Prime
variable (p : ℕ) [Fact p.Prime]
variable {W : J → Type} [∀ j, AddCommGroup (W j)] [∀ j, Module (ZMod p) (W j)]
variable (B : AffineSystem (ZMod p) I J W)
  (S : ∀ j, Coordinates (ZMod p) (ReadoutRadical B j))

def description (hq : 0 < q)
    (ε : AlternatingBilinearMap (ZMod p) (PaddedInput B q) (PaddedOutput B q)) :
    Statement.TensorDescription p where
  inputDimension := (groupInputCoordinates B S q hq).dimension
  outputDimension := FiniteCode.size (ConstructiveIncidence.OutputIndex B S q)
  tensor := tensor B S q hq ε

noncomputable def descriptionMulEquiv (hq : 0 < q)
    (ε : AlternatingBilinearMap (ZMod p) (PaddedInput B q) (PaddedOutput B q)) :
    ConstructedGroup B q hq (ConstructiveIncidence.inputEquiv B S q)
      (ConstructiveIncidence.outputEquiv B S q) ε ≃* (description q p B S hq ε).Carrier :=
  tensorMulEquiv B S q hq ε

end Prime
end GroupWL.ConstructiveTensor
