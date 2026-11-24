import GroupWL.ConstructiveTensor
import GroupWL.EvaluationCoordinates
import GroupWL.FrameResponses

set_option maxHeartbeats 1000000

/-! The computable radical coordinates yield the same zero and charged groups
as the scalar-first coordinates used in the mathematical reduction. The
orthogonal-complement construction requires inverse adjoints in this bridge. -/
namespace GroupWL.ConstructiveGroupBridge

open IncidenceTensor IncidenceGroup ConstructiveCoordinates EvaluationCoordinates
open scoped BigOperators

variable {F I J : Type} [Field F] [DecidableEq F]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [FiniteCode I] [FiniteCode J]
variable {V : J → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module F (V j)]
variable (A : AffineSystem F I J V) (R : ∀ j, Coordinates F (ReadoutRadical A j)) (q : ℕ)

noncomputable def inputChange :=
  (IncidenceCoordinates.inputCoordinates A q).symm.trans (ConstructiveIncidence.inputEquiv A R q)

noncomputable def outputChange :=
  (IncidenceCoordinates.outputCoordinates A q).symm.trans (ConstructiveIncidence.outputEquiv A R q)

theorem inputChange_scalarUnit (v : I ⊕ J) (a : Fin q) :
    inputChange A R q (Pi.single (IncidenceCoordinates.scalarIndex A q v a) 1) =
      Pi.single (ConstructiveIncidence.scalarIndex A R q v a) 1 := by
  classical
  simp only [inputChange, LinearEquiv.trans_apply, IncidenceCoordinates.inputCoordinates_symm_scalar]
  exact ConstructiveIncidence.inputEquiv_unit A R q v a

theorem outputChange_chargeCoordinate (hq : 2 ≤ q) (i : I)
    (x : IncidenceCoordinates.OutputIndex A q → F) :
    outputChange A R q x (ConstructiveIncidence.chargeIndex A R q hq i) =
      x (IncidenceCoordinates.chargeIndex A q hq i) := by
  change (((IncidenceCoordinates.outputCoordinates A q).symm x).1.1
      (.inl i) (firstPair q hq)).snd = _
  rw [← IncidenceCoordinates.outputCoordinates_charge, LinearEquiv.apply_symm_apply]

theorem inverseAdjoint_scalar (v : I ⊕ J) (a : Fin q)
    (x : IncidenceCoordinates.InputIndex A q → F) :
    scalarCoordinate A q v a ((ConstructiveIncidence.inputEquiv A R q).symm
      (inverseAdjoint (inputChange A R q) x)) =
      scalarCoordinate A q v a ((IncidenceCoordinates.inputCoordinates A q).symm x) := by
  have hh := inverseAdjoint_coordinate (inputChange A R q)
    (IncidenceCoordinates.scalarIndex A q v a) (ConstructiveIncidence.scalarIndex A R q v a)
    (by
      convert inputChange_scalarUnit A R q v a using 1
      ext j
      by_cases hj : j = ConstructiveIncidence.scalarIndex A R q v a <;>
        simp [Pi.single_apply, hj]) x
  change (((ConstructiveIncidence.inputEquiv A R q).symm _).1 v a).fst =
    (((IncidenceCoordinates.inputCoordinates A q).symm x).1 v a).fst
  rw [← ConstructiveIncidence.inputEquiv_scalar, LinearEquiv.apply_symm_apply,
    ← IncidenceCoordinates.inputCoordinates_scalar, LinearEquiv.apply_symm_apply]
  exact hh

theorem inverseAdjoint_chargeOutput (hq : 2 ≤ q) (i : I) :
    inverseAdjoint (outputChange A R q)
      (IncidenceCoordinates.outputCoordinates A q (chargeOutput A q hq i)) =
      ConstructiveIncidence.outputEquiv A R q (chargeOutput A q hq i) := by
  classical
  rw [IncidenceCoordinates.outputCoordinates_chargeOutput,
    ConstructiveIncidence.outputEquiv_chargeOutput]
  convert inverseAdjoint_single (outputChange A R q) _ _
    (outputChange_chargeCoordinate A R q hq i) using 1
  ext j
  by_cases hj : j = ConstructiveIncidence.chargeIndex A R q hq i <;>
    simp [Pi.single_apply, hj]

theorem chargeTwist_compatible (hq : 2 ≤ q) (β : I → F)
    (x y : IncidenceCoordinates.InputIndex A q → F) :
    twistCoordinates A q (ConstructiveIncidence.inputEquiv A R q)
      (ConstructiveIncidence.outputEquiv A R q) (epsilonCharge A q hq β)
      (inverseAdjoint (inputChange A R q) x) (inverseAdjoint (inputChange A R q) y) =
    inverseAdjoint (outputChange A R q)
      (twistCoordinates A q (IncidenceCoordinates.inputCoordinates A q)
        (IncidenceCoordinates.outputCoordinates A q) (epsilonCharge A q hq β) x y) := by
  change ConstructiveIncidence.outputEquiv A R q (epsilonCharge A q hq β _ _) =
    inverseAdjoint (outputChange A R q)
      (IncidenceCoordinates.outputCoordinates A q (epsilonCharge A q hq β _ _))
  simp only [epsilonCharge_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  simp only [unitCharge, elementaryTensor, LinearMap.mk₂_apply,
    inverseAdjoint_scalar, map_smul, inverseAdjoint_chargeOutput]

noncomputable def zeroGroupEquiv (hq : 2 ≤ q) :
    FrameResponses.ZeroGroup A q hq ≃*
      ConstructedGroup A q (by omega) (ConstructiveIncidence.inputEquiv A R q)
        (ConstructiveIncidence.outputEquiv A R q) AlternatingBilinearMap.zero := by
  unfold FrameResponses.ZeroGroup ConstructedGroup
  rw [coordinateObstruction_change A q (by omega)
    (IncidenceCoordinates.inputCoordinates A q) (IncidenceCoordinates.outputCoordinates A q)
    (ConstructiveIncidence.inputEquiv A R q) (ConstructiveIncidence.outputEquiv A R q)]
  apply EvaluationCoordinates.groupEquiv
  intro x y
  simp [twistCoordinates]

noncomputable def chargedGroupEquiv (hq : 2 ≤ q) (β : I → F) :
    FrameResponses.ChargedGroup A q hq β ≃*
      ConstructedGroup A q (by omega) (ConstructiveIncidence.inputEquiv A R q)
        (ConstructiveIncidence.outputEquiv A R q) (epsilonCharge A q hq β) := by
  unfold FrameResponses.ChargedGroup ConstructedGroup
  rw [coordinateObstruction_change A q (by omega)
    (IncidenceCoordinates.inputCoordinates A q) (IncidenceCoordinates.outputCoordinates A q)
    (ConstructiveIncidence.inputEquiv A R q) (ConstructiveIncidence.outputEquiv A R q)]
  exact EvaluationCoordinates.groupEquiv _ (inputChange A R q) (outputChange A R q)
    _ _ (chargeTwist_compatible A R q hq β)

end GroupWL.ConstructiveGroupBridge
