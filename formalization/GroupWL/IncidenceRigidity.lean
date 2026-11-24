import GroupWL.TwistNormalization
import GroupWL.CharacteristicSector
import GroupWL.FreeAnchors

/-! # Isomorphism detects the affine cokernel in the actual constructed groups -/
namespace GroupWL.IncidenceRigidity
open IncidenceTensor IncidenceCoordinates IncidenceGroup GlobalCokernel

section Dimensions
universe u
variable {F I J : Type u} [Field F] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {V : J → Type u} [∀ j, AddCommGroup (V j)] [∀ j, Module F (V j)]
variable (A : AffineSystem F I J V) (q : ℕ)

theorem canonical_dimension_gap [Nonempty I] (hq : 2 ≤ q) :
    Module.finrank F (InputIndex.{u, u} A q → F) < Module.finrank F (OutputIndex.{u, u, u} A q → F) := by
  classical
  letI : Nonempty (OldOutputIndex.{u, u} A q) :=
    ⟨.inl ⟨.inl (Classical.choice inferInstance), (firstPair q hq, none)⟩⟩
  simp only [Module.finrank_fintype_fun_eq_card]
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  change Nat.card (InputIndex.{u, u} A q) < Nat.card (OldOutputIndex.{u, u} A q ⊕ InputIndex.{u, u} A q)
  have hsum : Nat.card (OldOutputIndex.{u, u} A q ⊕ InputIndex.{u, u} A q) =
      Nat.card (OldOutputIndex.{u, u} A q) + Nat.card (InputIndex.{u, u} A q) := Nat.card_sum
  rw [hsum]
  have hpos : 0 < Nat.card (OldOutputIndex.{u, u} A q) := Nat.card_pos
  exact Nat.lt_add_of_pos_left hpos

theorem canonical_evaluation_surjective (hq : 3 ≤ q)
    (x : InputIndex.{u, u} A q → F) (hx : x ≠ 0) :
    Function.Surjective (fun y : MatrixEvaluationGroup.operatorSpace (C A q (by omega)) =>
      (y : (InputIndex.{u, u} A q → F) →ₗ[F] (OutputIndex.{u, u, u} A q → F)) x) := by
  intro z
  exact MatrixEvaluationGroup.evaluation_surjective _
    (coordinateObstruction_noRankOne A q hq (inputCoordinates A q) (outputCoordinates A q)) x hx z

end Dimensions

section PrimeField
variable {p : ℕ} [Fact p.Prime] [NeZero (2 : ZMod p)]
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [Nonempty I]
variable {V : J → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module (ZMod p) (V j)]
variable (A : AffineSystem (ZMod p) I J V) (q : ℕ)

/-- No coordinate-preservation assumption is imposed on the group isomorphism. -/
theorem zero_charge_iso_iff (hq : 3 ≤ q) (β : I → ZMod p) :
    Nonempty
      (TensorGroup (evaluationTwist (MatrixEvaluationGroup.operatorSpace (C A q (by omega)))
        AlternatingBilinearMap.zero) ≃*
       TensorGroup (evaluationTwist (MatrixEvaluationGroup.operatorSpace (C A q (by omega)))
        (canonicalTwist A q (epsilonCharge A q (by omega) β)))) ↔
      β ∈ LinearMap.range A.linearMap := by
  rw [← zero_twist_iff_group_iso _ _ (canonical_evaluation_surjective A q hq)
    (canonical_dimension_gap A q (by omega))]
  exact charge_is_shear_iff A q (NeZero.ne (2 : ZMod p)) (by omega) β

theorem zero_charge_nonisomorphic_iff (hq : 3 ≤ q) (β : I → ZMod p) :
    ¬ Nonempty
      (TensorGroup (evaluationTwist (MatrixEvaluationGroup.operatorSpace (C A q (by omega)))
        AlternatingBilinearMap.zero) ≃*
       TensorGroup (evaluationTwist (MatrixEvaluationGroup.operatorSpace (C A q (by omega)))
        (canonicalTwist A q (epsilonCharge A q (by omega) β)))) ↔
      β ∉ LinearMap.range A.linearMap :=
  not_congr (zero_charge_iso_iff A q hq β)

end PrimeField
end GroupWL.IncidenceRigidity
