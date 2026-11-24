import GroupWL.Statement
import GroupWL.ConcreteVersionI
import GroupWL.ConcreteVersionIII
import GroupWL.GraphToGroup
import GroupWL.PebbleReindex
import GroupWL.VersionBounds

/-! # Actual all-version tensor identification caps and reduction parameters -/
namespace GroupWL.TensorVersionCaps

open Refinement
universe u v
variable {G : Type u} {H : Type v} [Group G] [Group H] [Fintype G] [Fintype H]
variable {k d : ℕ}

theorem identifiesIII_of_identifiesII (hk : 0 < k) (hkd : (k+1)/2+2 ≤ d)
    (h : IdentifiesII k G) : Refinement.Identifies .three d G := by
  intro H hH
  exact h H (GraphToGroup.equivalentII_of_equivalentIII hk hkd hH)

/-- All three actual notions identify the group two dimensions above any
positive Version-II identification bound. -/
theorem identifies_all_of_identifiesII (hk : 0 < k) (hkd : k+2 ≤ d)
    (h : IdentifiesII k G) (version : Version) : Refinement.Identifies version d G := by
  cases version with
  | one => exact ConcreteVersionI.identifiesI_of_identifiesII hkd h
  | two => exact PebbleReindex.identifiesII_mono (by omega) h
  | three => exact identifiesIII_of_identifiesII hk (by omega) h

/-- The parameter sandwich is proved for the concrete group-WL definitions. -/
theorem rejection_I_III (r : ℕ)
    (h : EquivalentII (Parameters.rejectionDimension r) G H) :
    EquivalentI (Parameters.dimensionI r) G H ∧ EquivalentIII (Parameters.dimensionIII r) G H := by
  have hI := PebbleReindex.equivalentI_of_equivalentII_of_le
    (Parameters.versionI_in_rejection_range r) h
  refine ⟨hI,ConcreteVersionIII.equivalentIII_of_equivalentI ?_
    (Parameters.versionIII_comparison_fits r) hI⟩
  unfold Parameters.dimensionIII Parameters.dimensionII Parameters.ringBudget
    Parameters.frameWidth Parameters.blockBudget
  omega

/-- Identification transfers at exactly the three dimensions used by the reduction. -/
theorem identification_parameters (r : ℕ) (h : IdentifiesII (Parameters.dimensionII r) G) :
    Refinement.Identifies .one (Parameters.dimensionI r) G ∧
      Refinement.Identifies .two (Parameters.dimensionII r) G ∧
      Refinement.Identifies .three (Parameters.dimensionIII r) G := by
  refine ⟨ConcreteVersionI.identifiesI_of_identifiesII ?_ h,h,?_⟩
  · unfold Parameters.dimensionI
    omega
  · apply identifiesIII_of_identifiesII ?_ (by rfl) h
    unfold Parameters.dimensionII
    omega

/-- Isomorphic groups have the same actual colors in every joint-vector version. -/
theorem groupEquivalent_of_isomorphic (e : G ≃* H) (version : Version) (hk : k ≠ 1) :
    GroupEquivalent version k G H := by
  cases version with
  | one => exact equivalentI_of_isomorphic e k
  | two => exact equivalentII_of_isomorphic e k
  | three =>
      exact ConcreteVersionIII.equivalentIII_of_equivalentI hk (le_refl _)
        (equivalentI_of_isomorphic e (2*k+1))

end GroupWL.TensorVersionCaps

namespace GroupWL.Statement

open Refinement
variable {p : ℕ} [Fact p.Prime] [NeZero (2 : ZMod p)]

/-- A uniform cap for every version, including the zero-dimensional tensor. -/
def TensorDescription.wlCap (T : TensorDescription p) : ℕ :=
  T.inputDimension + T.outputDimension + 10

theorem identifies_at_common_cap (T : TensorDescription p) (version : Version) :
    Refinement.Identifies version T.wlCap T.Carrier := by
  apply TensorVersionCaps.identifies_all_of_identifiesII
    (k := max 1 (T.inputDimension+T.outputDimension)) (by omega) ?_
    (identifiesII_at_input_cap p T) version
  unfold TensorDescription.wlCap
  omega

theorem identifies_above_common_cap (T : TensorDescription p) (version : Version) {k : ℕ}
    (hk : T.wlCap ≤ k) : Refinement.Identifies version k T.Carrier := by
  apply TensorVersionCaps.identifies_all_of_identifiesII
    (k := max 1 (T.inputDimension+T.outputDimension)) (by omega) ?_
    (identifiesII_at_input_cap p T) version
  unfold TensorDescription.wlCap at hk
  omega

/-- Arbitrarily large binary dimensions can be clamped before running the
identification test, because every group above the cap is identified. -/
theorem identification_clamp (T : TensorDescription p) (version : Version) (k : ℕ) :
    Refinement.Identifies version k T.Carrier ↔
      Refinement.Identifies version (min k T.wlCap) T.Carrier := by
  by_cases hk : k ≤ T.wlCap
  · simp only [min_eq_left hk]
  · have hle : T.wlCap ≤ k := by omega
    rw [min_eq_right hle]
    exact iff_of_true (identifies_above_common_cap T version hle) (identifies_at_common_cap T version)

/-- The cap is linear in the charged dense input length. -/
theorem wlCap_le_encoded_length_add_ten (T : TensorDescription p) (bits : Complexity.BitString) :
    T.wlCap ≤ (T.denseWord p ++ bits).length + 10 := by
  have h := dimensions_le_encoded_length p T bits
  unfold TensorDescription.wlCap
  omega

/-- Above the common cap, each actual equivalence test is exactly isomorphism. -/
theorem equivalence_iff_isomorphic_above_cap (T U : TensorDescription p) (version : Version)
    {k : ℕ} (hk : T.wlCap ≤ k) :
    GroupEquivalent version k T.Carrier U.Carrier ↔ Nonempty (T.Carrier ≃* U.Carrier) := by
  constructor
  · intro h
    exact identifies_above_common_cap T version hk
      ⟨U.Carrier,inferInstance,inferInstance⟩ h
  · rintro ⟨e⟩
    apply TensorVersionCaps.groupEquivalent_of_isomorphic e version
    unfold TensorDescription.wlCap at hk
    omega

/-- Equivalence dimensions can be clamped as well, using the first tensor's
cap even when the comparison tensor has a different coordinate dimension. -/
theorem equivalence_clamp (T U : TensorDescription p) (version : Version) (k : ℕ) :
    GroupEquivalent version k T.Carrier U.Carrier ↔
      GroupEquivalent version (min k T.wlCap) T.Carrier U.Carrier := by
  by_cases hk : k ≤ T.wlCap
  · simp only [min_eq_left hk]
  · have hle : T.wlCap ≤ k := by omega
    rw [min_eq_right hle,equivalence_iff_isomorphic_above_cap T U version hle,
      equivalence_iff_isomorphic_above_cap T U version (le_refl _)]

end GroupWL.Statement
