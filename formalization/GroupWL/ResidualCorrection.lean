import GroupWL.RelativeObstruction
import GroupWL.RelativeGoodVertices

/-! # Coherence of the actual minor-normalized residual tensors -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace GroupWL.ResidualCorrection

open IncidenceTensor IncidenceCoordinates GlobalCokernel ObstructionDuality
open AlternatingCoordinates ResidualTensors RelativeObstruction

attribute [local instance] Classical.propDecidable
universe u
variable {F I J : Type u} [Field F] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {V : J → Type u} [∀ j, AddCommGroup (V j)] [∀ j, Module F (V j)]
variable (A : AffineSystem F I J V) (q : ℕ)

/-- The equations with a genuine unit minor on the retained annihilator. -/
noncomputable def goodEquations (E : Submodule F (InputIndex A q → F)) : Finset I :=
  Finset.univ.filter (Good A q E)

@[simp] theorem mem_goodEquations (E : Submodule F (InputIndex A q → F)) (i : I) :
    i ∈ goodEquations A q E ↔ Good A q E i := by simp [goodEquations]

theorem goodEquations_antitone {E D : Submodule F (InputIndex A q → F)} (hED : E ≤ D) :
    goodEquations A q D ⊆ goodEquations A q E := by
  intro i hi
  exact (mem_goodEquations A q E i).mpr
    (good_antitone A q hED i ((mem_goodEquations A q D i).mp hi))

/-- A retained relative obstruction has the same normalized reading on every
smaller query domain.  Both tensors read the original multiplier directly. -/
theorem minor_relative_reading
    {E D : Submodule F (InputIndex A q → F)} (hED : E ≤ D)
    (b : AlternatingBilinearMap F (InputIndex A q → F) (OutputIndex A q → F))
    (P : orthogonal E →ₗ[F] OldInput A q)
    (hP : ∀ u v : orthogonal E, b u.val v.val = outputCoordinates A q
      (omega A q (P u) (queryInput A q E v), 0))
    (r : ∀ v, RingAt A v)
    (hr : ∀ v, GoodVertex A (queryInput A q E) v → ∀ x k,
      P x v k = r v * queryInput A q E x v k)
    {i : I} (m : MinorAt A q D i) :
    tensorPair (bilinearCoordinates b.toLinearMap)
      (bilinearCoordinates (m.tensor A q).toLinearMap) = 2 * (r (.inl i)).snd := by
  let u' := queryInclusion A q hED m.u
  let v' := queryInclusion A q hED m.v
  have hi : GoodVertex A (queryInput A q E) (.inl i) :=
    goodVertex_of_good A q E i (good_antitone A q hED i ⟨m⟩)
  apply normalizedTensor_reads_multiplier A q i m.ab m.u.val m.v.val m.unit b (r (.inl i))
  change ((outputCoordinates A q).symm (b u'.val v'.val)).1.1 (.inl i) m.ab = _
  rw [hP u' v', LinearEquiv.symm_apply_apply, omega_internal,
    hr (.inl i) hi u' m.ab.val.1, hr (.inl i) hi u' m.ab.val.2, m.unit_eq]
  change (r (.inl i) * _ : TrivSqZeroExt F F) * _ - _ * (r (.inl i) * _) = _
  dsimp [u', v', queryInclusion, queryInput, LocalMultiplier.minor]
  ring

theorem eta_relative_reading
    {E D : Submodule F (InputIndex A q → F)} (hED : E ≤ D)
    (b : AlternatingBilinearMap F (InputIndex A q → F) (OutputIndex A q → F))
    (P : orthogonal E →ₗ[F] OldInput A q)
    (hP : ∀ u v : orthogonal E, b u.val v.val = outputCoordinates A q
      (omega A q (P u) (queryInput A q E v), 0))
    (r : ∀ v, RingAt A v)
    (hr : ∀ v, GoodVertex A (queryInput A q E) v → ∀ x k,
      P x v k = r v * queryInput A q E x v k)
    (i : I) :
    tensorPair (bilinearCoordinates b.toLinearMap)
      (bilinearCoordinates (eta A q D i).toLinearMap) =
      if Good A q D i then 2 * (r (.inl i)).snd else 0 := by
  classical
  unfold eta
  split_ifs with hi
  · exact minor_relative_reading A q hED b P hP r hr (Classical.choice hi)
  · simp [AlternatingBilinearMap.zero, tensorPair]

/-- Actual relative pairings of the constructed residuals are the weighted
source residuals on the good equation set. -/
theorem residual_relative_pairing
    {E D : Submodule F (InputIndex A q → F)} (hED : E ≤ D)
    (b : AlternatingBilinearMap F (InputIndex A q → F) (OutputIndex A q → F))
    (P : orthogonal E →ₗ[F] OldInput A q)
    (hP : ∀ u v : orthogonal E, b u.val v.val = outputCoordinates A q
      (omega A q (P u) (queryInput A q E v), 0))
    (r : ∀ v, RingAt A v)
    (hr : ∀ v, GoodVertex A (queryInput A q E) v → ∀ x k,
      P x v k = r v * queryInput A q E x v k)
    (β : I → F) (z : ∀ j, V j) :
    tensorPair (bilinearCoordinates b.toLinearMap)
      (bilinearCoordinates (residual A q β D z).toLinearMap) =
      2 * ∑ i ∈ goodEquations A q D, (r (.inl i)).snd * (β i - A.equation i z) := by
  change tensorDual (bilinearCoordinates b.toLinearMap)
    (bilinearCoordinates (∑ i, (β i - A.equation i z) • (eta A q D i).toLinearMap)) = _
  simp only [map_sum, map_smul, smul_eq_mul]
  change (∑ i, (β i - A.equation i z) * tensorPair (bilinearCoordinates b.toLinearMap)
    (bilinearCoordinates (eta A q D i).toLinearMap)) = _
  simp only [eta_relative_reading A q hED b P hP r hr]
  rw [goodEquations, Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : Good A q D i
  · rw [if_pos hi, if_pos hi]; ring
  · rw [if_neg hi, if_neg hi]; simp

/-- The coherent-residual lemma for the actual tensor construction. Every
normalization, relative obstruction, local multiplier, and good-star
cancellation used here has been derived from the construction. -/
theorem residual_correction (h2 : (2 : F) ≠ 0) (hq : 2 ≤ q)
    (E D : Submodule F (InputIndex A q → F)) (hED : E ≤ D)
    (β : I → F) (z w : ∀ j, V j)
    (_hz : ∀ i, ¬ Good A q E i → A.equation i z = β i)
    (hw : ∀ i, ¬ Good A q D i → A.equation i w = β i)
    (hchange : ∀ j, w j ≠ z j →
      GoodVertex A (queryInput A q E) (.inr j) ∧ ∀ i, j ∈ A.scope i → Good A q E i) :
    ∃ α : (InputIndex A q → F) →ₗ[F] MatrixEvaluationGroup.operatorSpace (C A q (by omega)),
      CoherentShears.RelativeCorrection _ E α ∧
      ∀ x y, shearCoboundary _ α x y = residual A q β D w x y - residual A q β E z x y := by
  let t : AlternatingBilinearMap F (InputIndex A q → F) (OutputIndex A q → F) :=
    { toLinearMap := (residual A q β D w).toLinearMap - (residual A q β E z).toLinearMap
      map_self_eq_zero := by intro x; simp }
  apply exists_relative_shear_of_pairings h2 (C A q (by omega)) E t
  intro b hb
  obtain ⟨P, hPL, hP⟩ := incidence_relative_lift A q h2 (by omega) E b hb
  have hP' : ∀ u v : orthogonal E, b u.val v.val = outputCoordinates A q
      (omega A q (P u) (queryInput A q E v), 0) := hP
  have hdiag : ∀ u, omega A q (P u) (queryInput A q E u) = 0 := by
    intro u
    have hu : outputCoordinates A q (omega A q (P u) (queryInput A q E u), 0) = 0 :=
      (hP' u u).symm.trans (b.self u.val)
    have hu' : (omega A q (P u) (queryInput A q E u), (0 : PaddedInput A q)) = 0 :=
      (outputCoordinates A q).injective (by simpa using hu)
    exact congrArg Prod.fst hu'
  obtain ⟨r, hr, he, hk⟩ := relative_multiplier_classification A P (queryInput A q E) hdiag
  have hsum : (∑ i ∈ goodEquations A q D, (r (.inl i)).snd * (β i - A.equation i w)) =
      ∑ i ∈ goodEquations A q E, (r (.inl i)).snd * (β i - A.equation i z) := by
    apply ResidualCancellation.normalized_pairings_eq A
      (goodEquations A q E) (goodEquations A q D) (goodEquations_antitone A q hED)
      (fun i => (r (.inl i)).snd) β z w
    · intro i hi hnot
      exact hw i (fun h => hnot ((mem_goodEquations A q D i).mpr h))
    · intro j hj i hij
      exact (mem_goodEquations A q E i).mpr ((hchange j hj).2 i hij)
    · intro j hj
      exact hk j (hchange j hj).1 (fun i hij =>
        goodVertex_of_good A q E i ((hchange j hj).2 i hij))
  change tensorDual (bilinearCoordinates b.toLinearMap)
    (bilinearCoordinates ((residual A q β D w).toLinearMap - (residual A q β E z).toLinearMap)) = 0
  rw [map_sub (bilinearCoordinates (F := F) (ι := InputIndex A q) (κ := OutputIndex A q)),
    map_sub (tensorDual (bilinearCoordinates b.toLinearMap))]
  change tensorPair (bilinearCoordinates b.toLinearMap)
      (bilinearCoordinates (residual A q β D w).toLinearMap) -
    tensorPair (bilinearCoordinates b.toLinearMap)
      (bilinearCoordinates (residual A q β E z).toLinearMap) = 0
  rw [residual_relative_pairing A q hED b P hP' r hr β w,
    residual_relative_pairing A q le_rfl b P hP' r hr β z, hsum, sub_self]

end GroupWL.ResidualCorrection
