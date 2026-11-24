import GroupWL.Affine
import GroupWL.ObstructionDuality

/-!
# The good-star cancellation in the coherent-residual lemma

When a readout changes, all incident equation vertices must remain in the
retained good set.  The local radical multiplier is a kernel relation on that
complete star.  Swapping the finite sums then makes the residual pairing
independent of the changed source assignment.
-/

namespace GroupWL
namespace ResidualCancellation

set_option linter.unusedSectionVars false

open scoped BigOperators

variable {K I J : Type*} [Field K] [Fintype I] [Fintype J] [DecidableEq J]
variable {V : J → Type*} [∀ j, AddCommGroup (V j)] [∀ j, Module K (V j)]
variable (A : AffineSystem K I J V)

/-- Pairing weighted equations and collecting by readouts is an exact finite
sum identity, including zero-coefficient incidences. -/
theorem weighted_equations (good : Finset I) (h : I → K) (z : ∀ j, V j) :
    (∑ i ∈ good, h i * A.equation i z) =
      ∑ j, (∑ i ∈ good, h i • A.coefficient i j) (z j) := by
  simp only [AffineSystem.equation, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.mul_sum, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]

/-- A full-star kernel relation restricts to the good equation set whenever
all incidences of that readout are good. -/
theorem good_star_kernel (good : Finset I) (h : I → K) (j : J)
    (hstar : ∀ i, j ∈ A.scope i → i ∈ good)
    (hkernel : ∑ i, h i • A.coefficient i j = 0) :
    ∑ i ∈ good, h i • A.coefficient i j = 0 := by
  classical
  rw [← hkernel]
  apply Finset.sum_subset (Finset.subset_univ good)
  intro i hi hnot
  have hout : j ∉ A.scope i := fun hij => hnot (hstar i hij)
  simp [A.coefficient_outside i j hout]

/-- The weighted equation value is invariant when each changed readout has a
complete good star and its multipliers satisfy the local kernel relation. -/
theorem weighted_equations_eq (good : Finset I) (h : I → K) (z w : ∀ j, V j)
    (hstar : ∀ j, w j ≠ z j → ∀ i, j ∈ A.scope i → i ∈ good)
    (hkernel : ∀ j, w j ≠ z j → ∑ i, h i • A.coefficient i j = 0) :
    (∑ i ∈ good, h i * A.equation i w) =
      ∑ i ∈ good, h i * A.equation i z := by
  rw [weighted_equations, weighted_equations]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hchange : w j = z j
  · rw [hchange]
  · have hk := good_star_kernel A good h j (hstar j hchange) (hkernel j hchange)
    simp [hk]

/-- Consequently the weighted affine residual is unchanged. -/
theorem weighted_residuals_eq (good : Finset I) (h β : I → K) (z w : ∀ j, V j)
    (hstar : ∀ j, w j ≠ z j → ∀ i, j ∈ A.scope i → i ∈ good)
    (hkernel : ∀ j, w j ≠ z j → ∑ i, h i • A.coefficient i j = 0) :
    (∑ i ∈ good, h i * (β i - A.equation i w)) =
      ∑ i ∈ good, h i * (β i - A.equation i z) := by
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [weighted_equations_eq A good h z w hstar hkernel]

/-- Equations that become bad have zero new residual, so their omission does
not affect the new pairing. -/
theorem shrinking_good_set (oldGood newGood : Finset I) (hsub : newGood ⊆ oldGood)
    (h β : I → K) (w : ∀ j, V j)
    (hzero : ∀ i ∈ oldGood, i ∉ newGood → A.equation i w = β i) :
    (∑ i ∈ newGood, h i * (β i - A.equation i w)) =
      ∑ i ∈ oldGood, h i * (β i - A.equation i w) := by
  classical
  apply Finset.sum_subset hsub
  intro i hi hnot
  simp [hzero i hi hnot]

/-- The exact normalized-pairing equality in the coherence proof. -/
theorem normalized_pairings_eq
    (oldGood newGood : Finset I) (hsub : newGood ⊆ oldGood)
    (h β : I → K) (z w : ∀ j, V j)
    (hzero : ∀ i ∈ oldGood, i ∉ newGood → A.equation i w = β i)
    (hstar : ∀ j, w j ≠ z j → ∀ i, j ∈ A.scope i → i ∈ oldGood)
    (hkernel : ∀ j, w j ≠ z j → ∑ i, h i • A.coefficient i j = 0) :
    (∑ i ∈ newGood, h i * (β i - A.equation i w)) =
      ∑ i ∈ oldGood, h i * (β i - A.equation i z) := by
  rw [shrinking_good_set A oldGood newGood hsub h β w hzero]
  exact weighted_residuals_eq A oldGood h β z w hstar hkernel

/-- Once relative obstructions have their normalized local-multiplier
readings, the difference of residuals is an actual relative boundary. -/
theorem residual_difference_mem_range
    {B W : Type*} [AddCommGroup B] [Module K B] [AddCommGroup W] [Module K W]
    (d : B →ₗ[K] W) (ρold ρnew : W)
    (oldGood newGood : Finset I) (hsub : newGood ⊆ oldGood)
    (β : I → K) (z w : ∀ j, V j)
    (hzero : ∀ i ∈ oldGood, i ∉ newGood → A.equation i w = β i)
    (hstar : ∀ j, w j ≠ z j → ∀ i, j ∈ A.scope i → i ∈ oldGood)
    (readings : ∀ φ : Module.Dual K W, d.dualMap φ = 0 → ∃ h : I → K,
      φ ρold = ∑ i ∈ oldGood, h i * (β i - A.equation i z) ∧
      φ ρnew = ∑ i ∈ newGood, h i * (β i - A.equation i w) ∧
      ∀ j, w j ≠ z j → ∑ i, h i • A.coefficient i j = 0) :
    ρnew - ρold ∈ LinearMap.range d := by
  apply (ObstructionDuality.sub_mem_range_iff_dual_obstructions d ρnew ρold).mpr
  intro φ hφ
  obtain ⟨h, hold, hnew, hkernel⟩ := readings φ hφ
  rw [hold, hnew]
  exact normalized_pairings_eq A oldGood newGood hsub h β z w hzero hstar hkernel

/-- A witness version of the range statement, directly usable by the shear
assembly with `B` chosen to be the relative correction subspace. -/
theorem exists_relative_correction
    {B W : Type*} [AddCommGroup B] [Module K B] [AddCommGroup W] [Module K W]
    (d : B →ₗ[K] W) (ρold ρnew : W)
    (oldGood newGood : Finset I) (hsub : newGood ⊆ oldGood)
    (β : I → K) (z w : ∀ j, V j)
    (hzero : ∀ i ∈ oldGood, i ∉ newGood → A.equation i w = β i)
    (hstar : ∀ j, w j ≠ z j → ∀ i, j ∈ A.scope i → i ∈ oldGood)
    (readings : ∀ φ : Module.Dual K W, d.dualMap φ = 0 → ∃ h : I → K,
      φ ρold = ∑ i ∈ oldGood, h i * (β i - A.equation i z) ∧
      φ ρnew = ∑ i ∈ newGood, h i * (β i - A.equation i w) ∧
      ∀ j, w j ≠ z j → ∑ i, h i • A.coefficient i j = 0) :
    ∃ b : B, d b = ρnew - ρold :=
  residual_difference_mem_range A d ρold ρnew oldGood newGood hsub β z w hzero hstar readings

end ResidualCancellation
end GroupWL
