import GroupWL.ObstructionDuality
import GroupWL.RankBound

namespace GroupWL
namespace RankOneExclusion

open ObstructionDuality
open scoped BigOperators
variable {K ι κ : Type*} [Field K] [Fintype ι] [Fintype κ]

/-- An outer product has image contained in the span of its output factor. -/
theorem rankOne_range_le_span (x : ι → K) (w : κ → K) :
    (matrixToLinear (rankOne x w)).range ≤ Submodule.span K {w} := by
  intro z hz
  obtain ⟨t, rfl⟩ := hz
  have heq : matrixToLinear (rankOne x w) t = (∑ i, t i * x i) • w := by
    ext z
    simp only [matrixToLinear_apply, evaluation, LinearMap.coe_mk, AddHom.coe_mk,
      rankOne, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, mul_assoc]
  rw [heq]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton w))

/-- An outer product has rank at most one, including either zero-factor case. -/
theorem rankOne_finrank_le_one (x : ι → K) (w : κ → K) :
    Module.finrank K (matrixToLinear (rankOne x w)).range ≤ 1 :=
  (Submodule.finrank_mono (rankOne_range_le_span x w)).trans
    (by simpa using (finrank_span_le_card (R := K) ({w} : Set (κ → K))))

/-- Nonzero outer products have both factors nonzero, and conversely. -/
theorem rankOne_eq_zero_iff (x : ι → K) (w : κ → K) :
    rankOne x w = 0 ↔ x = 0 ∨ w = 0 := by
  classical
  constructor
  · intro hz
    by_cases hx : x = 0
    · exact Or.inl hx
    · right
      obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
        by_contra! h
        exact hx (funext h)
      funext z
      have he := congrFun (congrFun hz i) z
      exact (mul_eq_zero.mp he).resolve_left hi
  · rintro (rfl | rfl) <;> ext i z <;> simp [rankOne]

/-- A lower rank bound of two excludes all nonzero outer products. -/
theorem noRankOne_of_rank_lower
    (C : Submodule K (MatrixSpace K ι κ))
    (hC : ∀ y ∈ C, y ≠ 0 → 2 ≤ Module.finrank K (matrixToLinear y).range) :
    NoRankOne C := by
  intro x w hmem
  by_cases hz : rankOne x w = 0
  · exact (rankOne_eq_zero_iff x w).mp hz
  · have hlo := hC _ hmem hz
    have hup := rankOne_finrank_le_one x w
    omega

/-- The rank estimate supplies the manuscript's evaluation-surjectivity claim. -/
theorem evaluation_surjective_of_rank_lower
    (C : Submodule K (MatrixSpace K ι κ))
    (hC : ∀ y ∈ C, y ≠ 0 → 2 ≤ Module.finrank K (matrixToLinear y).range)
    (x : ι → K) (hx : x ≠ 0) :
    Function.Surjective ((evaluation x).comp (annihilator C).subtype) :=
  evaluation_surjective_of_noRankOne C (noRankOne_of_rank_lower C hC) x hx

end RankOneExclusion
end GroupWL
