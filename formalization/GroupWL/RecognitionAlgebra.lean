import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic

/-!
# The commuting-complement calculation

This is the algebraic last step of the manuscript's zero-twist criterion.
It proves that an invertible change of quotient coordinates does not alter
the obstruction to finding a commuting complement. Recognition of the
characteristic subgroup and extraction of such a complement from a group
isomorphism are separate obligations.
-/

namespace GroupWL

section

variable {F X Y Z : Type*} [Field F]
  [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]
  [AddCommGroup Z] [Module F Z]

/-- Evaluation may be any fixed bilinear map; for the manuscript,
`Y` is a subspace of the linear maps from `X` to `Z`. -/
def shearDerivative (ev : Y →ₗ[F] X →ₗ[F] Z) (α : X →ₗ[F] Y)
    (x x' : X) : Z := ev (α x) x' - ev (α x') x

/-- The bracket on quotient and matrix coordinates, omitting the central
coordinate, which never affects commutation. -/
def evaluationBracket (ev : Y →ₗ[F] X →ₗ[F] Z)
    (ε : X →ₗ[F] X →ₗ[F] Z) (u v : X × Y) : Z :=
  ev v.2 u.1 - ev u.2 v.1 + ε u.1 v.1

theorem graph_commutes_iff_derivative
    (ev : Y →ₗ[F] X →ₗ[F] Z) (ε : X →ₗ[F] X →ₗ[F] Z)
    (α : X →ₗ[F] Y) :
    (∀ x x', evaluationBracket ev ε (x, α x) (x', α x') = 0) ↔
      ∀ x x', shearDerivative ev α x x' = ε x x' := by
  simp only [evaluationBracket, shearDerivative]
  constructor
  · intro h x x'
    calc
      ev (α x) x' - ev (α x') x = -(ev (α x') x - ev (α x) x') := by abel
      _ = ε x x' := neg_eq_iff_eq_neg.mpr (add_eq_zero_iff_eq_neg.mp (h x x'))
  · intro h x x'
    rw [← h x x']
    abel

theorem derivative_of_commuting_complement
    (ev : Y →ₗ[F] X →ₗ[F] Z) (ε : X →ₗ[F] X →ₗ[F] Z)
    (C : X ≃ₗ[F] X) (β : X →ₗ[F] Y)
    (h : ∀ x x', evaluationBracket ev ε (C x, β x) (C x', β x') = 0) :
    ∀ x x', shearDerivative ev (β.comp C.symm.toLinearMap) x x' = ε x x' := by
  apply (graph_commutes_iff_derivative ev ε _).1
  intro x x'
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] using h (C.symm x) (C.symm x')

theorem derivative_iff_commuting_complement
    (ev : Y →ₗ[F] X →ₗ[F] Z) (ε : X →ₗ[F] X →ₗ[F] Z) :
    (∃ α : X →ₗ[F] Y, ∀ x x', shearDerivative ev α x x' = ε x x') ↔
      ∃ (C : X ≃ₗ[F] X) (β : X →ₗ[F] Y),
        ∀ x x', evaluationBracket ev ε (C x, β x) (C x', β x') = 0 := by
  constructor
  · rintro ⟨α, hα⟩
    exact ⟨LinearEquiv.refl F X, α, (graph_commutes_iff_derivative ev ε α).2 hα⟩
  · rintro ⟨C, β, h⟩
    exact ⟨β.comp C.symm.toLinearMap, derivative_of_commuting_complement ev ε C β h⟩

/-- A linear complement may be supplied as one map rather than separately
as its two coordinates. Its quotient projection must be invertible. -/
theorem derivative_of_linear_section
    (ev : Y →ₗ[F] X →ₗ[F] Z) (ε : X →ₗ[F] X →ₗ[F] Z)
    (s : X →ₗ[F] X × Y) (C : X ≃ₗ[F] X)
    (hC : ∀ x, (s x).1 = C x)
    (hs : ∀ x x', evaluationBracket ev ε (s x) (s x') = 0) :
    ∃ α : X →ₗ[F] Y, ∀ x x', shearDerivative ev α x x' = ε x x' := by
  apply (derivative_iff_commuting_complement ev ε).2
  refine ⟨C, (LinearMap.snd F X Y).comp s, ?_⟩
  intro x x'
  have hx : (C x, ((LinearMap.snd F X Y).comp s) x) = s x := by
    apply Prod.ext
    · exact (hC x).symm
    · rfl
  have hx' : (C x', ((LinearMap.snd F X Y).comp s) x') = s x' := by
    apply Prod.ext
    · exact (hC x').symm
    · rfl
  rw [hx, hx']
  exact hs x x'

end
end GroupWL
