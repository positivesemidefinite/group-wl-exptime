import GroupWL.GlobalCokernel

/-! # Global shears between arbitrary twists -/
namespace GroupWL

section Shears
variable {F X Z : Type*} [Field F] [AddCommGroup X] [Module F X]
  [AddCommGroup Z] [Module F Z]

def evaluationShearBetween (Y : Submodule F (X →ₗ[F] Z)) (α : X →ₗ[F] Y)
    (ε δ : AlternatingBilinearMap F X Z) :
    TensorGroup (evaluationTwist Y ε) ≃ TensorGroup (evaluationTwist Y δ) where
  toFun g := ⟨(g.fst.1, g.fst.2 + α g.fst.1), g.snd⟩
  invFun g := ⟨(g.fst.1, g.fst.2 - α g.fst.1), g.snd⟩
  left_inv g := by ext <;> simp
  right_inv g := by ext <;> simp

def evaluationShearBetweenMulEquiv (Y : Submodule F (X →ₗ[F] Z)) (α : X →ₗ[F] Y)
    (ε δ : AlternatingBilinearMap F X Z)
    (hα : ∀ x y, shearCoboundary Y α x y = δ x y - ε x y) :
    TensorGroup (evaluationTwist Y ε) ≃* TensorGroup (evaluationTwist Y δ) where
  toEquiv := evaluationShearBetween Y α ε δ
  map_mul' g h := by
    ext
    · rfl
    · simp [evaluationShearBetween, TensorGroup.mul_fst]
      abel
    · simp only [evaluationShearBetween, TensorGroup.mul_snd, TensorGroup.mul_fst,
        evaluationTwist_apply, Submodule.coe_add, LinearMap.add_apply]
      have hc := hα g.fst.1 h.fst.1
      change (α g.fst.1 : X →ₗ[F] Z) h.fst.1 -
        (α h.fst.1 : X →ₗ[F] Z) g.fst.1 = δ g.fst.1 h.fst.1 - ε g.fst.1 h.fst.1 at hc
      have he : ε g.fst.1 h.fst.1 = δ g.fst.1 h.fst.1 -
          ((α g.fst.1 : X →ₗ[F] Z) h.fst.1 - (α h.fst.1 : X →ₗ[F] Z) g.fst.1) := by
        rw [hc]; abel
      change ε.toLinearMap g.fst.1 h.fst.1 = δ.toLinearMap g.fst.1 h.fst.1 -
        ((α g.fst.1 : X →ₗ[F] Z) h.fst.1 - (α h.fst.1 : X →ₗ[F] Z) g.fst.1) at he
      rw [he]
      congr 2
      abel

@[simp] theorem evaluationShearBetween_quotient
    (Y : Submodule F (X →ₗ[F] Z)) (α : X →ₗ[F] Y)
    (ε δ : AlternatingBilinearMap F X Z) (g : TensorGroup (evaluationTwist Y ε)) :
    (evaluationShearBetween Y α ε δ g).fst.1 = g.fst.1 := rfl

@[simp] theorem evaluationShearBetween_center
    (Y : Submodule F (X →ₗ[F] Z)) (α : X →ₗ[F] Y)
    (ε δ : AlternatingBilinearMap F X Z) (y : Y) (z : Z) :
    evaluationShearBetween Y α ε δ ⟨(0, y), z⟩ = ⟨(0, y), z⟩ := by
  ext <;> simp [evaluationShearBetween]

end Shears

namespace GlobalCokernel
open IncidenceTensor IncidenceCoordinates
universe u
variable {F I J : Type u} [Field F] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {V : J → Type u} [∀ j, AddCommGroup (V j)] [∀ j, Module F (V j)]
variable (A : AffineSystem F I J V) (q : ℕ)

/-- Every actual twisted group is isomorphic to an actual charge-twisted group.
The displayed shear fixes quotient labels, the center, and all matrix anchors. -/
theorem every_twist_isomorphic_charge (h2 : (2 : F) ≠ 0) (hq : 2 ≤ q)
    (ε : AlternatingBilinearMap F (InputIndex A q → F) (OutputIndex A q → F)) :
    ∃ β : I → F, Nonempty
      (TensorGroup (evaluationTwist (MatrixEvaluationGroup.operatorSpace (C A q (by omega))) ε) ≃*
       TensorGroup (evaluationTwist (MatrixEvaluationGroup.operatorSpace (C A q (by omega)))
        (canonicalTwist A q (epsilonCharge A q hq β)))) := by
  obtain ⟨β, α, hα⟩ := every_twist_charge_representative A q h2 hq ε
  exact ⟨β, ⟨(evaluationShearBetweenMulEquiv _ α _ ε hα).symm⟩⟩

/-- Charge normalization with the exact named-sector preservation exposed. -/
theorem every_twist_isomorphic_charge_preserving (h2 : (2 : F) ≠ 0) (hq : 2 ≤ q)
    (ε : AlternatingBilinearMap F (InputIndex A q → F) (OutputIndex A q → F)) :
    ∃ (β : I → F)
      (f : TensorGroup (evaluationTwist (MatrixEvaluationGroup.operatorSpace (C A q (by omega))) ε) ≃*
       TensorGroup (evaluationTwist (MatrixEvaluationGroup.operatorSpace (C A q (by omega)))
        (canonicalTwist A q (epsilonCharge A q hq β)))),
      (∀ g, (f g).fst.1 = g.fst.1) ∧
      ∀ (y : MatrixEvaluationGroup.operatorSpace (C A q (by omega))) (z : OutputIndex A q → F),
        f ⟨(0, y), z⟩ = ⟨(0, y), z⟩ := by
  obtain ⟨β, α, hα⟩ := every_twist_charge_representative A q h2 hq ε
  refine ⟨β, (evaluationShearBetweenMulEquiv _ α _ ε hα).symm, ?_, ?_⟩
  · intro g
    rfl
  · intro y z
    change (⟨(0, y - α 0), z⟩ : TensorGroup _) = ⟨(0, y), z⟩
    simp
    exact sub_zero y

end GlobalCokernel
end GroupWL
