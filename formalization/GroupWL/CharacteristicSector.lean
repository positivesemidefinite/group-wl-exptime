import GroupWL.ZeroTwist
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # The matrix sector is preserved by arbitrary group isomorphisms

We recover the sector using commutator rank. This is equivalent to the
manuscript's centralizer-cardinality argument and avoids enumerating group
elements. Coordinate linearity of abstract isomorphisms is already proved.
-/

namespace GroupWL

section Adjoint

variable {F V Z : Type*} [Field F]
  [AddCommGroup V] [Module F V] [AddCommGroup Z] [Module F Z]

/-- Commutation with a fixed element, as a linear map on all coordinates. -/
def tensorAdjoint (b : AlternatingBilinearMap F V Z) (u : V × Z) :
    (V × Z) →ₗ[F] V × Z :=
  (LinearMap.inr F V Z).comp ((b.toLinearMap u.1).comp (LinearMap.fst F V Z))

@[simp] theorem tensorAdjoint_apply (b : AlternatingBilinearMap F V Z)
    (u v : V × Z) : tensorAdjoint b u v = (0, b u.1 v.1) := rfl

end Adjoint

section Isomorphism

variable {p : ℕ} [Fact p.Prime] [NeZero (2 : ZMod p)]
variable {V Z V' Z' : Type*}
variable [AddCommGroup V] [Module (ZMod p) V]
  [AddCommGroup Z] [Module (ZMod p) Z]
  [AddCommGroup V'] [Module (ZMod p) V']
  [AddCommGroup Z'] [Module (ZMod p) Z']
variable {b : AlternatingBilinearMap (ZMod p) V Z}
  {c : AlternatingBilinearMap (ZMod p) V' Z'}

theorem tensorAdjoint_conjugate (f : TensorGroup b ≃* TensorGroup c) (u : V × Z) :
    (TensorGroup.equivLinearEquiv f).toLinearMap.comp (tensorAdjoint b u) =
      (tensorAdjoint c (TensorGroup.equivLinearEquiv f u)).comp
        (TensorGroup.equivLinearEquiv f).toLinearMap := by
  apply LinearMap.ext
  intro v
  let g : TensorGroup b := TensorGroup.equivProd.symm u
  let h : TensorGroup b := TensorGroup.equivProd.symm v
  have heq : f (g * h * g⁻¹ * h⁻¹) = f g * f h * (f g)⁻¹ * (f h)⁻¹ := by simp
  rw [TensorGroup.commutator_eq, TensorGroup.commutator_eq] at heq
  exact congrArg TensorGroup.equivProd heq

theorem tensorAdjoint_finrank_invariant (f : TensorGroup b ≃* TensorGroup c) (u : V × Z) :
    Module.finrank (ZMod p) (LinearMap.range (tensorAdjoint b u)) =
      Module.finrank (ZMod p)
        (LinearMap.range (tensorAdjoint c (TensorGroup.equivLinearEquiv f u))) := by
  let E := TensorGroup.equivLinearEquiv f
  calc
    _ = Module.finrank (ZMod p) ((LinearMap.range (tensorAdjoint b u)).map E.toLinearMap) :=
      (E.finrank_map_eq _).symm
    _ = Module.finrank (ZMod p) (LinearMap.range (E.toLinearMap.comp (tensorAdjoint b u))) := by
      rw [LinearMap.range_comp]
    _ = Module.finrank (ZMod p) (LinearMap.range
        ((tensorAdjoint c (E u)).comp E.toLinearMap)) := by
      rw [tensorAdjoint_conjugate]
    _ = _ := by rw [LinearMap.range_comp_of_range_eq_top _ E.range]

end Isomorphism

section Evaluation

variable {F X Z : Type*} [Field F]
  [AddCommGroup X] [Module F X] [AddCommGroup Z] [Module F Z]
variable (Y : Submodule F (X →ₗ[F] Z)) (ε : AlternatingBilinearMap F X Z)

theorem evaluationAdjoint_range_of_nonzero
    (heval : ∀ x : X, x ≠ 0 → Function.Surjective (fun y : Y => (y : X →ₗ[F] Z) x))
    (u : (X × Y) × Z) (hx : u.1.1 ≠ 0) :
    LinearMap.range (tensorAdjoint (evaluationTwist Y ε) u) =
      LinearMap.range (LinearMap.inr F (X × Y) Z) := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨evaluationTwist Y ε u.1 w.1, rfl⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨y, hy⟩ := heval u.1.1 hx z
    refine ⟨((0, y), 0), ?_⟩
    simp [tensorAdjoint_apply, evaluationTwist_apply, hy]

theorem evaluationAdjoint_finrank_of_nonzero
    (heval : ∀ x : X, x ≠ 0 → Function.Surjective (fun y : Y => (y : X →ₗ[F] Z) x))
    (u : (X × Y) × Z) (hx : u.1.1 ≠ 0) :
    Module.finrank F (LinearMap.range (tensorAdjoint (evaluationTwist Y ε) u)) =
      Module.finrank F Z := by
  rw [evaluationAdjoint_range_of_nonzero Y ε heval u hx]
  apply LinearMap.finrank_range_of_inj
  intro z z' h
  exact congrArg Prod.snd h

theorem evaluationAdjoint_finrank_of_zero [FiniteDimensional F X]
    (u : (X × Y) × Z) (hx : u.1.1 = 0) :
    Module.finrank F (LinearMap.range (tensorAdjoint (evaluationTwist Y ε) u)) ≤
      Module.finrank F X := by
  let a : X →ₗ[F] (X × Y) × Z := (LinearMap.inr F (X × Y) Z).comp (-(u.1.2 : X →ₗ[F] Z))
  have hrange : LinearMap.range (tensorAdjoint (evaluationTwist Y ε) u) = LinearMap.range a := by
    ext v
    constructor
    · rintro ⟨w, rfl⟩
      refine ⟨w.1.1, ?_⟩
      simp [a, tensorAdjoint_apply, evaluationTwist_apply, hx]
    · rintro ⟨x, rfl⟩
      refine ⟨((x, 0), 0), ?_⟩
      simp [a, tensorAdjoint_apply, evaluationTwist_apply, hx]
  rw [hrange]
  exact LinearMap.finrank_range_le a

theorem matrixSector_iff_adjoint_finrank_lt [FiniteDimensional F X]
    (heval : ∀ x : X, x ≠ 0 → Function.Surjective (fun y : Y => (y : X →ₗ[F] Z) x))
    (hdim : Module.finrank F X < Module.finrank F Z) (u : (X × Y) × Z) :
    u.1.1 = 0 ↔
      Module.finrank F (LinearMap.range (tensorAdjoint (evaluationTwist Y ε) u)) <
        Module.finrank F Z := by
  constructor
  · intro hx
    exact (evaluationAdjoint_finrank_of_zero Y ε u hx).trans_lt hdim
  · intro hrank
    by_contra hx
    rw [evaluationAdjoint_finrank_of_nonzero Y ε heval u hx] at hrank
    exact (lt_irrefl _ hrank)

end Evaluation

section FullCriterion

variable {p : ℕ} [Fact p.Prime] [NeZero (2 : ZMod p)]
variable {X Z : Type*} [AddCommGroup X] [Module (ZMod p) X]
  [AddCommGroup Z] [Module (ZMod p) Z] [FiniteDimensional (ZMod p) X]
variable (Y : Submodule (ZMod p) (X →ₗ[ZMod p] Z))
variable (ε : AlternatingBilinearMap (ZMod p) X Z)

theorem group_iso_preserves_matrixSector
    (heval : ∀ x : X, x ≠ 0 → Function.Surjective (fun y : Y => (y : X →ₗ[ZMod p] Z) x))
    (hdim : Module.finrank (ZMod p) X < Module.finrank (ZMod p) Z)
    (f : TensorGroup (evaluationTwist Y AlternatingBilinearMap.zero) ≃*
      TensorGroup (evaluationTwist Y ε)) (g) :
    (f g).fst.1 = 0 ↔ g.fst.1 = 0 := by
  change (TensorGroup.equivProd (f g)).1.1 = 0 ↔ (TensorGroup.equivProd g).1.1 = 0
  rw [matrixSector_iff_adjoint_finrank_lt Y ε heval hdim (TensorGroup.equivProd (f g)),
    matrixSector_iff_adjoint_finrank_lt Y AlternatingBilinearMap.zero heval hdim
      (TensorGroup.equivProd g)]
  rw [tensorAdjoint_finrank_invariant f (TensorGroup.equivProd g)]
  rfl

/-- The zero-twist isomorphism criterion for arbitrary abstract group
isomorphisms. The remaining assumptions are the explicit evaluation and
dimension properties of the manuscript's padded construction. -/
theorem zero_twist_iff_group_iso
    (heval : ∀ x : X, x ≠ 0 → Function.Surjective (fun y : Y => (y : X →ₗ[ZMod p] Z) x))
    (hdim : Module.finrank (ZMod p) X < Module.finrank (ZMod p) Z) :
    (∃ α : X →ₗ[ZMod p] Y, ∀ x x', shearCoboundary Y α x x' = ε x x') ↔
      Nonempty (TensorGroup (evaluationTwist Y AlternatingBilinearMap.zero) ≃*
        TensorGroup (evaluationTwist Y ε)) := by
  constructor
  · rintro ⟨α, hα⟩
    exact ⟨evaluationShearMulEquiv Y α ε hα⟩
  · rintro ⟨f⟩
    exact derivative_of_sector_preserving_group_iso Y ε f
      (group_iso_preserves_matrixSector Y ε heval hdim f)

end FullCriterion
end GroupWL
