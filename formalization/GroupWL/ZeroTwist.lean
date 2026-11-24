import GroupWL.TensorLinearity
import GroupWL.RecognitionAlgebra

/-! # Actual group isomorphisms and the zero-twist obstruction

The only extra premise in the converse is preservation of the matrix sector
`x = 0`. The manuscript obtains that premise from centralizer cardinalities.
The group isomorphism is otherwise arbitrary: its coordinate linearity is
proved in `TensorLinearity`, not assumed.
-/

namespace GroupWL

section Quotient

variable {F X Y Z : Type*} [Field F]
  [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]
  [AddCommGroup Z] [Module F Z]

def quotientBlock (E : ((X × Y) × Z) ≃ₗ[F] (X × Y) × Z) : X →ₗ[F] X where
  toFun x := (E ((x, 0), 0)).1.1
  map_add' x y := by
    have : (((x + y, 0), 0) : (X × Y) × Z) = ((x, 0), 0) + ((y, 0), 0) := by
      ext <;> simp
    rw [this, map_add]
    rfl
  map_smul' a x := by
    have : (((a • x, 0), 0) : (X × Y) × Z) = a • ((x, 0), 0) := by
      ext <;> simp
    rw [this, map_smul]
    rfl

theorem quotientBlock_depends_only_on_quotient
    (E : ((X × Y) × Z) ≃ₗ[F] (X × Y) × Z)
    (hE : ∀ v, (E v).1.1 = 0 ↔ v.1.1 = 0) (v : (X × Y) × Z) :
    (E v).1.1 = quotientBlock E v.1.1 := by
  have hz : (E ((0, v.1.2), v.2)).1.1 = 0 := (hE _).2 rfl
  have hv : v = ((v.1.1, 0), 0) + ((0, v.1.2), v.2) := by ext <;> simp
  conv_lhs => rw [hv, map_add]
  change (E ((v.1.1, 0), 0)).1.1 + (E ((0, v.1.2), v.2)).1.1 = _
  rw [hz, add_zero]
  rfl

theorem quotientBlock_bijective
    (E : ((X × Y) × Z) ≃ₗ[F] (X × Y) × Z)
    (hE : ∀ v, (E v).1.1 = 0 ↔ v.1.1 = 0) :
    Function.Bijective (quotientBlock E) := by
  constructor
  · intro x y hxy
    have hzero : quotientBlock E (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have : x - y = 0 := (hE ((x - y, 0), 0)).1 hzero
    exact sub_eq_zero.mp this
  · intro x
    obtain ⟨v, hv⟩ := E.surjective ((x, 0), 0)
    refine ⟨v.1.1, ?_⟩
    rw [← quotientBlock_depends_only_on_quotient E hE, hv]

noncomputable def quotientBlockEquiv
    (E : ((X × Y) × Z) ≃ₗ[F] (X × Y) × Z)
    (hE : ∀ v, (E v).1.1 = 0 ↔ v.1.1 = 0) : X ≃ₗ[F] X :=
  LinearEquiv.ofBijective (quotientBlock E) (quotientBlock_bijective E hE)

end Quotient

section GroupCriterion

variable {p : ℕ} [Fact p.Prime] [NeZero (2 : ZMod p)]
variable {X Z : Type*} [AddCommGroup X] [Module (ZMod p) X]
  [AddCommGroup Z] [Module (ZMod p) Z]
variable (Y : Submodule (ZMod p) (X →ₗ[ZMod p] Z))
variable (ε : AlternatingBilinearMap (ZMod p) X Z)

theorem derivative_of_sector_preserving_group_iso
    (f : TensorGroup (evaluationTwist Y AlternatingBilinearMap.zero) ≃*
      TensorGroup (evaluationTwist Y ε))
    (hB : ∀ g, (f g).fst.1 = 0 ↔ g.fst.1 = 0) :
    ∃ α : X →ₗ[ZMod p] Y, ∀ x x', shearCoboundary Y α x x' = ε x x' := by
  let E := TensorGroup.equivLinearEquiv f
  have hE : ∀ v, (E v).1.1 = 0 ↔ v.1.1 = 0 := by
    intro v
    exact hB (TensorGroup.equivProd.symm v)
  let C := quotientBlockEquiv E hE
  let s : X →ₗ[ZMod p] X × Y :=
    (LinearMap.fst (ZMod p) (X × Y) Z).comp
      (E.toLinearMap.comp
        ((LinearMap.inl (ZMod p) (X × Y) Z).comp (LinearMap.inl (ZMod p) X Y)))
  have hC : ∀ x, (s x).1 = C x := fun _ => rfl
  have hs : ∀ x x', evaluationBracket Y.subtype ε.toLinearMap (s x) (s x') = 0 := by
    intro x x'
    let g : TensorGroup (evaluationTwist Y AlternatingBilinearMap.zero) := ⟨(x, 0), 0⟩
    let h : TensorGroup (evaluationTwist Y AlternatingBilinearMap.zero) := ⟨(x', 0), 0⟩
    have hgh : g * h = h * g := by
      apply (TensorGroup.mul_comm_iff g h).2
      simp [g, h, evaluationTwist_apply]
    have hfg : f g * f h = f h * f g := by
      rw [← map_mul, hgh, map_mul]
    exact (TensorGroup.mul_comm_iff (f g) (f h)).1 hfg
  obtain ⟨α, hα⟩ := derivative_of_linear_section Y.subtype ε.toLinearMap s C hC hs
  exact ⟨α, hα⟩

/-- Zero twist is equivalent to an actual isomorphism preserving the matrix
sector. The reverse implication derives linearity from the group laws. -/
theorem zero_twist_iff_sector_preserving_group_iso :
    (∃ α : X →ₗ[ZMod p] Y, ∀ x x', shearCoboundary Y α x x' = ε x x') ↔
      ∃ f : TensorGroup (evaluationTwist Y AlternatingBilinearMap.zero) ≃*
        TensorGroup (evaluationTwist Y ε),
        ∀ g, (f g).fst.1 = 0 ↔ g.fst.1 = 0 := by
  constructor
  · rintro ⟨α, hα⟩
    exact ⟨evaluationShearMulEquiv Y α ε hα, fun _ => Iff.rfl⟩
  · rintro ⟨f, hB⟩
    exact derivative_of_sector_preserving_group_iso Y ε f hB

end GroupCriterion
end GroupWL
