import GroupWL.CharacteristicSector
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Concrete cardinality predicates for the characteristic matrix sector. -/

namespace GroupWL

section Kernel

variable {F V Z : Type*} [Field F] [NeZero (2 : F)]
  [AddCommGroup V] [Module F V] [AddCommGroup Z] [Module F Z]

/-- The actual group centralizer is the kernel of its commutator map. -/
def centralizerEquivKernel (b : AlternatingBilinearMap F V Z) (g : TensorGroup b) :
    {h : TensorGroup b // g * h = h * g} ≃
      LinearMap.ker (tensorAdjoint b (TensorGroup.equivProd g)) where
  toFun h := ⟨TensorGroup.equivProd h.val, by
    simpa [LinearMap.mem_ker, tensorAdjoint_apply] using
      (TensorGroup.mul_comm_iff g h.val).mp h.property⟩
  invFun u := ⟨TensorGroup.equivProd.symm u.val, by
    apply (TensorGroup.mul_comm_iff _ _).mpr
    have hu := u.property
    change (0, b g.fst u.val.1) = (0, 0) at hu
    exact congrArg Prod.snd hu⟩
  left_inv h := by apply Subtype.ext; rfl
  right_inv u := by apply Subtype.ext; rfl

end Kernel

section Cardinality

variable {p : ℕ} [Fact p.Prime] [NeZero (2 : ZMod p)]
variable {V Z : Type*} [AddCommGroup V] [Module (ZMod p) V]
  [AddCommGroup Z] [Module (ZMod p) Z]
  [FiniteDimensional (ZMod p) V] [FiniteDimensional (ZMod p) Z]

theorem centralizer_card_eq_pow_kernel (b : AlternatingBilinearMap (ZMod p) V Z)
    (g : TensorGroup b) :
    Nat.card {h : TensorGroup b // g * h = h * g} =
      p ^ Module.finrank (ZMod p)
        (LinearMap.ker (tensorAdjoint b (TensorGroup.equivProd g))) := by
  rw [Nat.card_congr (centralizerEquivKernel b g),
    Module.natCard_eq_pow_finrank (K := ZMod p)]
  simp

end Cardinality

section Evaluation

variable {p : ℕ} [Fact p.Prime] [NeZero (2 : ZMod p)]
variable {X Z : Type*} [AddCommGroup X] [Module (ZMod p) X]
  [AddCommGroup Z] [Module (ZMod p) Z]
  [FiniteDimensional (ZMod p) X] [FiniteDimensional (ZMod p) Z]
variable (Y : Submodule (ZMod p) (X →ₗ[ZMod p] Z))
  (ε : AlternatingBilinearMap (ZMod p) X Z)

/-- Coordinates on the matrix subgroup, including the central coordinate. -/
def matrixSectorEquiv :
    {g : TensorGroup (evaluationTwist Y ε) // g.fst.1 = 0} ≃ Y × Z where
  toFun g := (g.val.fst.2, g.val.snd)
  invFun u := ⟨⟨(0, u.1), u.2⟩, rfl⟩
  left_inv g := by
    apply Subtype.ext
    apply TensorGroup.ext
    · exact Prod.ext g.property.symm rfl
    · rfl
  right_inv u := rfl

omit [NeZero (2 : ZMod p)] in
theorem matrixSector_card :
    Nat.card {g : TensorGroup (evaluationTwist Y ε) // g.fst.1 = 0} =
      p ^ (Module.finrank (ZMod p) Y + Module.finrank (ZMod p) Z) := by
  rw [Nat.card_congr (matrixSectorEquiv Y ε),
    Module.natCard_eq_pow_finrank (K := ZMod p), Module.finrank_prod]
  simp

omit [FiniteDimensional (ZMod p) X] [FiniteDimensional (ZMod p) Z] in
theorem matrixSector_commutative
    (g h : TensorGroup (evaluationTwist Y ε))
    (hg : g.fst.1 = 0) (hh : h.fst.1 = 0) : g * h = h * g := by
  apply (TensorGroup.mul_comm_iff _ _).mpr
  simp [evaluationTwist_apply, hg, hh]

omit [NeZero (2 : ZMod p)] [FiniteDimensional (ZMod p) X] [FiniteDimensional (ZMod p) Z] in
theorem evaluation_separates_of_surjective
    (heval : ∀ x : X, x ≠ 0 →
      Function.Surjective (fun y : Y => (y : X →ₗ[ZMod p] Z) x))
    (hdim : Module.finrank (ZMod p) X < Module.finrank (ZMod p) Z)
    (x : X) (hx : ∀ y : Y, (y : X →ₗ[ZMod p] Z) x = 0) : x = 0 := by
  letI : Nontrivial Z := Module.nontrivial_of_finrank_pos (Nat.zero_le _ |>.trans_lt hdim)
  by_contra hne
  obtain ⟨z, hz⟩ := exists_ne (0 : Z)
  obtain ⟨y, hy⟩ := heval x hne z
  exact hz (hy.symm.trans (hx y))

def centerEquivOutput
    (hsep : ∀ x : X, (∀ y : Y, (y : X →ₗ[ZMod p] Z) x = 0) → x = 0) :
    Subgroup.center (TensorGroup (evaluationTwist Y ε)) ≃ Z where
  toFun g := g.val.snd
  invFun z := ⟨⟨0, z⟩, by
    rw [Subgroup.mem_center_iff]
    intro h
    exact ((evaluationGroup_center Y ε hsep ⟨0, z⟩).mpr rfl h).symm⟩
  left_inv g := by
    apply Subtype.ext
    apply TensorGroup.ext
    · symm
      apply (evaluationGroup_center Y ε hsep g.val).mp
      intro h
      exact (Subgroup.mem_center_iff.mp g.property h).symm
    · rfl
  right_inv z := rfl

omit [FiniteDimensional (ZMod p) X] in
theorem center_card
    (hsep : ∀ x : X, (∀ y : Y, (y : X →ₗ[ZMod p] Z) x = 0) → x = 0) :
    Nat.card (Subgroup.center (TensorGroup (evaluationTwist Y ε))) =
      p ^ Module.finrank (ZMod p) Z := by
  rw [Nat.card_congr (centerEquivOutput Y ε hsep),
    Module.natCard_eq_pow_finrank (K := ZMod p)]
  simp

/-- The strict centralizer threshold used by the manuscript recognizes exactly
the matrix sector, for every twist. -/
theorem matrixSector_iff_centralizer_card_gt
    (heval : ∀ x : X, x ≠ 0 →
      Function.Surjective (fun y : Y => (y : X →ₗ[ZMod p] Z) x))
    (hdim : Module.finrank (ZMod p) X < Module.finrank (ZMod p) Z)
    (g : TensorGroup (evaluationTwist Y ε)) :
    g.fst.1 = 0 ↔
      p ^ (Module.finrank (ZMod p) X + Module.finrank (ZMod p) Y) <
        Nat.card {h : TensorGroup (evaluationTwist Y ε) // g * h = h * g} := by
  rw [centralizer_card_eq_pow_kernel]
  rw [Nat.pow_lt_pow_iff_right (Fact.out : p.Prime).one_lt]
  have hrank := (tensorAdjoint (evaluationTwist Y ε)
    (TensorGroup.equivProd g)).finrank_range_add_finrank_ker
  simp only [Module.finrank_prod] at hrank
  have hsector := matrixSector_iff_adjoint_finrank_lt Y ε heval hdim
    (TensorGroup.equivProd g)
  change g.fst.1 = 0 ↔ _ at hsector
  rw [hsector]
  omega

end Evaluation

end GroupWL
