import GroupWL.TensorGroup
import Mathlib.Algebra.Module.ZMod
import Mathlib.Tactic

/-! # Group homomorphisms are linear in the displayed coordinates

Over a prime field of odd characteristic, coordinate addition is recovered
from multiplication and commutators. Consequently every group homomorphism
between tensor groups induces a linear map on their underlying vector spaces.
-/

namespace GroupWL.TensorGroup

variable {p : ℕ} [Fact p.Prime] [NeZero (2 : ZMod p)]
variable {V Z V' Z' : Type*}
variable [AddCommGroup V] [Module (ZMod p) V]
  [AddCommGroup Z] [Module (ZMod p) Z]
  [AddCommGroup V'] [Module (ZMod p) V']
  [AddCommGroup Z'] [Module (ZMod p) Z']
variable {b : AlternatingBilinearMap (ZMod p) V Z}
  {c : AlternatingBilinearMap (ZMod p) V' Z'}

/-- Addition in the displayed vector coordinates. -/
def coordinateAdd (g h : TensorGroup b) : TensorGroup b :=
  ⟨g.fst + h.fst, g.snd + h.snd⟩

/-- The class-two BCH formula, with the half exponent interpreted in the prime field. -/
theorem coordinateAdd_eq (g h : TensorGroup b) :
    coordinateAdd g h =
      (g * h) * ((g * h * g⁻¹ * h⁻¹) ^ ((2 : ZMod p)⁻¹).val)⁻¹ := by
  rw [commutator_eq, pow_eq]
  ext
  · simp [coordinateAdd]
  · simp only [coordinateAdd, mul_snd, inv_fst, inv_snd,
      neg_zero, AlternatingBilinearMap.zero_right, smul_zero, add_zero]
    rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
    abel

theorem map_coordinateAdd (f : TensorGroup b →* TensorGroup c) (g h : TensorGroup b) :
    f (coordinateAdd g h) = coordinateAdd (f g) (f h) := by
  rw [coordinateAdd_eq, coordinateAdd_eq]
  simp only [map_mul, map_inv, map_pow]

/-- The coordinate map of an arbitrary group homomorphism. -/
def homLinearMap (f : TensorGroup b →* TensorGroup c) :
    (V × Z) →ₗ[ZMod p] V' × Z' :=
  AddMonoidHom.toZModLinearMap p
    { toFun := fun x => equivProd (f (equivProd.symm x))
      map_zero' := by
        change equivProd (f 1) = 0
        rw [map_one]
        rfl
      map_add' := by
        intro x y
        change equivProd (f (coordinateAdd (equivProd.symm x) (equivProd.symm y))) = _
        rw [map_coordinateAdd]
        rfl }

@[simp] theorem homLinearMap_apply (f : TensorGroup b →* TensorGroup c) (x : V × Z) :
    homLinearMap f x = equivProd (f (equivProd.symm x)) := rfl

/-- Every abstract group isomorphism of these groups is linear in their
displayed vector coordinates. No coordinate-preservation hypothesis is used. -/
def equivLinearEquiv (f : TensorGroup b ≃* TensorGroup c) :
    (V × Z) ≃ₗ[ZMod p] V' × Z' where
  toLinearMap := homLinearMap f.toMonoidHom
  invFun := homLinearMap f.symm.toMonoidHom
  left_inv x := by simp
  right_inv x := by simp

@[simp] theorem equivLinearEquiv_apply (f : TensorGroup b ≃* TensorGroup c) (x : V × Z) :
    equivLinearEquiv f x = equivProd (f (equivProd.symm x)) := rfl

end GroupWL.TensorGroup
