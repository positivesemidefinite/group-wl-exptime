import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-! The scalar-restriction rank calculation is most naturally stated with the
canonical pairing between a vector space and its dual. This avoids assuming
that an orthogonal subspace is nondegenerate. -/
namespace GroupWL
namespace RestrictionRank

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  [Module.Finite F V]

/-- Restrict functionals annihilating `E` to the scalar-coordinate space `S`. -/
def restriction (E S : Submodule F V) : E.dualAnnihilator →ₗ[F] Module.Dual F S :=
  S.dualRestrict.comp E.dualAnnihilator.subtype

lemma ker_restriction (E S : Submodule F V) :
    (restriction E S).ker =
      (E ⊔ S).dualAnnihilator.comap E.dualAnnihilator.subtype := by
  rw [restriction, LinearMap.ker_comp, Submodule.dualRestrict_ker_eq_dualAnnihilator]
  ext f
  simp only [Submodule.mem_comap, Submodule.dualAnnihilator_sup_eq, Submodule.mem_inf]
  exact ⟨fun h => ⟨f.property, h⟩, And.right⟩

/-- Rank of restricted scalar functionals plus the retained scalar directions
is the full number of scalar directions. -/
theorem rank_add_intersection (E S : Submodule F V) :
    Module.finrank F (restriction E S).range + Module.finrank F ↥(E ⊓ S) =
      Module.finrank F S := by
  have hle : (E ⊔ S).dualAnnihilator ≤ E.dualAnnihilator := by
    rw [Submodule.dualAnnihilator_sup_eq]
    exact inf_le_left
  have hk : Module.finrank F (restriction E S).ker =
      Module.finrank F (E ⊔ S).dualAnnihilator := by
    rw [ker_restriction]
    exact (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
  have hr := LinearMap.finrank_range_add_finrank_ker (K := F)
    (V := E.dualAnnihilator) (V₂ := Module.Dual F S) (restriction E S)
  rw [hk] at hr
  have hE := Subspace.finrank_add_finrank_dualAnnihilator_eq E
  have hES := Subspace.finrank_add_finrank_dualAnnihilator_eq (E ⊔ S)
  have hi := Submodule.finrank_sup_add_finrank_inf_eq E S
  omega

/-- In a `q`-dimensional coordinate block, rank at most one is equivalent to
at least `q-1` retained scalar directions. -/
theorem bad_iff_intersection (E S : Submodule F V) (q : ℕ)
    (hS : Module.finrank F S = q) :
    Module.finrank F (restriction E S).range ≤ 1 ↔
      q - 1 ≤ Module.finrank F ↥(E ⊓ S) := by
  have h := rank_add_intersection E S
  rw [hS] at h
  omega

end RestrictionRank
end GroupWL
