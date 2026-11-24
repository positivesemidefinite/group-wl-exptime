import GroupWL.IncidenceRank
import GroupWL.CoordinateBlocks

namespace GroupWL
namespace IncidenceBudget

open IncidenceTensor
universe u
variable {F I J : Type u} [Field F] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {V : J → Type u} [∀ j, AddCommGroup (V j)] [∀ j, Module F (V j)]
variable (A : AffineSystem F I J V)

/-- Embed all scalar coordinate directions in the actual padded input space. -/
def scalarEmbedding (q : ℕ) :
    ((I ⊕ J) → Fin q → F) →ₗ[F] PaddedInput A q where
  toFun x := (fun v a => TrivSqZeroExt.inl (x v a), 0)
  map_add' x y := by
    apply Prod.ext
    · funext v a
      exact TrivSqZeroExt.inl_add _ _ _
    · simp
  map_smul' c x := by
    apply Prod.ext
    · funext v a
      exact TrivSqZeroExt.inl_smul (Radical A v) c (x v a)
    · simp

/-- The embedding retains every scalar coordinate exactly. -/
theorem scalarEmbedding_injective (q : ℕ) : Function.Injective (scalarEmbedding A q) := by
  intro x y h
  funext v a
  exact congrArg (fun z : PaddedInput A q => (z.1 v a).fst) h

/-- The manuscript's scalar unit subspace `S_v` at one vertex. -/
def scalarSubspace (q : ℕ) (v : I ⊕ J) : Submodule F (PaddedInput A q) :=
  (CoordinateBlocks.atVertex (F := F) (W := Fin q → F) v).map (scalarEmbedding A q)

/-- Distinct vertices have independent scalar coordinate subspaces. -/
theorem scalarSubspace_independent (q : ℕ) : iSupIndep (scalarSubspace A q) :=
  (scalarEmbedding A q).iSupIndep_map (scalarEmbedding_injective A q)
    CoordinateBlocks.independent

/-- Every scalar coordinate subspace has dimension exactly `q`. -/
theorem scalarSubspace_finrank (q : ℕ) (v : I ⊕ J) :
    Module.finrank F (scalarSubspace A q v) = q := by
  have he := (Submodule.equivMapOfInjective (scalarEmbedding A q)
    (scalarEmbedding_injective A q)
    (CoordinateBlocks.atVertex (F := F) (W := Fin q → F) v)).finrank_eq
  unfold scalarSubspace
  rw [← he]
  exact CoordinateBlocks.finrank_scalarFrame v q

/-- Bad vertices for the actual padded incidence input. -/
noncomputable def badVertices (q : ℕ) (E : Submodule F (PaddedInput A q)) : Finset (I ⊕ J) :=
  BadBudget.badVertices (scalarSubspace A q) E q

/-- The dimension definition agrees with rank at most one of scalar restrictions. -/
theorem mem_badVertices_iff (q : ℕ) (E : Submodule F (PaddedInput A q)) (v : I ⊕ J) :
    v ∈ badVertices A q E ↔
      Module.finrank F (RestrictionRank.restriction E (scalarSubspace A q v)).range ≤ 1 := by
  rw [badVertices, BadBudget.mem_badVertices]
  exact (RestrictionRank.bad_iff_intersection E (scalarSubspace A q v) q
    (scalarSubspace_finrank A q v)).symm

/-- The concrete bad-vertex dimension inequality. -/
theorem badVertices_budget (q : ℕ) (E : Submodule F (PaddedInput A q)) :
    (q - 1) * (badVertices A q E).card ≤ Module.finrank F E :=
  BadBudget.badVertices_budget _ (scalarSubspace_independent A q) E q

/-- At most `K` equation owners are needed for any span satisfying the stated
pebble budget. The owner map is fixed once for the affine instance. -/
theorem owner_budget (q K : ℕ) (hq : 1 < q)
    (owner : I ⊕ J → I) (E : Submodule F (PaddedInput A q))
    (hbudget : Module.finrank F E < (q - 1) * (K + 1)) :
    (BadBudget.ownerSet owner (scalarSubspace A q) E q).card ≤ K :=
  BadBudget.ownerSet_card_le_of_budget owner _ (scalarSubspace_independent A q)
    E q K hq hbudget

end IncidenceBudget
end GroupWL
