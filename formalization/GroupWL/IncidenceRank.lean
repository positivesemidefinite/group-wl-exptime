import GroupWL.IncidenceTensor
import GroupWL.RankOneExclusion

namespace GroupWL
namespace IncidenceRank

open IncidenceTensor
universe u
variable {F I J : Type u} [Field F] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {V : J → Type u} [∀ j, AddCommGroup (V j)] [∀ j, Module F (V j)]
variable (A : AffineSystem F I J V)

instance ringAtFiniteDimensional (v : I ⊕ J) : Module.Finite F (RingAt A v) :=
  inferInstanceAs (Module.Finite F (F × Radical A v))

instance edgeRingFiniteDimensional : Module.Finite F (EdgeRing (F := F)) :=
  inferInstanceAs (Module.Finite F (F × F))

/-- Recover the ordered internal wedge coordinates from the stored triangular
ones. The added input and output sectors are ignored by this projection. -/
def internalProjection (q : ℕ) (v : I ⊕ J) :
    PaddedOutput A q →ₗ[F] (Fin q × Fin q → RingAt A v) where
  toFun z ab := if h : ab.1 < ab.2 then z.1.1 v ⟨ab, h⟩
    else if h' : ab.2 < ab.1 then -z.1.1 v ⟨(ab.2, ab.1), h'⟩ else 0
  map_add' x y := by
    funext ab
    dsimp
    split_ifs <;> simp_all [add_comm]
  map_smul' c x := by
    funext ab
    dsimp
    split_ifs <;> simp_all [add_comm]

/-- Projection recovers the whole local wedge map, including the diagonal and
reversed coordinate pairs. -/
theorem internalProjection_slice (q : ℕ) (v : I ⊕ J)
    (a : OldInput A q) (x : PaddedInput A q) (i j : Fin q) :
    internalProjection A q v (sliceMap A q a x) (i, j) =
      a v i * x.1 v j - a v j * x.1 v i := by
  simp only [internalProjection, LinearMap.coe_mk, AddHom.coe_mk,
    sliceMap_apply, omega_internal]
  split_ifs with hij hji
  · ring
  · ring
  · have heq : i = j := le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
    subst j
    ring

/-- One scalar unit in one old input coordinate. -/
def unitInput (q : ℕ) (v : I ⊕ J) (j : Fin q) : PaddedInput A q :=
  (Pi.single v (Pi.single j 1), 0)

/-- These inputs expose exactly the unit columns used in the rank proof. -/
theorem projected_unit (q : ℕ) (v : I ⊕ J) (a : OldInput A q) (j : Fin q) :
    internalProjection A q v (sliceMap A q a (unitInput A q v j)) =
      RankBound.column (a v) j := by
  funext ab
  rcases ab with ⟨i, k⟩
  rw [internalProjection_slice]
  simp only [unitInput, Pi.single_eq_same]
  simp only [Pi.single_apply, RankBound.column, mul_ite, mul_one, mul_zero]

/-- Every nonzero slice of the actual padded incidence tensor has rank at
least `q-1`. This includes slices supported purely in radicals. -/
theorem slice_rank_lower (q : ℕ) (a : OldInput A q) (ha : a ≠ 0) :
    q - 1 ≤ Module.finrank F (sliceMap A q a).range := by
  classical
  obtain ⟨v, i, hi⟩ : ∃ v i, a v i ≠ 0 := by
    by_contra! hz
    exact ha (funext fun v => funext (hz v))
  have h := RankBound.rank_lower_of_projected_columns
    (sliceMap A q a) (internalProjection A q v) (a v) i hi
    (fun j => unitInput A q v j.1) (fun j => projected_unit A q v a j.1)
  simpa only [Fintype.card_fin] using h

/-- The slice map is injective as soon as there are at least two coordinates. -/
theorem sliceMap_injective (q : ℕ) (hq : 2 ≤ q) :
    Function.Injective (sliceMap A q) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro a ha
  change a = 0
  by_contra hne
  have h := slice_rank_lower A q a hne
  rw [LinearMap.mem_ker.mp ha] at h
  have hz : Module.finrank F (0 : PaddedInput A q →ₗ[F] PaddedOutput A q).range = 0 := by
    rw [LinearMap.range_zero, finrank_bot]
  rw [hz] at h
  omega

/-- Hence every nonzero matrix in the actual obstruction space has rank at
least `q-1`, independently of the chosen component anchors. -/
theorem obstructionSpace_rank_lower (q : ℕ)
    (anchors : Set ((I ⊕ J) × Fin q))
    (c : PaddedInput A q →ₗ[F] PaddedOutput A q)
    (hc : c ∈ obstructionSpace A q anchors) (hne : c ≠ 0) :
    q - 1 ≤ Module.finrank F c.range := by
  obtain ⟨a, _, rfl⟩ := hc
  apply slice_rank_lower A q a
  intro ha
  exact hne (by simp [ha])

/-- The form needed to exclude rank-one obstruction matrices. -/
theorem obstructionSpace_rank_ge_two (q : ℕ) (hq : 3 ≤ q)
    (anchors : Set ((I ⊕ J) × Fin q))
    (c : PaddedInput A q →ₗ[F] PaddedOutput A q)
    (hc : c ∈ obstructionSpace A q anchors) (hne : c ≠ 0) :
    2 ≤ Module.finrank F c.range := by
  have h := obstructionSpace_rank_lower A q anchors c hc hne
  omega

end IncidenceRank
end GroupWL
