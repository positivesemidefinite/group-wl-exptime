import GroupWL.LocalMultiplier
import Mathlib.LinearAlgebra.Dimension.Finite

/-! The rank bound underlying the tensor construction, proved by its explicit
independent unit-input columns.  Output coordinates are ordered pairs; passing
to unordered alternating coordinates does not change this independence. -/
namespace GroupWL
namespace RankBound

open scoped BigOperators
variable {F : Type*} [Field F] {N : Type*} [AddCommGroup N] [Module F N]
variable {ι : Type*} [DecidableEq ι]

/-- The column of the alternating multiplication tensor at a scalar unit input.
The expression uses only addition, so the rank argument works for any vector
space of output coefficients. -/
def column (a : ι → N) (j : ι) : ι × ι → N :=
  fun z => (if z.2 = j then a z.1 else 0) - (if z.1 = j then a z.2 else 0)

lemma column_star (a : ι → N) (i : ι) (j k : {j : ι // j ≠ i}) :
    column a k.1 (i, j.1) = if k = j then a i else 0 := by
  simp only [column, ne_comm.mp k.property, ↓reduceIte, sub_zero]
  simp only [Subtype.ext_iff, eq_comm]

/-- A nonzero coordinate yields independent columns at all other scalar inputs. -/
theorem independent_columns (a : ι → N) (i : ι) (ha : a i ≠ 0) :
    LinearIndependent F (fun j : {j : ι // j ≠ i} => column a j.1) := by
  classical
  rw [linearIndependent_iff']
  intro s c hsum j hj
  have he := congrArg (fun v : ι × ι → N => v (i, j.1)) hsum
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, column_star] at he
  have he' : c j • a i = 0 := by
    simpa only [smul_ite, smul_zero, Finset.sum_ite_eq', hj, ↓reduceIte] using he
  exact (smul_eq_zero.mp he').resolve_right ha

/-- Any output subspace containing these columns has dimension at least `q-1`. -/
theorem dimension_lower_bound [Fintype ι]
    (a : ι → N) (i : ι) (ha : a i ≠ 0)
    (S : Submodule F (ι × ι → N)) [Module.Finite F S]
    (hS : ∀ j : {j : ι // j ≠ i}, column a j.1 ∈ S) :
    Fintype.card ι - 1 ≤ Module.finrank F S := by
  let v : {j : ι // j ≠ i} → S := fun j => ⟨column a j.1, hS j⟩
  have hv : LinearIndependent F v :=
    LinearIndependent.of_comp S.subtype (independent_columns a i ha)
  have hcard := hv.fintype_card_le_finrank
  simpa only [Fintype.card_subtype_compl, Fintype.card_unique] using hcard

section RingTensor

variable {R : Type*} [CommRing R] [Algebra F R]

/-- The local wedge map `x ↦ a ∧ x`, as an `F`-linear map. -/
def wedgeLinear (a : ι → R) : (ι → R) →ₗ[F] (ι × ι → R) where
  toFun x z := a z.1 * x z.2 - a z.2 * x z.1
  map_add' x y := by ext z; simp only [Pi.add_apply]; ring
  map_smul' c x := by
    ext z
    simp only [Pi.smul_apply, RingHom.id_apply, mul_smul_comm, smul_sub]

/-- Its scalar-unit columns are exactly the independent columns above. -/
theorem wedgeLinear_unit (a : ι → R) (j : ι) :
    wedgeLinear (F := F) a (Pi.single j 1) = column a j := by
  ext z
  simp only [wedgeLinear, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_apply,
    column, mul_ite, mul_one, mul_zero]

/-- The actual local wedge map has rank at least `q-1` at every nonzero input. -/
theorem wedgeLinear_rank_lower [Fintype ι] [Module.Finite F R]
    (a : ι → R) (ha : a ≠ 0) :
    Fintype.card ι - 1 ≤ Module.finrank F (wedgeLinear (F := F) a).range := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra! hz
    exact ha (funext hz)
  apply dimension_lower_bound a i hi (wedgeLinear (F := F) a).range
  intro j
  exact ⟨Pi.single j.1 1, wedgeLinear_unit a j.1⟩

end RingTensor

/-- The same lower bound applies when the local columns are extracted from a
larger tensor output.  Thus additional incidence and padding coordinates do
not weaken the bound. -/
theorem rank_lower_of_projected_columns [Fintype ι]
    {X Z : Type*} [AddCommGroup X] [Module F X] [AddCommGroup Z] [Module F Z]
    (L : X →ₗ[F] Z) [Module.Finite F L.range]
    (π : Z →ₗ[F] (ι × ι → N))
    (a : ι → N) (i : ι) (ha : a i ≠ 0)
    (u : {j : ι // j ≠ i} → X)
    (hu : ∀ j, π (L (u j)) = column a j.1) :
    Fintype.card ι - 1 ≤ Module.finrank F L.range := by
  let v : {j : ι // j ≠ i} → L.range := fun j => ⟨L (u j), ⟨u j, rfl⟩⟩
  have hv : LinearIndependent F v := by
    apply LinearIndependent.of_comp (π.comp L.range.subtype)
    convert independent_columns a i ha using 1
    funext j
    exact hu j
  have hcard := hv.fintype_card_le_finrank
  simpa only [Fintype.card_subtype_compl, Fintype.card_unique] using hcard

end RankBound
end GroupWL
