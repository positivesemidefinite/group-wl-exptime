import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-!
# Local multiplier rigidity

The local multiplier argument in the manuscript is a consequence of a stronger
commutative-ring statement: two vectors with a unit coordinate minor suffice.
No nondegeneracy of a restricted dot product is used.
-/

namespace GroupWL
namespace LocalMultiplier

variable {R : Type*} [CommRing R] {ι : Type*}

/-- An ordered coordinate minor. -/
def minor (x y : ι → R) (i j : ι) : R := x i * y j - x j * y i

/-- A vector whose wedge with `x` vanishes is a scalar multiple of `x`,
provided `x` participates in a unit minor.  This works over arbitrary
commutative rings, including rings with zero divisors. -/
theorem eq_mul_of_unit_minor {x y v : ι → R} {i j : ι}
    (hunit : IsUnit (minor x y i j))
    (hw : ∀ k l, v k * x l = v l * x k) :
    ∃ r : R, ∀ k, v k = r * x k := by
  obtain ⟨d, _, hd⟩ := isUnit_iff_exists.mp hunit
  refine ⟨d * (v i * y j - v j * y i), ?_⟩
  intro k
  calc
    v k = d * (minor x y i j * v k) := by rw [← mul_assoc, hd, one_mul]
    _ = d * ((v i * y j - v j * y i) * x k) := by
      congr 1
      dsimp [minor]
      linear_combination -(y j) * hw i k + y i * hw j k
    _ = _ := by ring

/-- A unit minor detects a scalar that annihilates the wedge. -/
theorem scalar_eq_zero {x y : ι → R} {i j : ι} {c : R}
    (hunit : IsUnit (minor x y i j))
    (h : (c * x i) * y j = (c * x j) * y i) : c = 0 := by
  apply hunit.mul_right_cancel
  dsimp [minor]
  linear_combination h

variable {U : Type*} [AddCommGroup U]

/-- Polarization uses additivity only; in particular it does not divide by two. -/
theorem polarized (f g : U →+ (ι → R))
    (h : ∀ u i j, f u i * g u j = f u j * g u i)
    (u v : U) (i j : ι) :
    f u i * g v j + f v i * g u j =
      f u j * g v i + f v j * g u i := by
  have huv := h (u + v) i j
  simp only [map_add, Pi.add_apply] at huv
  linear_combination huv - h u i j - h v i j

/-- If an additive operator has zero wedge with an additive vector-valued map
on every diagonal, and the latter has a unit two-by-two minor, then the
operator is multiplication by one uniquely determined ring element. -/
theorem existsUnique_multiplier (f g : U →+ (ι → R))
    (h : ∀ u i j, f u i * g u j = f u j * g u i)
    (a b : U) (i j : ι) (hunit : IsUnit (minor (g a) (g b) i j)) :
    ∃! r : R, ∀ u k, f u k = r * g u k := by
  obtain ⟨r, hr⟩ := eq_mul_of_unit_minor hunit (h a)
  let d : U →+ (ι → R) := f - r • g
  have hd (u : U) (k : ι) : d u k = f u k - r * g u k := rfl
  have hdiag (u : U) (k l : ι) : d u k * g u l = d u l * g u k := by
    simp only [hd]
    linear_combination h u k l
  have hda (k : ι) : d a k = 0 := by rw [hd, hr, sub_self]
  have hparallel (u : U) (k l : ι) : d u k * g a l = d u l * g a k := by
    have hp := polarized d g hdiag u a k l
    simpa only [hda, zero_mul, add_zero] using hp
  have hdb (k : ι) : d b k = 0 := by
    obtain ⟨s, hs⟩ := eq_mul_of_unit_minor hunit (hparallel b)
    have hs0 : s = 0 := scalar_eq_zero hunit (by simpa only [hs] using hdiag b i j)
    rw [hs, hs0, zero_mul]
  have hz (u : U) (k : ι) : d u k = 0 := by
    obtain ⟨s, hs⟩ := eq_mul_of_unit_minor hunit (hparallel u)
    have hp := polarized d g hdiag u b i j
    simp only [hdb, zero_mul, add_zero] at hp
    have hs0 : s = 0 := scalar_eq_zero hunit (by simpa only [hs] using hp)
    rw [hs, hs0, zero_mul]
  have hall (u : U) (k : ι) : f u k = r * g u k := sub_eq_zero.mp (hz u k)
  refine ⟨r, hall, ?_⟩
  intro s hs
  apply hunit.mul_right_cancel
  dsimp [minor]
  linear_combination -(g b j) * (hs a i) + g b i * (hs a j) +
    g b j * (hall a i) - g b i * (hall a j)

section ScalarProjection

variable {F : Type*} [Field F]

/-- Linear independence of two coordinate vectors is detected by a nonzero minor. -/
theorem exists_minor_ne_zero {x y : ι → F}
    (h : LinearIndependent F ![x, y]) : ∃ i j, minor x y i j ≠ 0 := by
  classical
  by_contra! hz
  have hy : y ≠ 0 := by simpa using h.ne_zero 1
  obtain ⟨j, hj⟩ : ∃ j, y j ≠ 0 := by
    by_contra! hzero
    exact hy (funext hzero)
  apply (linearIndependent_fin2.mp h).2 (x j / y j)
  funext i
  change x j / y j * y i = x i
  rw [div_mul_eq_mul_div]
  exact (div_eq_iff hj).2 (sub_eq_zero.mp (hz i j)).symm

/-- Scalar independence is enough when nonzero scalar parts detect units. -/
theorem existsUnique_of_independent_scalars (π : R →+* F)
    (hπ : ∀ r, π r ≠ 0 → IsUnit r)
    (f g : U →+ (ι → R))
    (h : ∀ u i j, f u i * g u j = f u j * g u i)
    (a b : U)
    (hind : LinearIndependent F
      ![fun k => π (g a k), fun k => π (g b k)]) :
    ∃! r : R, ∀ u k, f u k = r * g u k := by
  obtain ⟨i, j, hij⟩ := exists_minor_ne_zero hind
  apply existsUnique_multiplier f g h a b i j
  apply hπ
  simpa only [minor, map_sub, map_mul] using hij

/-- The scalar projection of a trivial square-zero extension. -/
def scalarProjection {N : Type*} [AddCommGroup N]
    [Module F N] [Module Fᵐᵒᵖ N] [IsCentralScalar F N] :
    TrivSqZeroExt F N →+* F where
  toFun := TrivSqZeroExt.fst
  map_zero' := rfl
  map_one' := rfl
  map_add' := fun _ _ => rfl
  map_mul' := fun _ _ => rfl

/-- The square-zero extension has a unit exactly when its scalar part is nonzero. -/
theorem squareZero_isUnit_iff {N : Type*} [AddCommGroup N]
    [Module F N] [Module Fᵐᵒᵖ N] [IsCentralScalar F N]
    (r : TrivSqZeroExt F N) : IsUnit r ↔ r.fst ≠ 0 := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero]

/-- The local multiplier lemma for the actual rings used in the manuscript,
with the two independent scalar vectors stated explicitly. -/
theorem squareZero_existsUnique_multiplier {N : Type*} [AddCommGroup N]
    [Module F N] [Module Fᵐᵒᵖ N] [IsCentralScalar F N]
    (f g : U →+ (ι → TrivSqZeroExt F N))
    (h : ∀ u i j, f u i * g u j = f u j * g u i)
    (a b : U)
    (hind : LinearIndependent F
      ![fun k => (g a k).fst, fun k => (g b k).fst]) :
    ∃! r : TrivSqZeroExt F N, ∀ u k, f u k = r * g u k :=
  existsUnique_of_independent_scalars (R := TrivSqZeroExt F N) (F := F)
    (scalarProjection (F := F) (N := N))
    (fun r hr => (squareZero_isUnit_iff (F := F) (N := N) r).2 hr) f g h a b hind

/-- An image of dimension at least two contains two independent images. -/
theorem independent_images_of_one_lt_finrank [Module F U]
    (g : U →ₗ[F] (ι → F)) (hg : 1 < Module.finrank F g.range) :
    ∃ a b, LinearIndependent F ![g a, g b] := by
  letI : Nontrivial g.range := Module.nontrivial_of_finrank_pos (lt_trans Nat.zero_lt_one hg)
  obtain ⟨x, hx⟩ := exists_ne (0 : g.range)
  obtain ⟨y, hxy⟩ := exists_linearIndependent_pair_of_one_lt_finrank hg hx
  obtain ⟨a, ha⟩ := x.property
  obtain ⟨b, hb⟩ := y.property
  refine ⟨a, b, ?_⟩
  have hm := hxy.map' g.range.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  rw [ha, hb]
  convert hm using 1
  ext k
  fin_cases k <;> rfl

/-- Coordinatewise scalar projection of a linear map into a square-zero ring. -/
def scalarMap {N : Type*} [AddCommGroup N] [Module F U]
    [Module F N] [Module Fᵐᵒᵖ N] [IsCentralScalar F N]
    (g : U →ₗ[F] (ι → TrivSqZeroExt F N)) : U →ₗ[F] (ι → F) where
  toFun u k := (g u k).fst
  map_add' u v := by ext k; simp only [map_add, Pi.add_apply, TrivSqZeroExt.fst_add]
  map_smul' c u := by ext k; simp only [map_smul, Pi.smul_apply, TrivSqZeroExt.fst_smul, RingHom.id_apply]

/-- The manuscript's good-vertex local multiplier statement, using exactly
rank at least two of the scalar projection. -/
theorem squareZero_existsUnique_multiplier_of_rank {N : Type*} [AddCommGroup N]
    [Module F U] [Module F N] [Module Fᵐᵒᵖ N] [IsCentralScalar F N]
    (f g : U →ₗ[F] (ι → TrivSqZeroExt F N))
    (h : ∀ u i j, f u i * g u j = f u j * g u i)
    (hg : 1 < Module.finrank F (scalarMap g).range) :
    ∃! r : TrivSqZeroExt F N, ∀ u k, f u k = r * g u k := by
  obtain ⟨a, b, hab⟩ := independent_images_of_one_lt_finrank (scalarMap g) hg
  exact squareZero_existsUnique_multiplier f.toAddMonoidHom g.toAddMonoidHom h a b hab

end ScalarProjection

/-- Equality of the multipliers across an incidence follows from one diagonal
incidence equation with unit input coordinates. -/
theorem incidence_compatibility {r s x y : R}
    (hx : IsUnit x) (hy : IsUnit y) (h : (r * x) * y = (s * y) * x) : r = s := by
  apply (hx.mul hy).mul_right_cancel
  linear_combination h

/-- Two proper additive kernels do not cover the source.  This elementary
argument works in every characteristic, including fields of order two. -/
theorem exists_common_nonzero {F : Type*} [Field F]
    (f g : U →+ F) (hf : ∃ a, f a ≠ 0) (hg : ∃ b, g b ≠ 0) :
    ∃ u, f u ≠ 0 ∧ g u ≠ 0 := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  by_cases hga : g a = 0
  · by_cases hfb : f b = 0
    · exact ⟨a + b, by simpa only [map_add, hfb, add_zero] using ha,
        by simpa only [map_add, hga, zero_add] using hb⟩
    · exact ⟨b, hfb, hb⟩
  · exact ⟨a, ha, hga⟩

/-- Compatibility can be tested on one common nonzero scalar query; such a
query is obtained from separate nonzero witnesses at the two endpoints. -/
theorem incidence_compatibility_of_nonzero_scalars {F : Type*} [Field F]
    (π : R →+* F) (hπ : ∀ z, π z ≠ 0 → IsUnit z)
    (x y : U →+ R) {r s : R}
    (hx : ∃ u, π (x u) ≠ 0) (hy : ∃ u, π (y u) ≠ 0)
    (h : ∀ u, (r * x u) * y u = (s * y u) * x u) : r = s := by
  obtain ⟨u, hxu, hyu⟩ := exists_common_nonzero
    (π.toAddMonoidHom.comp x) (π.toAddMonoidHom.comp y) hx hy
  exact incidence_compatibility (hπ (x u) hxu) (hπ (y u) hyu) (h u)

end LocalMultiplier
end GroupWL
