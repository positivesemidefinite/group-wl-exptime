import GroupWL.IncidenceRank
import GroupWL.MatrixEvaluationGroup
import Mathlib.GroupTheory.Exponent

/-! # The concrete groups obtained from the affine incidence construction

The coordinate equivalences below are choices of bases. Rank, center, derived
subgroup, and exponent are proved for every such choice. In particular these
results apply to the manuscript's prescribed scalar-first radical bases.
-/

set_option linter.unusedSectionVars false

namespace GroupWL
namespace IncidenceGroup

open IncidenceTensor IncidenceRank ObstructionDuality
universe u
variable {F I J : Type u} [Field F] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {V : J → Type u} [∀ j, AddCommGroup (V j)] [∀ j, Module F (V j)]
variable (A : AffineSystem F I J V) (q : ℕ)
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Converting operators to matrices in the chosen input and output bases. -/
noncomputable def operatorCoordinates
    (eX : PaddedInput A q ≃ₗ[F] (ι → F))
    (eZ : PaddedOutput A q ≃ₗ[F] (κ → F)) :
    (PaddedInput A q →ₗ[F] PaddedOutput A q) ≃ₗ[F] MatrixSpace F ι κ :=
  (eX.arrowCongr eZ).trans matrixLinearEquiv.symm

/-- Matrix coordinates preserve the rank of every actual operator. -/
theorem operatorCoordinates_rank
    (eX : PaddedInput A q ≃ₗ[F] (ι → F))
    (eZ : PaddedOutput A q ≃ₗ[F] (κ → F))
    (c : PaddedInput A q →ₗ[F] PaddedOutput A q) :
    Module.finrank F (matrixToLinear (operatorCoordinates A q eX eZ c)).range =
      Module.finrank F c.range := by
  have heq : matrixToLinear (operatorCoordinates A q eX eZ c) =
      eZ.toLinearMap.comp (c.comp eX.symm.toLinearMap) := by
    change matrixLinearEquiv (matrixLinearEquiv.symm ((eX.arrowCongr eZ) c)) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  rw [heq, LinearMap.range_comp, LinearMap.range_comp,
    LinearEquiv.range, Submodule.map_top, LinearEquiv.finrank_map_eq]

/-- The concrete obstruction space in exactly the matrix representation used
for the orthogonal-complement evaluation group. -/
noncomputable def coordinateObstruction (hq : 0 < q)
    (eX : PaddedInput A q ≃ₗ[F] (ι → F))
    (eZ : PaddedOutput A q ≃ₗ[F] (κ → F)) : Submodule F (MatrixSpace F ι κ) :=
  (constructionObstructionSpace A q hq).map (operatorCoordinates A q eX eZ).toLinearMap

/-- Every nonzero matrix of the concrete obstruction space has rank at least
`q-1`, including all padding coordinates. -/
theorem coordinateObstruction_rank_lower (hq : 0 < q)
    (eX : PaddedInput A q ≃ₗ[F] (ι → F))
    (eZ : PaddedOutput A q ≃ₗ[F] (κ → F))
    (c : MatrixSpace F ι κ)
    (hc : c ∈ coordinateObstruction A q hq eX eZ) (hne : c ≠ 0) :
    q - 1 ≤ Module.finrank F (matrixToLinear c).range := by
  obtain ⟨d, hd, rfl⟩ := hc
  rw [LinearEquiv.coe_coe, operatorCoordinates_rank]
  apply obstructionSpace_rank_lower A q (componentAnchors A q hq) d hd
  intro hz
  exact hne (by simp [hz])

/-- The actual constructed obstruction space contains no nonzero rank-one
matrix. Its crucial rank property is proved, not taken as a premise. -/
theorem coordinateObstruction_noRankOne (hq : 3 ≤ q)
    (eX : PaddedInput A q ≃ₗ[F] (ι → F))
    (eZ : PaddedOutput A q ≃ₗ[F] (κ → F)) :
    NoRankOne (coordinateObstruction A q (by omega) eX eZ) := by
  apply RankOneExclusion.noRankOne_of_rank_lower
  intro c hc hne
  have h := coordinateObstruction_rank_lower A q (by omega) eX eZ c hc hne
  omega

/-- Express an input twist in the chosen bases. -/
def twistCoordinates
    (eX : PaddedInput A q ≃ₗ[F] (ι → F))
    (eZ : PaddedOutput A q ≃ₗ[F] (κ → F))
    (ε : AlternatingBilinearMap F (PaddedInput A q) (PaddedOutput A q)) :
    AlternatingBilinearMap F (ι → F) (κ → F) where
  toLinearMap := LinearMap.mk₂ F (fun x y => eZ (ε (eX.symm x) (eX.symm y)))
    (by intros; simp)
    (by intros; simp)
    (by intros; simp)
    (by intros; simp)
  map_self_eq_zero x := by simp

/-- The group constructed from the affine system and an actual input twist. -/
abbrev ConstructedGroup (hq : 0 < q)
    (eX : PaddedInput A q ≃ₗ[F] (ι → F))
    (eZ : PaddedOutput A q ≃ₗ[F] (κ → F))
    (ε : AlternatingBilinearMap F (PaddedInput A q) (PaddedOutput A q)) :=
  TensorGroup (evaluationTwist
    (MatrixEvaluationGroup.operatorSpace (coordinateObstruction A q hq eX eZ))
    (twistCoordinates A q eX eZ ε))

/-- For the actual affine-system construction, the center is the derived subgroup. -/
theorem constructed_center_eq_derived [NeZero (2 : F)] [Nonempty ι] [Nonempty κ]
    (hq : 3 ≤ q)
    (eX : PaddedInput A q ≃ₗ[F] (ι → F))
    (eZ : PaddedOutput A q ≃ₗ[F] (κ → F))
    (ε : AlternatingBilinearMap F (PaddedInput A q) (PaddedOutput A q)) :
    Subgroup.center (ConstructedGroup A q (by omega) eX eZ ε) =
      commutator (ConstructedGroup A q (by omega) eX eZ ε) :=
  MatrixEvaluationGroup.center_eq_derived _
    (coordinateObstruction_noRankOne A q hq eX eZ) _

/-- Every constructed element has `p`th power one in characteristic `p`. -/
theorem constructed_pow_char (p : ℕ) [CharP F p] (hq : 0 < q)
    (eX : PaddedInput A q ≃ₗ[F] (ι → F))
    (eZ : PaddedOutput A q ≃ₗ[F] (κ → F))
    (ε : AlternatingBilinearMap F (PaddedInput A q) (PaddedOutput A q))
    (g : ConstructedGroup A q hq eX eZ ε) : g ^ p = 1 :=
  TensorGroup.pow_char_eq_one p g

/-- Every commutator is central in the actual constructed group. -/
theorem constructed_class_at_most_two (hq : 0 < q)
    (eX : PaddedInput A q ≃ₗ[F] (ι → F))
    (eZ : PaddedOutput A q ≃ₗ[F] (κ → F))
    (ε : AlternatingBilinearMap F (PaddedInput A q) (PaddedOutput A q))
    (g h k : ConstructedGroup A q hq eX eZ ε) :
    (g * h * g⁻¹ * h⁻¹) * k = k * (g * h * g⁻¹ * h⁻¹) :=
  TensorGroup.commutator_central g h k

/-- The concrete group is finite whenever its coordinate field is finite. -/
instance constructed_finite [Finite F] (hq : 0 < q)
    (eX : PaddedInput A q ≃ₗ[F] (ι → F))
    (eZ : PaddedOutput A q ≃ₗ[F] (κ → F))
    (ε : AlternatingBilinearMap F (PaddedInput A q) (PaddedOutput A q)) :
    Finite (ConstructedGroup A q hq eX eZ ε) := by
  infer_instance

/-- The exponent is exactly the characteristic prime, rather than merely a divisor. -/
theorem constructed_exponent [Nonempty κ] (p : ℕ) (hp : p.Prime) [CharP F p]
    (hq : 0 < q)
    (eX : PaddedInput A q ≃ₗ[F] (ι → F))
    (eZ : PaddedOutput A q ≃ₗ[F] (κ → F))
    (ε : AlternatingBilinearMap F (PaddedInput A q) (PaddedOutput A q)) :
    Monoid.exponent (ConstructedGroup A q hq eX eZ ε) = p := by
  letI : Nontrivial (ConstructedGroup A q hq eX eZ ε) := TensorGroup.equivProd.nontrivial
  letI : Fact p.Prime := ⟨hp⟩
  apply (Monoid.exponent_eq_prime_iff hp).mpr
  intro g hg
  exact orderOf_eq_prime (TensorGroup.pow_char_eq_one p g) hg

/-- The constructed group is nonabelian. Together with centrality of every
commutator, this gives class exactly two. -/
theorem constructed_noncommutative [NeZero (2 : F)] [Nonempty ι] [Nonempty κ]
    (hq : 3 ≤ q)
    (eX : PaddedInput A q ≃ₗ[F] (ι → F))
    (eZ : PaddedOutput A q ≃ₗ[F] (κ → F))
    (ε : AlternatingBilinearMap F (PaddedInput A q) (PaddedOutput A q)) :
    ∃ g h : ConstructedGroup A q (Nat.lt_of_lt_of_le (by decide : 0 < 3) hq) eX eZ ε, g * h ≠ h * g := by
  obtain ⟨x, hx⟩ := exists_ne (0 : ι → F)
  obtain ⟨z, hz⟩ := exists_ne (0 : κ → F)
  let C := coordinateObstruction A q (by omega) eX eZ
  have hC : NoRankOne C := coordinateObstruction_noRankOne A q hq eX eZ
  obtain ⟨g, h, hgh⟩ := output_is_commutator
    (MatrixEvaluationGroup.operatorSpace C) (twistCoordinates A q eX eZ ε) x
    (MatrixEvaluationGroup.evaluation_surjective C hC x hx) z
  refine ⟨g, h, ?_⟩
  intro hc
  have he := commutatorElement_eq_one_iff_mul_comm.mpr hc
  rw [hgh] at he
  exact hz (congrArg TensorGroup.snd he)

end IncidenceGroup
end GroupWL
