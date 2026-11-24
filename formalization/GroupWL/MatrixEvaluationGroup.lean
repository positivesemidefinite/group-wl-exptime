import GroupWL.ObstructionDuality
import GroupWL.EvaluationDerived

/-! # From the matrix obstruction space to the actual group

This connects the coordinate orthogonal complement used in the tensor
construction to the operator space in the evaluation group. The absence of
nonzero rank-one obstruction matrices proves the center and derived-subgroup
statements for the concrete group, without assuming these group properties.
-/

namespace GroupWL
namespace MatrixEvaluationGroup

open ObstructionDuality

variable {F ι κ : Type*} [Field F] [Fintype ι] [Fintype κ]

/-- The manuscript's `Y = C^⊥`, viewed as an actual space of linear maps. -/
def operatorSpace (C : Submodule F (MatrixSpace F ι κ)) :
    Submodule F ((ι → F) →ₗ[F] (κ → F)) :=
  (annihilator C).map
    ({ toFun := matrixToLinear
       map_add' := matrixLinearEquiv.map_add
       map_smul' := matrixLinearEquiv.map_smul } :
      MatrixSpace F ι κ →ₗ[F] ((ι → F) →ₗ[F] (κ → F)))

/-- The matrix-coordinate evaluation theorem gives an operator in the
concrete group for every prescribed output at any nonzero input. -/
theorem evaluation_surjective (C : Submodule F (MatrixSpace F ι κ))
    (hC : NoRankOne C) (x : ι → F) (hx : x ≠ 0) (z : κ → F) :
    ∃ y : operatorSpace C, (y : (ι → F) →ₗ[F] (κ → F)) x = z := by
  obtain ⟨m, hm, hmz⟩ := exists_evaluation_of_noRankOne C hC x hx z
  refine ⟨⟨matrixLinearEquiv m, ?_⟩, hmz⟩
  exact ⟨m, hm, rfl⟩

/-- Nontrivial outputs and onto evaluation imply separation of input vectors. -/
theorem operators_separate [Nonempty κ] (C : Submodule F (MatrixSpace F ι κ))
    (hC : NoRankOne C) (x : ι → F)
    (hx : ∀ y : operatorSpace C, (y : (ι → F) →ₗ[F] (κ → F)) x = 0) : x = 0 := by
  by_contra hne
  obtain ⟨z, hz⟩ := exists_ne (0 : κ → F)
  obtain ⟨y, hy⟩ := evaluation_surjective C hC x hne z
  exact hz (hy.symm.trans (hx y))

/-- The output coordinates are exactly the center, for every input twist. -/
theorem center_eq_output [NeZero (2 : F)] [Nonempty κ]
    (C : Submodule F (MatrixSpace F ι κ)) (hC : NoRankOne C)
    (ε : AlternatingBilinearMap F (ι → F) (κ → F)) :
    Subgroup.center (TensorGroup (evaluationTwist (operatorSpace C) ε)) =
      TensorGroup.outputSubgroup (evaluationTwist (operatorSpace C) ε) :=
  TensorGroup.center_eq_output _
    (evaluationTwist_radical_eq_zero (operatorSpace C) ε (operators_separate C hC))

/-- The output coordinates are exactly the derived subgroup. -/
theorem derived_eq_output [NeZero (2 : F)] [Nonempty ι]
    (C : Submodule F (MatrixSpace F ι κ)) (hC : NoRankOne C)
    (ε : AlternatingBilinearMap F (ι → F) (κ → F)) :
    commutator (TensorGroup (evaluationTwist (operatorSpace C) ε)) =
      TensorGroup.outputSubgroup (evaluationTwist (operatorSpace C) ε) := by
  obtain ⟨x, hx⟩ := exists_ne (0 : ι → F)
  exact evaluationGroup_derived_eq_output (operatorSpace C) ε x
    (evaluation_surjective C hC x hx)

/-- The no-rank-one property proves the manuscript's `Z(G) = G'` statement
for the constructed group itself. -/
theorem center_eq_derived [NeZero (2 : F)] [Nonempty ι] [Nonempty κ]
    (C : Submodule F (MatrixSpace F ι κ)) (hC : NoRankOne C)
    (ε : AlternatingBilinearMap F (ι → F) (κ → F)) :
    Subgroup.center (TensorGroup (evaluationTwist (operatorSpace C) ε)) =
      commutator (TensorGroup (evaluationTwist (operatorSpace C) ε)) := by
  rw [center_eq_output C hC ε, derived_eq_output C hC ε]

/-- For finite coordinate fields, the concrete group is finite. -/
instance finiteGroup [Finite F] (C : Submodule F (MatrixSpace F ι κ))
    (ε : AlternatingBilinearMap F (ι → F) (κ → F)) :
    Finite (TensorGroup (evaluationTwist (operatorSpace C) ε)) := by
  letI : Finite ((ι → F) →ₗ[F] (κ → F)) :=
    Finite.of_injective (fun f : (ι → F) →ₗ[F] (κ → F) => (f : (ι → F) → (κ → F)))
      DFunLike.coe_injective
  infer_instance

end MatrixEvaluationGroup
end GroupWL
