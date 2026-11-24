import GroupWL.AlternatingCoordinates
import GroupWL.MatrixEvaluationGroup

/-! # Coordinate boundaries are actual group shears

The family of matrix columns used by tensor duality is equivalent to a
linear map into the exact operator space used by the constructed group.
-/

namespace GroupWL.CoordinateShears

open ObstructionDuality AlternatingCoordinates MatrixEvaluationGroup
variable {F ι κ : Type*} [Field F] [Fintype ι] [Fintype κ] [DecidableEq ι]

/-- The matrix orthogonal complement and the actual operator space agree. -/
noncomputable def operatorEquiv (C : Submodule F (MatrixSpace F ι κ)) :
    annihilator C ≃ₗ[F] operatorSpace C :=
  matrixLinearEquiv.submoduleMap (annihilator C)

/-- Every family of orthogonal matrices extends uniquely to a linear shear. -/
noncomputable def shearParameters (C : Submodule F (MatrixSpace F ι κ)) :
    (ι → annihilator C) ≃ₗ[F] ((ι → F) →ₗ[F] operatorSpace C) :=
  (LinearEquiv.piCongrRight (fun _ => operatorEquiv C)).trans
    (LinearEquiv.piRing F (operatorSpace C) ι F).symm

@[simp] theorem shearParameters_basis (C : Submodule F (MatrixSpace F ι κ))
    (a : ι → annihilator C) (i : ι) :
    shearParameters C a (Pi.single i 1) = operatorEquiv C (a i) := by
  simp [shearParameters]

@[simp] theorem operatorEquiv_basis (C : Submodule F (MatrixSpace F ι κ))
    (a : annihilator C) (i : ι) :
    (operatorEquiv C a : (ι → F) →ₗ[F] (κ → F)) (Pi.single i 1) = a.val i := by
  change matrixToLinear a.val (Pi.single i 1) = a.val i
  ext z
  simp [matrixToLinear, evaluation, Pi.single_apply]

/-- Antisymmetrizing the matrix family gives precisely the group's shear
coboundary, with no additional realization assumption. -/
theorem shear_boundary_coordinates (C : Submodule F (MatrixSpace F ι κ))
    (a : ι → annihilator C) :
    bilinearCoordinates (shearCoboundary (operatorSpace C) (shearParameters C a)).toLinearMap =
      boundaryMap C a := by
  funext i j z
  rw [bilinearCoordinates_apply]
  change ((shearParameters C a (Pi.single i 1) : (ι → F) →ₗ[F] (κ → F))
      (Pi.single j 1) -
    (shearParameters C a (Pi.single j 1) : (ι → F) →ₗ[F] (κ → F))
      (Pi.single i 1)) z = _
  rw [shearParameters_basis, shearParameters_basis, operatorEquiv_basis, operatorEquiv_basis]
  rfl

/-- The coordinate range condition is equivalent to an actual linear shear
into the exact operator space in the tensor group. -/
theorem mem_boundary_range_iff_shear (C : Submodule F (MatrixSpace F ι κ))
    (b : (ι → F) →ₗ[F] (ι → F) →ₗ[F] (κ → F)) :
    bilinearCoordinates b ∈ LinearMap.range (boundaryMap C) ↔
      ∃ α : (ι → F) →ₗ[F] operatorSpace C,
        (shearCoboundary (operatorSpace C) α).toLinearMap = b := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨shearParameters C a, bilinearCoordinates.injective ?_⟩
    rw [shear_boundary_coordinates, ha]
  · rintro ⟨α, hα⟩
    refine ⟨(shearParameters C).symm α, ?_⟩
    rw [← shear_boundary_coordinates, LinearEquiv.apply_symm_apply, hα]

end GroupWL.CoordinateShears
