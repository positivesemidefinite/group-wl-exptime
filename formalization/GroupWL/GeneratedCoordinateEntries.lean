import GroupWL.GeneratedCoordinates
import GroupWL.EvaluationTensorCoefficients

/-! Explicit indexing of the materialized annihilator kernel basis. -/
namespace GroupWL.GeneratedCoordinateEntries
open ConstructiveCoordinates GeneratedCoordinates ObstructionDuality
open scoped BigOperators
variable {F ι κ : Type} [Field F] [DecidableEq F]
  [Fintype ι] [Fintype κ] [DecidableEq ι] [FiniteCode ι] [FiniteCode κ]

def matrixPosition (i : Fin (FiniteCode.size ι)) (z : Fin (FiniteCode.size κ)) :
    Fin (matrixCoordinates (F:=F) (ι:=ι) (κ:=κ)).dimension :=
  FiniteCode.equiv ⟨(FiniteCode.equiv (α:=ι)).symm i,z⟩

theorem matrixCoordinates_dimension :
    (matrixCoordinates (F:=F) (ι:=ι) (κ:=κ)).dimension=FiniteCode.size ι*FiniteCode.size κ := by
  change (∑ _ : Fin (FiniteCode.size ι),FiniteCode.size κ)=_
  simp

theorem matrixPosition_val (i : Fin (FiniteCode.size ι)) (z : Fin (FiniteCode.size κ)) :
    (matrixPosition (F:=F) i z).val=i.val*FiniteCode.size κ+z.val := by
  let e := Equiv.sigmaCongrLeft (β:=fun _ : ι => Fin (FiniteCode.size κ))
    (FiniteCode.equiv (α:=ι)).symm
  change (finSigmaFinEquiv (e.symm (e ⟨i,z⟩))).val=_
  rw [e.symm_apply_apply]
  simp [finSigmaFinEquiv_apply]

theorem matrixCoordinates_apply (y : MatrixSpace F ι κ)
    (i : Fin (FiniteCode.size ι)) (z : Fin (FiniteCode.size κ)) :
    (matrixCoordinates (F:=F) (ι:=ι) (κ:=κ)).equiv y (matrixPosition (F:=F) i z)=
      y ((FiniteCode.equiv (α:=ι)).symm i) ((FiniteCode.equiv (α:=κ)).symm z) := by
  let e := FiniteCode.equiv (α:=Σ _ : ι,Fin (FiniteCode.size κ))
  change (fun a : Σ _ : ι,Fin (FiniteCode.size κ) => y a.1 ((FiniteCode.equiv (α:=κ)).symm a.2))
    (e.symm (e ⟨(FiniteCode.equiv (α:=ι)).symm i,z⟩))=_
  rw [e.symm_apply_apply]

theorem kernel_inverse_coordinates {X Z : Type} [AddCommGroup X] [Module F X]
    [AddCommGroup Z] [Module F Z] (D : Coordinates F X) (E : Coordinates F Z) (f : X →ₗ[F] Z)
    (x : Fin (Coordinates.kernel D E f).dimension → F) :
    D.equiv (((Coordinates.kernel D E f).equiv.symm x).val)=
      (PivotElimination.kernelChart E.dimension D.dimension
        (E.equiv.toLinearMap.comp (f.comp D.equiv.symm.toLinearMap))).lift x := by
  change D.equiv (D.equiv.symm (_))=_
  exact D.equiv.apply_symm_apply _

theorem pi_inverse_unit (i : Fin (FiniteCode.size ι)) :
    (Coordinates.pi (F:=F) ι).equiv.symm (EvaluationTensorCoefficients.unit i)=
      Pi.single ((FiniteCode.equiv (α:=ι)).symm i) 1 := by
  funext x
  change EvaluationTensorCoefficients.unit i (FiniteCode.equiv x)=_
  simp [EvaluationTensorCoefficients.unit,Pi.single_apply,Equiv.apply_eq_iff_eq_symm_apply]

variable {W : Type} [AddCommGroup W] [Module F W]
variable (D : Coordinates F W) (σ : W →ₗ[F] MatrixSpace F ι κ)

def constraintMap : (Fin (matrixCoordinates (F:=F) (ι:=ι) (κ:=κ)).dimension → F) →ₗ[F]
    (Fin D.dimension → F) :=
  (Coordinates.pi (F:=F) (Fin D.dimension)).equiv.toLinearMap.comp
    ((tests D σ).comp (matrixCoordinates (F:=F) (ι:=ι) (κ:=κ)).equiv.symm.toLinearMap)

def operatorChart : CoordinateElimination.Chart
    (matrixCoordinates (F:=F) (ι:=ι) (κ:=κ)).dimension (LinearMap.ker (constraintMap D σ)) :=
  PivotElimination.kernelChart D.dimension _ (constraintMap D σ)

theorem operatorCoefficient_lift (j : Fin (operatorCoordinates D σ).dimension)
    (i : Fin (FiniteCode.size ι)) (z : Fin (FiniteCode.size κ)) :
    EvaluationTensorCoefficients.operatorCoefficient (Coordinates.pi ι) (Coordinates.pi κ)
      (MatrixEvaluationGroup.operatorSpace σ.range) (operatorCoordinates D σ) j i z =
      (operatorChart D σ).lift (EvaluationTensorCoefficients.unit j) (matrixPosition (F:=F) i z) := by
  let K := Coordinates.kernel (matrixCoordinates (F:=F) (ι:=ι) (κ:=κ))
    (Coordinates.pi (F:=F) (Fin D.dimension)) (tests D σ)
  let a := ((K.equiv.symm (EvaluationTensorCoefficients.unit j)).val : MatrixSpace F ι κ)
  have hc := kernel_inverse_coordinates (matrixCoordinates (F:=F) (ι:=ι) (κ:=κ))
    (Coordinates.pi (F:=F) (Fin D.dimension)) (tests D σ) (EvaluationTensorCoefficients.unit j)
  have hv := congrFun hc (matrixPosition (F:=F) i z)
  change (matrixCoordinates (F:=F) (ι:=ι) (κ:=κ)).equiv a (matrixPosition (F:=F) i z)=
    (operatorChart D σ).lift (EvaluationTensorCoefficients.unit j) (matrixPosition (F:=F) i z) at hv
  rw [matrixCoordinates_apply] at hv
  rw [←hv]
  change (matrixToLinear a) ((Coordinates.pi (F:=F) ι).equiv.symm (EvaluationTensorCoefficients.unit (F:=F) i))
    ((FiniteCode.equiv (α:=κ)).symm z)=_
  rw [pi_inverse_unit]
  simp [matrixToLinear,evaluation,Pi.single_apply]

end GroupWL.GeneratedCoordinateEntries
