import GroupWL.ConstructiveCoordinates
import GroupWL.MatrixEvaluationGroup

/-! Computed coordinates for an orthogonal complement specified by generators. -/
namespace GroupWL.GeneratedCoordinates

open ConstructiveCoordinates ObstructionDuality
open scoped BigOperators
variable {F ι κ : Type} [Field F] [DecidableEq F]
  [Fintype ι] [Fintype κ] [DecidableEq ι] [FiniteCode ι] [FiniteCode κ]

/-- The matrix/operator equivalence with an explicit decidable index equality. -/
def matrixEquiv : MatrixSpace F ι κ ≃ₗ[F] ((ι → F) →ₗ[F] (κ → F)) where
  toFun := matrixToLinear
  invFun f i z := f (Pi.single i 1) z
  left_inv y := by funext i z; simp [matrixToLinear,evaluation,Pi.single_apply]
  right_inv f := by
    apply LinearMap.ext
    intro x
    have hx : x = ∑ i, x i • Pi.single i (1 : F) := by
      funext i
      simp [Pi.single_apply]
    funext z
    change (∑ i, x i*f (Pi.single i 1) z) = f x z
    conv_rhs => rw [hx]
    simp
  map_add' y y' := by ext x z; simp [matrixToLinear,evaluation,mul_add,Finset.sum_add_distrib]
  map_smul' c y := by ext x z; simp [matrixToLinear,evaluation,Finset.mul_sum,mul_left_comm]

theorem matrixEquiv_eq : (matrixEquiv : MatrixSpace F ι κ ≃ₗ[F] _) = matrixLinearEquiv := by
  ext y x z
  rfl

variable {W : Type} [AddCommGroup W] [Module F W]
  (D : Coordinates F W) (σ : W →ₗ[F] MatrixSpace F ι κ)

def generator (i : Fin D.dimension) : MatrixSpace F ι κ :=
  σ (D.equiv.symm (Pi.single i 1))

def tests : MatrixSpace F ι κ →ₗ[F] (Fin D.dimension → F) :=
  LinearMap.pi (fun i => matrixDual (generator D σ i))

theorem tests_kernel : LinearMap.ker (tests D σ) = annihilator σ.range := by
  ext y
  rw [LinearMap.mem_ker,mem_annihilator]
  constructor
  · intro hy c hc
    obtain ⟨w,rfl⟩ := hc
    let f := ((matrixDual y).comp σ).comp D.equiv.symm.toLinearMap
    have hf : ∀ i, f (Pi.single i 1) = 0 := by
      intro i
      have hi := congrFun hy i
      change matrixPair (generator D σ i) y = 0 at hi
      change matrixPair y (generator D σ i) = 0
      rwa [matrixPair_comm]
    have hz : f (D.equiv w) = 0 := by
      rw [LinearMap.pi_apply_eq_sum_univ]
      apply Finset.sum_eq_zero
      intro i _
      have he : (fun j : Fin D.dimension => if i=j then (1:F) else 0) = Pi.single i 1 := by
        funext j
        simp [Pi.single_apply,eq_comm]
      rw [he,hf,smul_zero]
    simpa only [f,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]
      using hz
  · intro hy
    funext i
    change matrixPair (generator D σ i) y = 0
    rw [matrixPair_comm]
    exact hy _ ⟨_,rfl⟩

def matrixCoordinates : Coordinates F (MatrixSpace F ι κ) :=
  Coordinates.dependentPi (fun _ : ι => Coordinates.pi κ)

def annihilatorCoordinates : Coordinates F (annihilator σ.range) :=
  let K := Coordinates.kernel (matrixCoordinates (F := F) (ι := ι) (κ := κ))
    (Coordinates.pi (Fin D.dimension)) (tests D σ)
  ⟨K.dimension,(LinearEquiv.ofEq _ _ (tests_kernel D σ).symm).trans K.equiv⟩

def operatorMatrixEquiv (C : Submodule F (MatrixSpace F ι κ)) :
    MatrixEvaluationGroup.operatorSpace C ≃ₗ[F] annihilator C where
  toFun y := ⟨matrixEquiv.symm y.val, by
    obtain ⟨m,hm,he⟩ := y.property
    rw [← he]
    change matrixEquiv.symm (matrixToLinear m) ∈ annihilator C
    change matrixEquiv.symm (matrixEquiv m) ∈ annihilator C
    rwa [LinearEquiv.symm_apply_apply]⟩
  invFun m := ⟨matrixEquiv m.val,⟨m.val,m.property,rfl⟩⟩
  left_inv y := Subtype.ext (matrixEquiv.apply_symm_apply _)
  right_inv m := Subtype.ext (matrixEquiv.symm_apply_apply _)
  map_add' y z := Subtype.ext (matrixEquiv.symm.map_add y.val z.val)
  map_smul' c y := Subtype.ext (matrixEquiv.symm.map_smul c y.val)

def operatorCoordinates : Coordinates F (MatrixEvaluationGroup.operatorSpace σ.range) :=
  ⟨(annihilatorCoordinates D σ).dimension,
    (operatorMatrixEquiv σ.range).trans (annihilatorCoordinates D σ).equiv⟩

end GroupWL.GeneratedCoordinates
