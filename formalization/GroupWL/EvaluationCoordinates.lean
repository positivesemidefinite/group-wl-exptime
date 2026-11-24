import GroupWL.MatrixEvaluationGroup
import GroupWL.DenseTensorEncoding

/-! Changing bases in an orthogonal-complement evaluation construction uses
inverse adjoints on the group coordinates. Ordinary tensor transport alone
would not account for the coordinate pairing defining the operator space. -/
namespace GroupWL.EvaluationCoordinates

open ObstructionDuality
open scoped BigOperators

variable {F ι κ ι' κ' : Type*} [Field F]
  [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']

noncomputable def coordinateDual : (ι → F) ≃ₗ[F] Module.Dual F (ι → F) :=
  by classical exact (Pi.basisFun F ι).toDualEquiv

open Classical in
@[simp] theorem coordinateDual_single (x : ι → F) (i : ι) :
    coordinateDual x (Pi.single i 1) = x i := by
  classical
  change (Pi.basisFun F ι).toDual x ((Pi.basisFun F ι) i) = x i
  rw [(Pi.basisFun F ι).toDual_apply_left]
  simp

@[simp] theorem functionalCoefficients_coordinateDual (x : ι → F) :
    functionalCoefficients (coordinateDual x) = x := by
  classical
  funext i
  exact coordinateDual_single x i

theorem coordinateDual_apply (x y : ι → F) : coordinateDual x y = ∑ i, x i * y i := by
  rw [functional_eq_sum, functionalCoefficients_coordinateDual]

theorem coordinateDual_comm (x y : ι → F) : coordinateDual x y = coordinateDual y x := by
  simp only [coordinateDual_apply, mul_comm]

noncomputable def inverseAdjoint (e : (ι → F) ≃ₗ[F] (ι' → F)) :
    (ι → F) ≃ₗ[F] (ι' → F) :=
  (coordinateDual.trans e.symm.dualMap).trans coordinateDual.symm

@[simp] theorem inverseAdjoint_pair (e : (ι → F) ≃ₗ[F] (ι' → F)) (x y : ι → F) :
    coordinateDual (inverseAdjoint e x) (e y) = coordinateDual x y := by
  simp [inverseAdjoint, LinearEquiv.dualMap_apply]

open Classical in
theorem inverseAdjoint_coordinate (e : (ι → F) ≃ₗ[F] (ι' → F)) (i : ι) (j : ι')
    (he : e (Pi.single i 1) = Pi.single j 1) (x : ι → F) :
    inverseAdjoint e x j = x i := by
  have h := inverseAdjoint_pair e x (Pi.single i 1)
  simpa only [he, coordinateDual_single] using h

open Classical in
theorem inverseAdjoint_single (e : (ι → F) ≃ₗ[F] (ι' → F)) (i : ι) (j : ι')
    (he : ∀ x, e x j = x i) : inverseAdjoint e (Pi.single i 1) = Pi.single j 1 := by
  apply coordinateDual.injective
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [inverseAdjoint_pair, coordinateDual_comm, coordinateDual_single,
    coordinateDual_comm, coordinateDual_single, he]

noncomputable def matrixChange (eX : (ι → F) ≃ₗ[F] (ι' → F))
    (eZ : (κ → F) ≃ₗ[F] (κ' → F)) :
    MatrixSpace F ι κ ≃ₗ[F] MatrixSpace F ι' κ' :=
  (matrixLinearEquiv.trans (eX.arrowCongr eZ)).trans matrixLinearEquiv.symm

noncomputable def matrixInverseAdjoint
    (D : MatrixSpace F ι κ ≃ₗ[F] MatrixSpace F ι' κ') :
    MatrixSpace F ι κ ≃ₗ[F] MatrixSpace F ι' κ' :=
  (matrixDualEquiv.trans D.symm.dualMap).trans matrixDualEquiv.symm

@[simp] theorem matrixInverseAdjoint_pair
    (D : MatrixSpace F ι κ ≃ₗ[F] MatrixSpace F ι' κ') (x y : MatrixSpace F ι κ) :
    matrixPair (matrixInverseAdjoint D x) (D y) = matrixPair x y := by
  change matrixDualEquiv (matrixInverseAdjoint D x) (D y) = matrixDualEquiv x y
  simp [matrixInverseAdjoint, LinearEquiv.dualMap_apply]

theorem matrixToLinear_rankOne (x : ι → F) (w : κ → F) (y : ι → F) :
    matrixToLinear (rankOne x w) y = (coordinateDual x y) • w := by
  funext z
  simp only [matrixToLinear_apply, evaluation, LinearMap.coe_mk, AddHom.coe_mk,
    rankOne, Pi.smul_apply, smul_eq_mul, coordinateDual_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem matrixChange_rankOne (eX : (ι → F) ≃ₗ[F] (ι' → F))
    (eZ : (κ → F) ≃ₗ[F] (κ' → F)) (x : ι → F) (w : κ → F) :
    matrixChange eX eZ (rankOne x w) = rankOne (inverseAdjoint eX x) (eZ w) := by
  apply (matrixLinearEquiv (K := F) (ι := ι') (κ := κ')).injective
  change matrixLinearEquiv (matrixLinearEquiv.symm ((eX.arrowCongr eZ)
    (matrixLinearEquiv (rankOne x w)))) = _
  rw [LinearEquiv.apply_symm_apply]
  apply LinearMap.ext
  intro v
  change eZ (matrixToLinear (rankOne x w) (eX.symm v)) =
    matrixToLinear (rankOne (inverseAdjoint eX x) (eZ w)) v
  rw [matrixToLinear_rankOne, map_smul, matrixToLinear_rankOne]
  have hp := inverseAdjoint_pair eX x (eX.symm v)
  simpa using congrArg (fun a : F => a • eZ w) hp.symm

theorem evaluation_pair (y : MatrixSpace F ι κ) (x : ι → F) (w : κ → F) :
    coordinateDual w (matrixToLinear y x) = matrixPair y (rankOne x w) := by
  rw [matrixToLinear_apply, evaluation_adjoint, functionalCoefficients_coordinateDual,
    matrixPair_comm]

theorem matrixInverseAdjoint_evaluation (eX : (ι → F) ≃ₗ[F] (ι' → F))
    (eZ : (κ → F) ≃ₗ[F] (κ' → F)) (y : MatrixSpace F ι κ) (x : ι → F) :
    matrixToLinear (matrixInverseAdjoint (matrixChange eX eZ) y) (inverseAdjoint eX x) =
      inverseAdjoint eZ (matrixToLinear y x) := by
  apply coordinateDual.injective
  apply LinearMap.ext
  intro z
  obtain ⟨w, rfl⟩ := eZ.surjective z
  rw [coordinateDual_comm, evaluation_pair, ← matrixChange_rankOne,
    matrixInverseAdjoint_pair, ← evaluation_pair, coordinateDual_comm,
    inverseAdjoint_pair]

theorem matrixInverseAdjoint_mem_annihilator
    (C : Submodule F (MatrixSpace F ι κ))
    (D : MatrixSpace F ι κ ≃ₗ[F] MatrixSpace F ι' κ') (y : MatrixSpace F ι κ) :
    matrixInverseAdjoint D y ∈ annihilator (C.map D.toLinearMap) ↔ y ∈ annihilator C := by
  rw [mem_annihilator, mem_annihilator]
  constructor
  · intro h c hc
    have hm : D c ∈ C.map D.toLinearMap := ⟨c, hc, rfl⟩
    simpa using h (D c) hm
  · intro h c hc
    obtain ⟨a, ha, rfl⟩ := hc
    simpa using h a ha

noncomputable def annihilatorEquiv (C : Submodule F (MatrixSpace F ι κ))
    (D : MatrixSpace F ι κ ≃ₗ[F] MatrixSpace F ι' κ') :
    annihilator C ≃ₗ[F] annihilator (C.map D.toLinearMap) where
  toFun y := ⟨matrixInverseAdjoint D y, (matrixInverseAdjoint_mem_annihilator C D y).mpr y.property⟩
  invFun y := ⟨(matrixInverseAdjoint D).symm y,
    (matrixInverseAdjoint_mem_annihilator C D ((matrixInverseAdjoint D).symm y)).mp
      (by simpa using y.property)⟩
  left_inv y := by apply Subtype.ext; exact (matrixInverseAdjoint D).symm_apply_apply y
  right_inv y := by apply Subtype.ext; exact (matrixInverseAdjoint D).apply_symm_apply y
  map_add' y z := by apply Subtype.ext; exact map_add _ _ _
  map_smul' a y := by apply Subtype.ext; exact map_smul _ _ _

noncomputable def operatorEquiv (C : Submodule F (MatrixSpace F ι κ))
    (eX : (ι → F) ≃ₗ[F] (ι' → F)) (eZ : (κ → F) ≃ₗ[F] (κ' → F)) :
    MatrixEvaluationGroup.operatorSpace C ≃ₗ[F]
      MatrixEvaluationGroup.operatorSpace (C.map (matrixChange eX eZ).toLinearMap) :=
  ((matrixLinearEquiv.submoduleMap (annihilator C)).symm.trans
    (annihilatorEquiv C (matrixChange eX eZ))).trans
      (matrixLinearEquiv.submoduleMap (annihilator (C.map (matrixChange eX eZ).toLinearMap)))

@[simp] theorem operatorEquiv_evaluation (C : Submodule F (MatrixSpace F ι κ))
    (eX : (ι → F) ≃ₗ[F] (ι' → F)) (eZ : (κ → F) ≃ₗ[F] (κ' → F))
    (y : MatrixEvaluationGroup.operatorSpace C) (x : ι → F) :
    (operatorEquiv C eX eZ y : (ι' → F) →ₗ[F] (κ' → F)) (inverseAdjoint eX x) =
      inverseAdjoint eZ ((y : (ι → F) →ₗ[F] (κ → F)) x) := by
  change matrixToLinear (matrixInverseAdjoint (matrixChange eX eZ)
    (matrixLinearEquiv.symm y.val)) (inverseAdjoint eX x) = _
  rw [matrixInverseAdjoint_evaluation]
  congr 1
  change matrixLinearEquiv (matrixLinearEquiv.symm y.val) x = y.val x
  rw [LinearEquiv.apply_symm_apply]

/-- An actual group isomorphism, with the twist transformed by the same
inverse adjoints as the evaluation coordinates. -/
noncomputable def groupEquiv (C : Submodule F (MatrixSpace F ι κ))
    (eX : (ι → F) ≃ₗ[F] (ι' → F)) (eZ : (κ → F) ≃ₗ[F] (κ' → F))
    (ε : AlternatingBilinearMap F (ι → F) (κ → F))
    (ε' : AlternatingBilinearMap F (ι' → F) (κ' → F))
    (hε : ∀ x y, ε' (inverseAdjoint eX x) (inverseAdjoint eX y) = inverseAdjoint eZ (ε x y)) :
    TensorGroup (evaluationTwist (MatrixEvaluationGroup.operatorSpace C) ε) ≃*
      TensorGroup (evaluationTwist
        (MatrixEvaluationGroup.operatorSpace (C.map (matrixChange eX eZ).toLinearMap)) ε') where
  toFun g := ⟨(inverseAdjoint eX g.fst.1, operatorEquiv C eX eZ g.fst.2), inverseAdjoint eZ g.snd⟩
  invFun g := ⟨((inverseAdjoint eX).symm g.fst.1,
    (operatorEquiv C eX eZ).symm g.fst.2), (inverseAdjoint eZ).symm g.snd⟩
  left_inv g := by apply TensorGroup.ext <;> simp
  right_inv g := by apply TensorGroup.ext <;> simp
  map_mul' g h := by
    apply TensorGroup.ext
    · change (inverseAdjoint eX (g.fst.1 + h.fst.1), operatorEquiv C eX eZ (g.fst.2 + h.fst.2)) =
        (inverseAdjoint eX g.fst.1 + inverseAdjoint eX h.fst.1,
          operatorEquiv C eX eZ g.fst.2 + operatorEquiv C eX eZ h.fst.2)
      simp
    · change inverseAdjoint eZ (g.snd + h.snd + (2 : F)⁻¹ •
          evaluationTwist (MatrixEvaluationGroup.operatorSpace C) ε g.fst h.fst) =
        inverseAdjoint eZ g.snd + inverseAdjoint eZ h.snd + (2 : F)⁻¹ •
          evaluationTwist _ ε' (inverseAdjoint eX g.fst.1, operatorEquiv C eX eZ g.fst.2)
            (inverseAdjoint eX h.fst.1, operatorEquiv C eX eZ h.fst.2)
      simp [evaluationTwist_apply, operatorEquiv_evaluation, hε]

/-- The zero-twist evaluation group is basis independent by inverse adjoints. -/
noncomputable def zeroGroupEquiv (C : Submodule F (MatrixSpace F ι κ))
    (eX : (ι → F) ≃ₗ[F] (ι' → F)) (eZ : (κ → F) ≃ₗ[F] (κ' → F)) :
    TensorGroup (evaluationTwist (MatrixEvaluationGroup.operatorSpace C) AlternatingBilinearMap.zero) ≃*
      TensorGroup (evaluationTwist
        (MatrixEvaluationGroup.operatorSpace (C.map (matrixChange eX eZ).toLinearMap))
          AlternatingBilinearMap.zero) :=
  groupEquiv C eX eZ AlternatingBilinearMap.zero AlternatingBilinearMap.zero (by intros; simp)

section Incidence
universe v
variable {K I J : Type v} [Field K] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {V : J → Type v} [∀ j, AddCommGroup (V j)] [∀ j, Module K (V j)]
  (A : AffineSystem K I J V) (q : ℕ) (hq : 0 < q)
  {α β α' β' : Type*} [Fintype α] [Fintype β] [Fintype α'] [Fintype β']

theorem coordinateObstruction_change
    (eX : IncidenceTensor.PaddedInput A q ≃ₗ[K] (α → K))
    (eZ : IncidenceTensor.PaddedOutput A q ≃ₗ[K] (β → K))
    (eX' : IncidenceTensor.PaddedInput A q ≃ₗ[K] (α' → K))
    (eZ' : IncidenceTensor.PaddedOutput A q ≃ₗ[K] (β' → K)) :
    IncidenceGroup.coordinateObstruction A q hq eX' eZ' =
      (IncidenceGroup.coordinateObstruction A q hq eX eZ).map
        (matrixChange (eX.symm.trans eX') (eZ.symm.trans eZ')).toLinearMap := by
  simp only [IncidenceGroup.coordinateObstruction]
  rw [← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro f
  apply (matrixLinearEquiv (K := K) (ι := α') (κ := β')).injective
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, IncidenceGroup.operatorCoordinates,
    matrixChange, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  apply LinearMap.ext
  intro x
  simp

end Incidence

end GroupWL.EvaluationCoordinates
