import GroupWL.FrameOrthogonality
import GroupWL.HornerCoordinates

/-! # The actual free-padding coordinate anchors -/
namespace GroupWL.FreeAnchors

open IncidenceTensor IncidenceCoordinates IncidenceGroup ObstructionDuality FrameOrthogonality
universe u
variable {F I J : Type u} [Field F] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {V : J → Type u} [∀ j, AddCommGroup (V j)] [∀ j, Module F (V j)]
variable (A : AffineSystem F I J V) (q : ℕ)

theorem inputBasis_old_free (c : OldInputIndex A q) :
    (inputBasis A q (.inl c)).2 = 0 := by
  apply (oldOutputCoordinates A q).injective
  funext d
  simp only [map_zero, Pi.zero_apply]
  change inputCoordinates A q (inputBasis A q (.inl c)) (.inr d) = 0
  rw [inputBasis, LinearEquiv.apply_symm_apply]
  simp [Pi.single_apply]

theorem inputBasis_free_old (c : OldOutputIndex A q) :
    (inputBasis A q (.inr c)).1 = 0 := by
  apply (oldInputCoordinates A q).injective
  funext d
  simp only [map_zero, Pi.zero_apply]
  change inputCoordinates A q (inputBasis A q (.inr c)) (.inl d) = 0
  rw [inputBasis, LinearEquiv.apply_symm_apply]
  simp [Pi.single_apply]

/-- The anchor projecting the free input copy onto the original output. -/
def oldOutputAnchor : PaddedInput A q →ₗ[F] PaddedOutput A q :=
  (LinearMap.inl F (OldOutput A q) (PaddedInput A q)).comp
    (LinearMap.snd F (OldInput A q) (OldOutput A q))

@[simp] theorem oldOutputAnchor_apply (x : PaddedInput A q) :
    oldOutputAnchor A q x = (x.2, 0) := rfl

theorem oldOutputAnchor_admissible (hq : 0 < q) :
    Admissible A q hq (oldOutputAnchor A q) := by
  apply (mem_annihilator _ _).mpr
  rintro c ⟨d, ⟨a, ha, rfl⟩, rfl⟩
  rw [matrixPair_comm]
  change matrixPair (operatorMatrix A q (sliceMap A q a))
    (operatorMatrix A q (oldOutputAnchor A q)) = 0
  rw [operatorMatrix_pair]
  apply Finset.sum_eq_zero
  intro b _
  cases b with
  | inl b =>
      simp only [oldOutputAnchor_apply, inputBasis_old_free]
      change outputPair A q _ 0 = 0
      simp [outputPair]
  | inr b =>
      simp only [sliceMap_apply, inputBasis_free_old, map_zero]
      change outputPair A q 0 _ = 0
      simp [outputPair]

noncomputable abbrev operators (hq : 0 < q) :=
  MatrixEvaluationGroup.operatorSpace (coordinateObstruction A q hq
    (inputCoordinates A q) (outputCoordinates A q))

/-- Transport an actual admissible operator to the evaluation space. -/
noncomputable def operatorOfAdmissible (hq : 0 < q)
    (y : PaddedInput A q →ₗ[F] PaddedOutput A q) (hy : Admissible A q hq y) :
    operators A q hq :=
  ⟨((inputCoordinates A q).arrowCongr (outputCoordinates A q)) y,
    ⟨operatorMatrix A q y, hy, by
      change matrixLinearEquiv (matrixLinearEquiv.symm _) = _
      exact matrixLinearEquiv.apply_symm_apply _⟩⟩

@[simp] theorem operatorOfAdmissible_apply (hq : 0 < q)
    (y : PaddedInput A q →ₗ[F] PaddedOutput A q) (hy : Admissible A q hq y)
    (x : InputIndex A q → F) :
    (operatorOfAdmissible A q hq y hy : (InputIndex A q → F) →ₗ[F] (OutputIndex A q → F)) x =
      outputCoordinates A q (y ((inputCoordinates A q).symm x)) := rfl

/-- The identity into the free output copy belongs to the actual operator space. -/
noncomputable def identityAnchor (hq : 0 < q) : operators A q hq :=
  operatorOfAdmissible A q hq (LinearMap.inr F (OldOutput A q) (PaddedInput A q))
    (free_output_admissible A q hq _ (fun _ => rfl))

@[simp] theorem identityAnchor_apply (hq : 0 < q) (x : InputIndex A q → F) :
    (identityAnchor A q hq : (InputIndex A q → F) →ₗ[F] (OutputIndex A q → F)) x =
      outputCoordinates A q (0, (inputCoordinates A q).symm x) := rfl

theorem identityAnchor_injective (hq : 0 < q) :
    Function.Injective (identityAnchor A q hq : (InputIndex A q → F) →ₗ[F] (OutputIndex A q → F)) := by
  intro x x' h
  have h' := congrArg Prod.snd ((outputCoordinates A q).injective h)
  exact (inputCoordinates A q).symm.injective h'

/-- Any prescribed coordinate endomorphism is available as the second anchor. -/
noncomputable def endomorphismAnchor (hq : 0 < q)
    (B : (InputIndex A q → F) →ₗ[F] (InputIndex A q → F)) : operators A q hq :=
  operatorOfAdmissible A q hq
    ((LinearMap.inr F (OldOutput A q) (PaddedInput A q)).comp
      ((inputCoordinates A q).symm.toLinearMap.comp (B.comp (inputCoordinates A q).toLinearMap)))
    (free_output_map_admissible A q hq _)

@[simp] theorem endomorphismAnchor_apply (hq : 0 < q)
    (B : (InputIndex A q → F) →ₗ[F] (InputIndex A q → F)) (x : InputIndex A q → F) :
    (endomorphismAnchor A q hq B : (InputIndex A q → F) →ₗ[F] (OutputIndex A q → F)) x = (identityAnchor A q hq : (InputIndex A q → F) →ₗ[F] (OutputIndex A q → F)) (B x) := by
  simp [endomorphismAnchor, identityAnchor_apply]

noncomputable def outputAnchor (hq : 0 < q) : operators A q hq :=
  operatorOfAdmissible A q hq (oldOutputAnchor A q) (oldOutputAnchor_admissible A q hq)

@[simp] theorem outputAnchor_apply (hq : 0 < q) (x : InputIndex A q → F) :
    (outputAnchor A q hq : (InputIndex A q → F) →ₗ[F] (OutputIndex A q → F)) x =
      outputCoordinates A q (((inputCoordinates A q).symm x).2, 0) := rfl

/-- The two output anchors cover every central coordinate exactly as prescribed. -/
theorem anchors_span_output (hq : 0 < q) (z : OutputIndex A q → F) :
    ∃ x x', (identityAnchor A q hq : (InputIndex A q → F) →ₗ[F] (OutputIndex A q → F)) x +
      (outputAnchor A q hq : (InputIndex A q → F) →ₗ[F] (OutputIndex A q → F)) x' = z := by
  let w := (outputCoordinates A q).symm z
  refine ⟨inputCoordinates A q w.2, inputCoordinates A q (0, w.1), ?_⟩
  simp only [identityAnchor_apply, outputAnchor_apply, LinearEquiv.symm_apply_apply]
  rw [← map_add]
  simpa [w] using (outputCoordinates A q).apply_symm_apply z

end GroupWL.FreeAnchors
