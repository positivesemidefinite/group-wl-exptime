import GroupWL.Statement
import GroupWL.GlobalCokernel
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Dense tensor descriptions of the constructed groups

A change to finite standard coordinates is an actual group isomorphism. The
description below supplies all tensor coefficients used by the fixed dense
encoding, with the dimensions equal to the corresponding vector-space ranks.
-/

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4096

namespace GroupWL.DenseTensorEncoding

open scoped commutatorElement

section Transport
variable {F X Z X' Z' : Type*} [Field F]
  [AddCommGroup X] [Module F X] [AddCommGroup Z] [Module F Z]
  [AddCommGroup X'] [Module F X'] [AddCommGroup Z'] [Module F Z']

/-- Transport an alternating tensor through specified input and output bases. -/
def transport (b : AlternatingBilinearMap F X Z)
    (eX : X ≃ₗ[F] X') (eZ : Z ≃ₗ[F] Z') : AlternatingBilinearMap F X' Z' where
  toLinearMap := LinearMap.mk₂ F (fun x y => eZ (b (eX.symm x) (eX.symm y)))
    (by intros; simp) (by intros; simp) (by intros; simp) (by intros; simp)
  map_self_eq_zero x := by simp

@[simp] theorem transport_apply (b : AlternatingBilinearMap F X Z)
    (eX : X ≃ₗ[F] X') (eZ : Z ≃ₗ[F] Z') (x y : X') :
    transport b eX eZ x y = eZ (b (eX.symm x) (eX.symm y)) := rfl

/-- The coordinate change is an isomorphism of the actual tensor groups. -/
def transportMulEquiv (b : AlternatingBilinearMap F X Z)
    (eX : X ≃ₗ[F] X') (eZ : Z ≃ₗ[F] Z') :
    TensorGroup b ≃* TensorGroup (transport b eX eZ) where
  toFun g := ⟨eX g.fst, eZ g.snd⟩
  invFun g := ⟨eX.symm g.fst, eZ.symm g.snd⟩
  left_inv g := by ext <;> simp
  right_inv g := by ext <;> simp
  map_mul' g h := by
    ext
    · change eX (g.fst + h.fst) = eX g.fst + eX h.fst
      exact map_add eX _ _
    · change eZ (g.snd + h.snd + (2 : F)⁻¹ • b g.fst h.fst) =
        eZ g.snd + eZ h.snd + (2 : F)⁻¹ • transport b eX eZ (eX g.fst) (eX h.fst)
      simp

end Transport

section GroupProperties
variable {G H : Type*} [Group G] [Group H]

theorem map_center (e : G ≃* H) :
    (Subgroup.center G).map e.toMonoidHom = Subgroup.center H := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change x ∈ Subgroup.center G at hx
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro z
    obtain ⟨w, rfl⟩ := e.surjective z
    simpa only [map_mul] using congrArg e (hx w)
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    change e.symm y ∈ Subgroup.center G
    rw [Subgroup.mem_center_iff] at hy ⊢
    intro x
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hy (e x)

theorem center_eq_derived_transport (e : G ≃* H)
    (h : Subgroup.center G = commutator G) : Subgroup.center H = commutator H := by
  rw [← map_center e, h, map_commutator_eq]
  rw [MonoidHom.range_eq_top.mpr e.surjective]
  rfl

end GroupProperties

section Dense
variable (p : ℕ) [Fact p.Prime]
variable {X Z : Type*} [AddCommGroup X] [Module (ZMod p) X]
  [AddCommGroup Z] [Module (ZMod p) Z]
  [Module.Finite (ZMod p) X] [Module.Finite (ZMod p) Z]

/-- Fixed finite standard coordinates for a finite-dimensional space. -/
noncomputable def coordinates (X : Type*) [AddCommGroup X] [Module (ZMod p) X]
    [Module.Finite (ZMod p) X] : X ≃ₗ[ZMod p] (Fin (Module.finrank (ZMod p) X) → ZMod p) :=
  (Module.finBasis (ZMod p) X).equivFun

/-- An actual dense tensor description of any finite-dimensional tensor group. -/
noncomputable def description (b : AlternatingBilinearMap (ZMod p) X Z) :
    Statement.TensorDescription p where
  inputDimension := Module.finrank (ZMod p) X
  outputDimension := Module.finrank (ZMod p) Z
  tensor := transport b (coordinates p X) (coordinates p Z)

/-- The description denotes precisely the original group, up to a proved
isomorphism, rather than a cardinality or presentation approximation. -/
noncomputable def descriptionMulEquiv (b : AlternatingBilinearMap (ZMod p) X Z) :
    TensorGroup b ≃* (description p b).Carrier :=
  transportMulEquiv b (coordinates p X) (coordinates p Z)

@[simp] theorem description_inputDimension (b : AlternatingBilinearMap (ZMod p) X Z) :
    (description p b).inputDimension = Module.finrank (ZMod p) X := rfl

@[simp] theorem description_outputDimension (b : AlternatingBilinearMap (ZMod p) X Z) :
    (description p b).outputDimension = Module.finrank (ZMod p) Z := rfl

/-- The dense coefficient is the tensor evaluated on the chosen basis pair. -/
theorem description_coefficient (b : AlternatingBilinearMap (ZMod p) X Z)
    (i j : Fin (Module.finrank (ZMod p) X)) (k : Fin (Module.finrank (ZMod p) Z)) :
    (description p b).coefficient p i j k =
      coordinates p Z (b ((coordinates p X).symm (Pi.single i 1))
        ((coordinates p X).symm (Pi.single j 1))) k := rfl

/-- The full HardGroup restrictions survive passage to the dense description. -/
theorem description_hardGroup (b : AlternatingBilinearMap (ZMod p) X Z)
    (hnonabelian : ∃ g h : TensorGroup b, g * h ≠ h * g)
    (hspecial : Subgroup.center (TensorGroup b) = commutator (TensorGroup b)) :
    Statement.HardGroup p (description p b) := by
  let e := descriptionMulEquiv p b
  refine ⟨fun g => TensorGroup.pow_char_eq_one p g, ?_, ?_, ?_⟩
  · intro g h x
    exact TensorGroup.commutator_central g h x
  · obtain ⟨g, h, hgh⟩ := hnonabelian
    refine ⟨e g, e h, ?_⟩
    intro he
    apply hgh
    apply e.injective
    simpa only [map_mul] using he.eq
  · exact center_eq_derived_transport e hspecial

end Dense

section Incidence
open IncidenceTensor IncidenceCoordinates IncidenceGroup GlobalCokernel
variable (p : ℕ) [Fact p.Prime] [NeZero (2 : ZMod p)]
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {V : J → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module (ZMod p) (V j)]
variable (A : AffineSystem (ZMod p) I J V) (q : ℕ)

/-- The operator sector is finite-dimensional as a concrete subspace of the
finite matrix space, with all scalar parameters supplied explicitly. -/
noncomputable instance canonicalOperatorFinite (hq : 0 < q) :
    Module.Finite (ZMod p) (MatrixEvaluationGroup.operatorSpace (C A q hq)) := by
  letI : Module.Finite (ZMod p)
      ((InputIndex A q → ZMod p) →ₗ[ZMod p] (OutputIndex A q → ZMod p)) :=
    Module.Finite.linearMap (ZMod p) (ZMod p) (InputIndex A q → ZMod p) (OutputIndex A q → ZMod p)
  exact FiniteDimensional.finiteDimensional_submodule
    (MatrixEvaluationGroup.operatorSpace (C A q hq))

/-- Dense description of the full padded incidence group with its actual
orthogonal-complement operator sector. -/
noncomputable def incidenceDescription (hq : 0 < q)
    (ε : AlternatingBilinearMap (ZMod p) (PaddedInput A q) (PaddedOutput A q)) :
    Statement.TensorDescription p :=
  description p (evaluationTwist (MatrixEvaluationGroup.operatorSpace (C A q hq))
    (canonicalTwist A q ε))

noncomputable def incidenceDescriptionMulEquiv (hq : 0 < q)
    (ε : AlternatingBilinearMap (ZMod p) (PaddedInput A q) (PaddedOutput A q)) :
    ConstructedGroup A q hq (inputCoordinates A q) (outputCoordinates A q) ε ≃*
      (incidenceDescription p A q hq ε).Carrier :=
  descriptionMulEquiv p _

/-- All restricted hardness-output group properties hold for the actual dense
incidence description, including noncommutativity and center=derived. -/
theorem incidenceDescription_hardGroup [Nonempty I] (hq : 3 ≤ q)
    (ε : AlternatingBilinearMap (ZMod p) (PaddedInput A q) (PaddedOutput A q)) :
    Statement.HardGroup p (incidenceDescription p A q (by omega) ε) := by
  classical
  letI : Nonempty (InputIndex A q) :=
    ⟨scalarIndex A q (.inl (Classical.arbitrary I)) ⟨0, by omega⟩⟩
  letI : Nonempty (OutputIndex A q) :=
    ⟨chargeIndex A q (by omega) (Classical.arbitrary I)⟩
  apply description_hardGroup
  · exact constructed_noncommutative A q hq (inputCoordinates A q) (outputCoordinates A q) ε
  · exact constructed_center_eq_derived A q hq (inputCoordinates A q) (outputCoordinates A q) ε

end Incidence

end GroupWL.DenseTensorEncoding
