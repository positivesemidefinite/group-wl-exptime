import GroupWL.ConstructiveTensor
import GroupWL.IncidenceSize

/-! Polynomial dimension and serialization bounds for the computed tensor. -/
namespace GroupWL.ConstructiveTensorSize

open IncidenceTensor ConstructiveCoordinates ConstructiveIncidence

variable {F I J : Type} [Field F] [DecidableEq F]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [FiniteCode I] [FiniteCode J]
variable {V : J → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module F (V j)]
variable (A : AffineSystem F I J V) (R : ∀ j, Coordinates F (ReadoutRadical A j)) (q : ℕ)

theorem dimension_eq_finrank {X : Type*} [AddCommGroup X] [Module F X]
    (D : Coordinates F X) : D.dimension = Module.finrank F X := by
  simpa using D.equiv.finrank_eq.symm

theorem input_card_eq : Fintype.card (InputIndex A R q) =
    Fintype.card (IncidenceCoordinates.InputIndex.{0,0} A q) := by
  have h := ((inputEquiv A R q).symm.trans (IncidenceCoordinates.inputCoordinates A q)).finrank_eq
  simpa using h

theorem output_card_eq : Fintype.card (OutputIndex A R q) =
    Fintype.card (IncidenceCoordinates.OutputIndex.{0,0,0} A q) := by
  have h := ((outputEquiv A R q).symm.trans (IncidenceCoordinates.outputCoordinates A q)).finrank_eq
  simpa using h

theorem input_card_le : Fintype.card (InputIndex A R q) ≤ IncidenceSize.inputBound A q :=
  (input_card_eq A R q).le.trans (IncidenceSize.card_input_le A q)

theorem output_card_le : Fintype.card (OutputIndex A R q) ≤ IncidenceSize.outputBound A q :=
  (output_card_eq A R q).le.trans (IncidenceSize.card_output_le A q)

theorem operator_dimension_le (hq : 0 < q) :
    (ConstructiveTensor.operatorCoordinates A R q hq).dimension ≤
      IncidenceSize.inputBound A q * IncidenceSize.outputBound A q := by
  letI : Module.Finite F ((InputIndex A R q → F) →ₗ[F] (OutputIndex A R q → F)) :=
    Module.Finite.linearMap F F _ _
  rw [dimension_eq_finrank]
  calc
    _ ≤ Module.finrank F ((InputIndex A R q → F) →ₗ[F] (OutputIndex A R q → F)) :=
      Submodule.finrank_le _
    _ = Fintype.card (InputIndex A R q) * Fintype.card (OutputIndex A R q) := by
      rw [Module.finrank_linearMap]; simp only [Module.finrank_pi]
    _ ≤ _ := Nat.mul_le_mul (input_card_le A R q) (output_card_le A R q)

theorem input_dimension_le (hq : 0 < q) :
    (ConstructiveTensor.groupInputCoordinates A R q hq).dimension ≤
      IncidenceSize.inputBound A q +
        IncidenceSize.inputBound A q * IncidenceSize.outputBound A q := by
  change FiniteCode.size (InputIndex A R q) + _ ≤ _
  rw [← FiniteCode.card_eq_size]
  exact Nat.add_le_add (input_card_le A R q) (operator_dimension_le A R q hq)

section Prime
variable (p : ℕ) [Fact p.Prime]
variable {W : J → Type} [∀ j, AddCommGroup (W j)] [∀ j, Module (ZMod p) (W j)]
variable (B : AffineSystem (ZMod p) I J W)
  (S : ∀ j, Coordinates (ZMod p) (ReadoutRadical B j))
  (hq : 0 < q)
  (ε : AlternatingBilinearMap (ZMod p) (PaddedInput B q) (PaddedOutput B q))

theorem description_inputDimension_le :
    (ConstructiveTensor.description q p B S hq ε).inputDimension ≤
      IncidenceSize.inputBound B q +
        IncidenceSize.inputBound B q * IncidenceSize.outputBound B q :=
  input_dimension_le B S q hq

theorem description_outputDimension_le :
    (ConstructiveTensor.description q p B S hq ε).outputDimension ≤
      IncidenceSize.outputBound B q := by
  change FiniteCode.size (OutputIndex B S q) ≤ _
  rw [← FiniteCode.card_eq_size]
  exact output_card_le B S q

def inputBound : ℕ := IncidenceSize.inputBound B q +
  IncidenceSize.inputBound B q * IncidenceSize.outputBound B q

def wordBound : ℕ := inputBound q p B + IncidenceSize.outputBound B q + 2 +
  inputBound q p B * (inputBound q p B * (IncidenceSize.outputBound B q * p))

theorem description_word_length_le :
    ((ConstructiveTensor.description q p B S hq ε).denseWord p).length ≤ wordBound q p B := by
  have hx := description_inputDimension_le q p B S hq ε
  have hz := description_outputDimension_le q p B S hq ε
  refine (Statement.denseWord_length_le p _).trans ?_
  exact Nat.add_le_add
    (Nat.add_le_add_right (Nat.add_le_add hx hz) 2)
    (Nat.mul_le_mul hx (Nat.mul_le_mul hx (Nat.mul_le_mul_right p hz)))

end Prime
end GroupWL.ConstructiveTensorSize
