import GroupWL.DenseTensorEncoding
import GroupWL.DenseParsing

/-! Polynomial dimension and dense-output bounds for the actual incidence construction. -/
namespace GroupWL.IncidenceSize

open IncidenceTensor IncidenceCoordinates DenseTensorEncoding
open scoped BigOperators

variable {F I J : Type} [Field F] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {V : J → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module F (V j)]
variable (A : AffineSystem F I J V) (q : ℕ)

def vertexBound (_A : AffineSystem F I J V) : ℕ := (Fintype.card I + Fintype.card J) * (Fintype.card I + 2)
def oldInputBound : ℕ := q * vertexBound A
def oldOutputBound : ℕ := q*q*(vertexBound A + 2*Fintype.card I*Fintype.card J)
def inputBound : ℕ := oldInputBound A q + oldOutputBound A q
def outputBound : ℕ := oldOutputBound A q + inputBound A q

theorem card_radical_le (v : I ⊕ J) :
    Fintype.card (RadicalIndex A v) ≤ Fintype.card I + 1 := by
  classical
  cases v with
  | inl i => simp [RadicalIndex]
  | inr j =>
    calc
      _ = Module.finrank F (ReadoutRadical A j) := by
        simpa only [RadicalIndex] using (Module.finrank_eq_card_chooseBasisIndex F
          (ReadoutRadical A j)).symm
      _ ≤ Module.finrank F (Neighbors A j → F) := Submodule.finrank_le _
      _ = Fintype.card (Neighbors A j) := Module.finrank_pi F
      _ ≤ Fintype.card I := Fintype.card_subtype_le _
      _ ≤ _ := Nat.le_succ _

theorem card_pair_le : Fintype.card (Pair q) ≤ q*q := by
  simpa using Fintype.card_subtype_le (fun ab : Fin q × Fin q => ab.1 < ab.2)

theorem card_incidence_le : Fintype.card (Incidence A) ≤ Fintype.card I * Fintype.card J := by
  simpa using Fintype.card_subtype_le (fun ij : I × J => ij.2 ∈ A.scope ij.1)

theorem card_oldInput_le : Fintype.card (OldInputIndex A q) ≤ oldInputBound A q := by
  classical
  rw [← Nat.card_eq_fintype_card]
  change Nat.card (Σ v : I ⊕ J, Fin q × Option (RadicalIndex A v)) ≤ _
  rw [Nat.card_sigma]
  calc
    _ ≤ ∑ _ : I ⊕ J, q*(Fintype.card I+2) := by
      apply Finset.sum_le_sum
      intro v _
      simp only [Nat.card_prod,Nat.card_eq_fintype_card,Fintype.card_prod,Fintype.card_fin,Fintype.card_option]
      exact Nat.mul_le_mul_left q (by have := card_radical_le A v; omega)
    _ = _ := by simp [oldInputBound,vertexBound]; ring

theorem card_oldOutput_le : Fintype.card (OldOutputIndex A q) ≤ oldOutputBound A q := by
  classical
  rw [← Nat.card_eq_fintype_card]
  change Nat.card ((Σ v : I ⊕ J, Pair q × Option (RadicalIndex A v)) ⊕
    (Incidence A × (Fin q × Fin q) × Option PUnit)) ≤ _
  rw [Nat.card_sum,Nat.card_sigma]
  have hsum : (∑ v : I ⊕ J, Nat.card (Pair q × Option (RadicalIndex A v))) ≤
      (Fintype.card I + Fintype.card J)*(q*q*(Fintype.card I+2)) := by
    calc
      _ ≤ ∑ _ : I ⊕ J, q*q*(Fintype.card I+2) := by
        apply Finset.sum_le_sum
        intro v _
        simp only [Nat.card_prod,Nat.card_eq_fintype_card,Fintype.card_prod,Fintype.card_option]
        exact Nat.mul_le_mul (card_pair_le q) (by have := card_radical_le A v; omega)
      _ = _ := by simp
  have he : Nat.card (Incidence A × (Fin q × Fin q) × Option PUnit) ≤
      Fintype.card I*Fintype.card J*(q*q)*2 := by
    simp only [Nat.card_prod,Nat.card_eq_fintype_card,Fintype.card_prod,
      Fintype.card_fin,Fintype.card_option,Fintype.card_punit]
    calc
      _ ≤ (Fintype.card I*Fintype.card J)*(q*q*(1+1)) :=
        Nat.mul_le_mul_right _ (card_incidence_le A)
      _ = _ := by ring
  calc
    _ ≤ _ := Nat.add_le_add hsum he
    _ = _ := by simp only [oldOutputBound,vertexBound]; ring

theorem card_input_le : Fintype.card (InputIndex A q) ≤ inputBound A q := by
  rw [← Nat.card_eq_fintype_card]
  change Nat.card (OldInputIndex A q ⊕ OldOutputIndex A q) ≤ _
  rw [Nat.card_sum]
  simpa only [Nat.card_eq_fintype_card,inputBound] using
    Nat.add_le_add (card_oldInput_le A q) (card_oldOutput_le A q)

theorem card_output_le : Fintype.card (OutputIndex A q) ≤ outputBound A q := by
  rw [← Nat.card_eq_fintype_card]
  change Nat.card (OldOutputIndex A q ⊕ InputIndex A q) ≤ _
  rw [Nat.card_sum]
  simpa only [Nat.card_eq_fintype_card,outputBound] using
    Nat.add_le_add (card_oldOutput_le A q) (card_input_le A q)

section Dense
variable (p : ℕ) [Fact p.Prime] [NeZero (2 : ZMod p)]
variable {W : J → Type} [∀ j, AddCommGroup (W j)] [∀ j, Module (ZMod p) (W j)]
variable (B : AffineSystem (ZMod p) I J W) (hq : 0 < q)
variable (ε : AlternatingBilinearMap (ZMod p) (PaddedInput B q) (PaddedOutput B q))

theorem operator_finrank_le :
    Module.finrank (ZMod p) (MatrixEvaluationGroup.operatorSpace (GlobalCokernel.C B q hq)) ≤
      inputBound B q * outputBound B q := by
  letI : Module.Finite (ZMod p)
      ((InputIndex.{0,0} B q → ZMod p) →ₗ[ZMod p] (OutputIndex.{0,0,0} B q → ZMod p)) :=
    Module.Finite.linearMap (ZMod p) (ZMod p) _ _
  calc
    _ ≤ Module.finrank (ZMod p)
      ((InputIndex.{0,0} B q → ZMod p) →ₗ[ZMod p] (OutputIndex.{0,0,0} B q → ZMod p)) :=
        Submodule.finrank_le _
    _ = Fintype.card (InputIndex.{0,0} B q)*Fintype.card (OutputIndex.{0,0,0} B q) := by
      rw [Module.finrank_linearMap]; simp only [Module.finrank_pi]
    _ ≤ _ := Nat.mul_le_mul (card_input_le B q) (card_output_le B q)

theorem description_inputDimension_le :
    (incidenceDescription p B q hq ε).inputDimension ≤
      inputBound B q + inputBound B q*outputBound B q := by
  letI : Module.Free (ZMod p) (MatrixEvaluationGroup.operatorSpace (GlobalCokernel.C B q hq)) :=
    Module.Free.of_divisionRing (ZMod p) _
  change Module.finrank (ZMod p) (_ × _) ≤ _
  rw [Module.finrank_prod]
  exact Nat.add_le_add (by simpa only [Module.finrank_pi] using card_input_le B q)
    (operator_finrank_le q p B hq)

theorem description_outputDimension_le :
    (incidenceDescription p B q hq ε).outputDimension ≤ outputBound B q := by
  change Module.finrank (ZMod p) (OutputIndex.{0,0,0} B q → ZMod p) ≤ _
  simpa only [Module.finrank_pi] using card_output_le B q

end Dense
end GroupWL.IncidenceSize
