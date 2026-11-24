import GroupWL.MachinePrograms.LayoutRecordBounds
import GroupWL.MachinePrograms.LayoutIncidenceCorrectness
import GroupWL.LayoutMetadataFormArrays
import GroupWL.LayoutMetadataFinalArrays

/-! The complete source-record program realizes the original typed data exactly. -/
namespace GroupWL.MachinePrograms.LayoutRecordPrograms
open NatArrayLanguage SourceLayout
set_option maxHeartbeats 3000000
set_option synthInstance.maxSize 65536
set_option maxRecDepth 32768

def coefficientArray : SourceCoefficients.Arr→Arr
  | .left => .inl (.inl (.inr (.inr .left)))
  | .right => .inl (.inl (.inr (.inr .right)))
  | .before => .inl (.inl (.inr (.inr .before)))
  | .after => .inl (.inl (.inr (.inr .after)))
  | .leftForm => .inl (.inr (.inr (.inl (.inr (.inr .output)))))
  | .rightForm => .inl (.inr (.inr (.inr (.inr (.inr .output)))))
def dimensionArray : Arr := .inr (.inl (.inr .output))
def chargeArray : Arr := .inr (.inr (.inr (.inr 2)))

variable {T E : Type} [FiniteCode T] [FiniteCode E] {r : ℕ}
  (p : ℕ) [Fact p.Prime] (C : ComparisonData (ZMod p) T E r) (L q : ℕ)

theorem Output.coefficients {S : State} (h : Output (ComparisonMetadata.ofComparison p C) L q S)
    (a : SourceCoefficients.Arr) : S.array (coefficientArray a)=SourceTableEncoding.coefficientData p C L a := by
  cases a with
  | left => exact (h.forms.incidence.endpoints .left).trans (LayoutMetadata.selected_left p C L)
  | right => exact (h.forms.incidence.endpoints .right).trans (LayoutMetadata.selected_right p C L)
  | before => exact (h.forms.incidence.endpoints .before).trans (LayoutMetadata.selected_before p C L)
  | after => exact (h.forms.incidence.endpoints .after).trans (LayoutMetadata.selected_after p C L)
  | leftForm => exact h.forms.leftForm.trans (LayoutMetadata.selectedForms_correct p C L false)
  | rightForm => exact h.forms.rightForm.trans (LayoutMetadata.selectedForms_correct p C L true)

theorem Output.dimension_correct {S : State} (h : Output (ComparisonMetadata.ofComparison p C) L q S) :
    S.array dimensionArray=SourceTableEncoding.readoutDimensions p C L := by
  change S.right.left.right.array .output=_
  rw [h.dimensions]
  unfold dimensionWord
  rw [LayoutMetadata.horizontalCount_correct,LayoutMetadata.verticalCount_correct]
  exact LayoutMetadata.readoutDimensionProgram_correct p C L

theorem Output.charge_correct {S : State} (h : Output (ComparisonMetadata.ofComparison p C) L q S) :
    S.array chargeArray=LayoutMetadata.sourceCharge p C L
      (fun e => if (FiniteCode.equiv e).val=q then 1 else 0) := by
  apply h.charge.trans
  simpa [chargeWord,SquareChargeRecords.word,LayoutMetadata.squareFlags,ComparisonMetadata.ofComparison]
    using LayoutMetadata.squareCharges_selected p C L q

theorem Output.zero_charge {S : State}
    (h : Output (ComparisonMetadata.ofComparison p C) L (FiniteCode.size E) S) :
    S.array chargeArray=LayoutMetadata.sourceCharge p C L (fun _ => 0) := by
  rw [h.charge_correct p C L (FiniteCode.size E)]
  congr 1
  funext e
  have he := (FiniteCode.equiv e).isLt
  simp [show (FiniteCode.equiv e).val≠FiniteCode.size E by omega]

theorem Output.rejecting_charge {A : Type} [FiniteCode A]
    (D : AddressedCircuit.Circuit A r) {S : State}
    (h : Output (ComparisonMetadata.ofComparison p (CircuitComparisons.comparisons D (ZMod p)))
      L (FiniteCode.size (CircuitComparisons.Comparison D)-3) S) :
    S.array chargeArray=LayoutMetadata.sourceCharge p (CircuitComparisons.comparisons D (ZMod p)) L
      (CircuitComparisons.rejectingConstant D (ZMod p)) := by
  rw [h.charge_correct p (CircuitComparisons.comparisons D (ZMod p)) L
    (FiniteCode.size (CircuitComparisons.Comparison D)-3)]
  congr 1
  funext e
  exact (CircuitComparisonCodes.rejectingConstant_eq_code D e).symm

theorem program_runs_correct (S : State)
    (bounded : S.Bounded (budget (ComparisonMetadata.ofComparison p C) L))
    (input : LayoutIncidencePrograms.Input (ComparisonMetadata.ofComparison p C) L S.left.left)
    (source : S.left.right.right.left.left.array .forms=ComparisonMetadata.sourceForm p C)
    (target : S.left.right.right.right.left.array .forms=ComparisonMetadata.targetForm p C)
    (dimensions : S.right.left.left.left.array .input=ComparisonMetadata.dimensions p C)
    (special : S.right.right.left.scalar .special=q) (qbound : q≤FiniteCode.size E)
    (positive : 0<L) (width : 0<r) :
    ∃t≤80500*(LayoutIncidencePrograms.magnitude (ComparisonMetadata.ofComparison p C) L)^3,∃U,
      Runs (storageBound Reg Arr (budget (ComparisonMetadata.ofComparison p C) L)) program S t U ∧
      U.Bounded (budget (ComparisonMetadata.ofComparison p C) L) ∧
      (∀a,U.array (coefficientArray a)=SourceTableEncoding.coefficientData p C L a) ∧
      U.array dimensionArray=SourceTableEncoding.readoutDimensions p C L ∧
      U.array chargeArray=LayoutMetadata.sourceCharge p C L
        (fun e => if (FiniteCode.equiv e).val=q then 1 else 0) := by
  obtain ⟨t,ht,U,run,hU,hout⟩ := program_runs_polynomial (ComparisonMetadata.ofComparison p C) L q S
    bounded input source target dimensions special qbound (LayoutIncidencePrograms.comparison_valid p C) positive width
    (by change (ComparisonMetadata.sourceForm p C).length=2*FiniteCode.size E
        rw [ComparisonMetadata.sourceForm_length];omega)
    (by change (ComparisonMetadata.targetForm p C).length=2*FiniteCode.size E
        rw [ComparisonMetadata.targetForm_length];omega)
  exact ⟨t,ht,U,run,hU,hout.coefficients p C L q,hout.dimension_correct p C L q,hout.charge_correct p C L q⟩

end GroupWL.MachinePrograms.LayoutRecordPrograms
