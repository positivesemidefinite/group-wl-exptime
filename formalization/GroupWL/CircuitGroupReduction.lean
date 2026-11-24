import GroupWL.CircuitLocalFamily
import GroupWL.CircuitUnsolvable
import GroupWL.IncidenceForward
import GroupWL.SourceIdentification
import GroupWL.IsomorphismTransport
import GroupWL.DenseTensorEncoding

/-! The concrete circuit-to-group construction, with the manuscript's
parameters and all three WL versions. The rejecting pair is nonisomorphic on
every input, including accepting inputs. -/
namespace GroupWL.CircuitGroupReduction

open AddressedCircuit CircuitComparisons SourceLayout SourceLayout.ComparisonData
open FrameResponses Refinement IncidenceTensor

/-- The dimension output by the reduction for each WL version. -/
def dimension (version : Version) (r : ℕ) : ℕ :=
  match version with
  | .one => Parameters.dimensionI r
  | .two => Parameters.dimensionII r
  | .three => Parameters.dimensionIII r

theorem dimension_gt_one (version : Version) (r : ℕ) : 1 < dimension version r := by
  cases version <;>
    simp only [dimension, Parameters.dimensionI, Parameters.dimensionII,
      Parameters.dimensionIII, Parameters.ringBudget, Parameters.frameWidth,
      Parameters.blockBudget] <;> omega

def wireLength (n : ℕ) : ℕ := 4*n+15

theorem frameWidth_ge_three (r : ℕ) : 3 ≤ Parameters.frameWidth r :=
  le_trans (by decide) (Parameters.frameWidth_ge_four r)

theorem frameWidth_ge_two (r : ℕ) : 2 ≤ Parameters.frameWidth r :=
  le_trans (by decide) (frameWidth_ge_three r)

variable (p : ℕ) [Fact p.Prime] [NeZero (2 : ZMod p)]
variable {T : Type} [Fintype T] {n : ℕ} (C : Circuit T (n+3))

noncomputable abbrev system :=
  (comparisons C (ZMod p)).affineSystem (L := wireLength n)

def charge : (comparisons C (ZMod p)).Block (wireLength n) → ZMod p :=
  (comparisons C (ZMod p)).sourceShift (rejectingConstant C (ZMod p))

abbrev Base := ZeroGroup (system p C) (Parameters.frameWidth (n+3))
  (frameWidth_ge_two (n+3))

abbrev Mate := ChargedGroup (system p C) (Parameters.frameWidth (n+3))
  (frameWidth_ge_two (n+3)) (charge p C)

noncomputable instance baseFintype : Fintype (Base p C) := Fintype.ofFinite _
noncomputable instance mateFintype : Fintype (Mate p C) := Fintype.ofFinite _

theorem block_nonempty : Nonempty ((comparisons C (ZMod p)).Block (wireLength n)) := by
  refine ⟨.inl ⟨.inl (.inl .broadcast), ⟨0,by omega⟩, ?_, ?_⟩⟩
  · exact ⟨false,Finset.mem_univ _⟩
  · exact ⟨false,Finset.mem_univ _⟩

/-- The explicitly output charge is insoluble independently of acceptance. -/
theorem charge_not_solvable : charge p C ∉ LinearMap.range (system p C).linearMap :=
  rejecting_shift_not_solvable C (F := ZMod p) (L := wireLength n) (by omega)

/-- Thus the pair reduction meets its nonisomorphism restriction on every input. -/
theorem nonisomorphic : ¬ Nonempty (Base p C ≃* Mate p C) := by
  letI := block_nonempty p C
  exact fun h => charge_not_solvable p C
    ((NamedChargeReduction.zero_charge_iso (system p C) (Parameters.frameWidth (n+3))
      (frameWidth_ge_two (n+3)) (frameWidth_ge_three (n+3)) (charge p C)).mp h)

private theorem rejection_pairs_fit :
    Parameters.rejectionDimension (n+3)+1 <
      (Parameters.frameWidth (n+3)-1)*((n+4)+1) := by
  rw [Parameters.rejectionDimension_eq]
  unfold Parameters.ringBudget Parameters.frameWidth Parameters.blockBudget
  have hsub : n+3+100-1 = n+102 := by omega
  rw [hsub]
  nlinarith

/-- On rejection, the actual pair is equivalent throughout the full spare range. -/
theorem rejection_equivalentII (hreject : ¬ C.Accepts) :
    EquivalentII (Parameters.rejectionDimension (n+3)) (Base p C) (Mate p C) := by
  apply IncidenceForward.equivalentII (system p C) (Parameters.frameWidth (n+3))
    (frameWidth_ge_two (n+3)) (charge p C) (n+4)
    (Parameters.rejectionDimension (n+3)) rejection_pairs_fit
    (comparisons C (ZMod p)).readoutOwner
    (comparisons C (ZMod p)).readout_mem_affine_owner_scope
  exact CircuitRejection.canonical_rejecting_exact_family C (ZMod p) hreject

/-- One numerical construction yields rejecting equivalence for all versions. -/
theorem rejection_equivalent (hreject : ¬ C.Accepts) (version : Version) :
    GroupEquivalent version (dimension version (n+3)) (Base p C) (Mate p C) := by
  have h := rejection_equivalentII p C hreject
  have hv := TensorVersionCaps.rejection_I_III (n+3) h
  cases version with
  | one => exact hv.1
  | two =>
      exact PebbleReindex.equivalentII_mono
        (by simp only [dimension, Parameters.rejectionDimension_eq, Parameters.dimensionII]; omega) h
  | three => exact hv.2

theorem rejection_not_identified (hreject : ¬ C.Accepts) (version : Version) :
    ¬ Refinement.Identifies version (dimension version (n+3)) (Base p C) := by
  intro hi
  exact nonisomorphic p C
    (hi ⟨Mate p C,inferInstance,inferInstance⟩ (rejection_equivalent p C hreject version))

/-- This intermediate statement isolates the accepting affine lemma. The
concrete source supplies that lemma in `CircuitSolvability`. -/
theorem identifies_of_scalarImageSolvability
    (hsource : SourceIdentification.ScalarImageSolvability
      (comparisons C (ZMod p)) (wireLength n))
    (hodd : Odd p) (version : Version) :
    Refinement.Identifies version (dimension version (n+3)) (Base p C) := by
  letI := block_nonempty p C
  have hi : IdentifiesII (Parameters.dimensionII (n+3)) (Base p C) :=
    SourceIdentification.identifiesII (comparisons C (ZMod p)) (wireLength n)
      (Parameters.frameWidth (n+3)) (frameWidth_ge_three (n+3)) hsource hodd
      (by unfold Parameters.dimensionII; omega)
      (by unfold Parameters.dimensionII Parameters.ringBudget Parameters.blockBudget; omega)
  have hv := TensorVersionCaps.identification_parameters (n+3) hi
  cases version with
  | one => exact hv.1
  | two => exact hv.2.1
  | three => exact hv.2.2

end GroupWL.CircuitGroupReduction
