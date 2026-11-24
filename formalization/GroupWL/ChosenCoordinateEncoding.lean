import GroupWL.ScalarTestCoordinates
import GroupWL.GeneratedCoordinateEntries
import GroupWL.MachinePrograms.ChosenKernel

/-! Exact basis agreement between the runtime chosen-space kernel and the
constructive tensor coordinates. -/
namespace GroupWL.ConstructiveIncidence
open IncidenceTensor ConstructiveCoordinates MachinePrograms
variable {F I J : Type} [Field F] [DecidableEq F]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [FiniteCode I] [FiniteCode J]
variable {V : J → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module F (V j)]
variable (A : AffineSystem F I J V) (R : ∀ j, Coordinates F (ReadoutRadical A j)) (q : ℕ)

def chosenChart (hq : 0<q) := PivotElimination.kernelChart (FiniteCode.size (I⊕J))
  (FiniteCode.size (OldInputIndex A R q)) (scalarCoordinates A R q hq)

theorem chosen_inverse_coordinates (hq : 0<q)
    (x : Fin (chosenCoordinates A R q hq).dimension → F) :
    (oldInputCoordinates A R q).equiv (((chosenCoordinates A R q hq).equiv.symm x).val)=
      (chosenChart A R q hq).lift x := by
  exact GeneratedCoordinateEntries.kernel_inverse_coordinates
    (oldInputCoordinates A R q) (Coordinates.pi (I⊕J)) (scalarTests A q hq) x

theorem chosenLift_entry (hq : 0<q) (k : Fin (chosenCoordinates A R q hq).dimension)
    (i : OldInputIndex A R q) :
    oldInputEquiv A R q (((chosenCoordinates A R q hq).equiv.symm (Pi.single k 1)).val) i=
      (chosenChart A R q hq).lift (Pi.single k 1) (FiniteCode.equiv i) := by
  have h := congrFun (chosen_inverse_coordinates A R q hq (Pi.single k 1)) (FiniteCode.equiv i)
  change oldInputEquiv A R q _ ((FiniteCode.equiv (α:=OldInputIndex A R q)).symm
    (FiniteCode.equiv i))=_ at h
  rw [Equiv.symm_apply_apply] at h
  exact h

theorem chosenSizes_runtime : ChosenKernel.sizes (readoutWidths A R) (FiniteCode.size I) q=inputSizes A R q := by
  unfold ChosenKernel.sizes
  rw [←ringDimensions_runtime,←inputSizes_scaled]

theorem chosenTotal_runtime : ChosenKernel.total (readoutWidths A R) (FiniteCode.size I) q=
    FiniteCode.size (OldInputIndex A R q) := by
  unfold ChosenKernel.total
  rw [chosenSizes_runtime]
  have hlen : (inputSizes A R q).length=FiniteCode.size (I⊕J) := List.length_ofFn
  rw [hlen]
  exact inputTotal_eq A R q

theorem chosenSelectors_runtime (hq : 0<q) :
    ChosenKernel.selectors (readoutWidths A R) (FiniteCode.size I) q=scalarSelectors A R q hq := by
  unfold ChosenKernel.selectors
  rw [chosenSizes_runtime,scalarSelectors_offsets]
  simp only [inputSizes,List.length_ofFn]
  apply congrArg List.ofFn
  funext i
  rfl

end ConstructiveIncidence

namespace ConstructiveIncidence
open IncidenceTensor ConstructiveCoordinates MachinePrograms
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [FiniteCode I] [FiniteCode J]
variable (p : ℕ) [Fact p.Prime]
variable {V : J → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module (ZMod p) (V j)]
variable (A : AffineSystem (ZMod p) I J V) (R : ∀ j, Coordinates (ZMod p) (ReadoutRadical A j)) (q : ℕ)

theorem chosenData_runtime (hq : 0<q) :
    ChosenKernel.data p (readoutWidths A R) (FiniteCode.size I) q=
      KernelProgramCorrectness.encode (chosenChart A R q hq) := by
  unfold ChosenKernel.data
  rw [chosenTotal_runtime,chosenSelectors_runtime A R q hq]
  simpa only [readoutWidths,List.length_ofFn] using scalar_executeRows p A R q hq

theorem chosenData_entry (hq : 0<q) (k : Fin (chosenCoordinates A R q hq).dimension)
    (i : OldInputIndex A R q) :
    ((ChosenKernel.data p (readoutWidths A R) (FiniteCode.size I) q).lift[
      (FiniteCode.equiv i).val*(chosenCoordinates A R q hq).dimension+k.val]?.getD 0 : ZMod p)=
    oldInputEquiv A R q (((chosenCoordinates A R q hq).equiv.symm (Pi.single k 1)).val) i := by
  rw [chosenData_runtime p A R q hq]
  change ((MatrixEncoding.word (CachedElimination.ofLinear (chosenChart A R q hq).lift))[
    (FiniteCode.equiv i).val*(chosenChart A R q hq).width+k.val]?.getD 0 : ZMod p)=_
  have h := MatrixEncoding.word_read (CachedElimination.ofLinear (chosenChart A R q hq).lift)
    (FiniteCode.equiv i) k
  erw [CachedElimination.ofLinear_entry] at h
  unfold MatrixArithmetic.read at h
  rw [h,ZMod.natCast_zmod_val]
  exact (chosenLift_entry A R q hq k i).symm

end GroupWL.ConstructiveIncidence
