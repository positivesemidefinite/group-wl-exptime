import GroupWL.ConstructiveInputEncoding
import GroupWL.MachinePrograms.SelectorMatrix
import GroupWL.MatrixWordExt
import GroupWL.KernelProgramCorrectness

/-! The scalar tests are the explicitly selected input coordinates. -/
namespace GroupWL.ConstructiveIncidence
open IncidenceTensor ConstructiveCoordinates
variable {F I J : Type} [Field F] [DecidableEq F]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [FiniteCode I] [FiniteCode J]
variable {V : J → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module F (V j)]
variable (A : AffineSystem F I J V) (R : ∀ j, Coordinates F (ReadoutRadical A j)) (q : ℕ)

def scalarCoordinates (hq : 0<q) :
    (Fin (FiniteCode.size (OldInputIndex A R q)) → F) →ₗ[F]
      (Fin (FiniteCode.size (I⊕J)) → F) :=
  (Coordinates.pi (I⊕J)).equiv.toLinearMap.comp
    ((scalarTests A q hq).comp (oldInputCoordinates A R q).equiv.symm.toLinearMap)

theorem scalarCoordinates_apply (hq : 0<q)
    (x : Fin (FiniteCode.size (OldInputIndex A R q)) → F)
    (v : Fin (FiniteCode.size (I⊕J))) :
    scalarCoordinates A R q hq x v=x (FiniteCode.equiv
      (α:=OldInputIndex A R q) ⟨(FiniteCode.equiv (α:=I⊕J)).symm v,(⟨0,hq⟩,none)⟩) := by
  rfl

theorem scalarCoordinates_unit (hq : 0<q)
    (v : Fin (FiniteCode.size (I⊕J)))
    (i : Fin (FiniteCode.size (OldInputIndex A R q))) :
    scalarCoordinates A R q hq (Pi.single i 1) v=
      if i.val=(scalarSelectors A R q hq)[v.val]?.getD 0 then 1 else 0 := by
  rw [scalarCoordinates_apply]
  simp [scalarSelectors,Pi.single_apply,Fin.ext_iff,v.isLt,eq_comm]

end ConstructiveIncidence

namespace ConstructiveIncidence
open IncidenceTensor ConstructiveCoordinates
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [FiniteCode I] [FiniteCode J]
variable (p : ℕ) [Fact p.Prime]
variable {V : J → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module (ZMod p) (V j)]
variable (A : AffineSystem (ZMod p) I J V) (R : ∀ j, Coordinates (ZMod p) (ReadoutRadical A j)) (q : ℕ)

theorem scalarWord_matrix (hq : 0<q) :
    MachinePrograms.SelectorMatrix.word (scalarSelectors A R q hq)
      (FiniteCode.size (OldInputIndex A R q))=
    MatrixEncoding.word (CachedElimination.ofLinear (scalarCoordinates A R q hq)) := by
  unfold MachinePrograms.SelectorMatrix.word
  simp only [scalarSelectors,List.length_ofFn]
  apply MatrixEncoding.ofFn_eq_word
  intro v i
  erw [CachedElimination.ofLinear_entry]
  rw [scalarCoordinates_unit]
  have hn : 0<FiniteCode.size (OldInputIndex A R q) := Nat.zero_lt_of_lt i.isLt
  have hmod : (v.val*FiniteCode.size (OldInputIndex A R q)+i.val)%
      FiniteCode.size (OldInputIndex A R q)=i.val := by
    rw [Nat.add_mod,Nat.mul_mod_left,Nat.zero_add,Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt i.isLt]
  have hdiv : (v.val*FiniteCode.size (OldInputIndex A R q)+i.val)/
      FiniteCode.size (OldInputIndex A R q)=v.val := by
    rw [Nat.mul_comm v.val, Nat.mul_add_div hn,Nat.div_eq_of_lt i.isLt,Nat.add_zero]
  simp only [MachinePrograms.SelectorMatrix.entry,hmod,hdiv]
  change (if i.val=(scalarSelectors A R q hq)[v.val]?.getD 0 then 1 else 0)=
    (if i.val=(scalarSelectors A R q hq)[v.val]?.getD 0 then (1:ZMod p) else 0).val
  split_ifs <;> simp [ZMod.val_one, Nat.mod_eq_of_lt (Fact.out : p.Prime).one_lt]

theorem scalar_executeRows (hq : 0<q) :
    MachinePrograms.KernelProgram.executeRows
      (MachinePrograms.SelectorMatrix.word (scalarSelectors A R q hq)
        (FiniteCode.size (OldInputIndex A R q))) p
      (FiniteCode.size (OldInputIndex A R q)) (FiniteCode.size (I⊕J))
      (MachinePrograms.KernelProgram.initial (FiniteCode.size (OldInputIndex A R q)))=
    KernelProgramCorrectness.encode (PivotElimination.kernelChart (FiniteCode.size (I⊕J))
      (FiniteCode.size (OldInputIndex A R q)) (scalarCoordinates A R q hq)) := by
  rw [scalarWord_matrix]
  exact KernelProgramCorrectness.executeRows_encode _

end GroupWL.ConstructiveIncidence
