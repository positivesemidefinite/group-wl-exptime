import GroupWL.IncidenceWedgeForms
import GroupWL.MachinePrograms.WedgeConstraints

/-! The modular wedge table agrees entrywise with the exact obstruction map. -/
namespace GroupWL.ConstructiveIncidence
open IncidenceTensor ConstructiveCoordinates MachinePrograms
open scoped BigOperators
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [FiniteCode I] [FiniteCode J]
variable (p : ℕ) [Fact p.Prime]
variable {V : J → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module (ZMod p) (V j)]
variable (A : AffineSystem (ZMod p) I J V)
  (R : ∀ j, Coordinates (ZMod p) (ReadoutRadical A j)) (q : ℕ)
local instance wedgeOldInputDecidable : DecidableEq (OldInputIndex A R q) :=
  (FiniteCode.equiv (α:=OldInputIndex A R q)).decidableEq

def wedgeDescriptors : WedgeConstraints.Descriptors where
  u0 := List.ofFn (fun i : Fin (FiniteCode.size (OldOutputIndex A R q)) =>
    (FiniteCode.equiv (formU0 A R q ((FiniteCode.equiv (α:=OldOutputIndex A R q)).symm i))).val)
  v0 := List.ofFn (fun i : Fin (FiniteCode.size (OldOutputIndex A R q)) =>
    (FiniteCode.equiv (formV0 A R q ((FiniteCode.equiv (α:=OldOutputIndex A R q)).symm i))).val)
  u1 := List.ofFn (fun i : Fin (FiniteCode.size (OldOutputIndex A R q)) =>
    (FiniteCode.equiv (formU1 A R q ((FiniteCode.equiv (α:=OldOutputIndex A R q)).symm i))).val)
  v1 := List.ofFn (fun i : Fin (FiniteCode.size (OldOutputIndex A R q)) =>
    (FiniteCode.equiv (formV1 A R q ((FiniteCode.equiv (α:=OldOutputIndex A R q)).symm i))).val)
  second := List.ofFn (fun i : Fin (FiniteCode.size (OldOutputIndex A R q)) =>
    if formSecond A R q ((FiniteCode.equiv (α:=OldOutputIndex A R q)).symm i) then 1 else 0)

def formMatrix := MatrixEncoding.word (CachedElimination.ofLinear (numericFormMap A R q))
def chosenFormMatrix (hq : 0<q) := MatrixEncoding.word
  (CachedElimination.ofLinear ((numericFormMap A R q).comp (chosenChart A R q hq).lift))

theorem wedge_cast (a b c d : ℕ) : (WedgeConstraints.wedge p a b c d : ZMod p)=
    (a:ZMod p)*b-c*d := by
  have h : c*d%p≤a*b%p+p := by have := Nat.mod_lt (c*d) (Fact.out : p.Prime).pos; omega
  simp only [WedgeConstraints.wedge,ZMod.natCast_mod,Nat.cast_sub h,Nat.cast_add,Nat.cast_mul,
    ZMod.natCast_self,add_zero]

theorem formMatrix_read (f : FormIndex A R q) (i : OldInputIndex A R q) :
    (MatrixArithmetic.read (formMatrix p A R q)
      ((FiniteCode.equiv f).val*FiniteCode.size (OldInputIndex A R q)+(FiniteCode.equiv i).val) : ZMod p)=
    formValue A R q (Pi.single i 1) f := by
  rw [formMatrix,MatrixEncoding.word_read]
  erw [CachedElimination.ofLinear_entry]
  rw [ZMod.natCast_zmod_val,numericFormMap_apply]
  congr 1
  funext j
  simp [Pi.single_apply,eq_comm]

theorem chosenFormMatrix_read (hq : 0<q) (f : FormIndex A R q)
    (k : Fin (chosenCoordinates A R q hq).dimension) :
    (MatrixArithmetic.read (chosenFormMatrix p A R q hq)
      ((FiniteCode.equiv f).val*(chosenCoordinates A R q hq).dimension+k.val) : ZMod p)=
    formValue A R q (oldInputEquiv A R q (((chosenCoordinates A R q hq).equiv.symm (Pi.single k 1)).val)) f := by
  unfold chosenFormMatrix
  erw [MatrixEncoding.word_read]
  erw [CachedElimination.ofLinear_entry]
  rw [ZMod.natCast_zmod_val,LinearMap.comp_apply,numericFormMap_apply]
  congr 1
  funext i
  exact (chosenLift_entry A R q hq k i).symm

theorem wedgeValue_cast (hq : 0<q) (k : Fin (chosenCoordinates A R q hq).dimension)
    (i : OldInputIndex A R q) (z : OldOutputIndex A R q) :
    (WedgeConstraints.value (wedgeDescriptors p A R q) (formMatrix p A R q) (chosenFormMatrix p A R q hq)
      p (FiniteCode.size (OldInputIndex A R q)) (chosenCoordinates A R q hq).dimension
      k.val (FiniteCode.equiv i).val (FiniteCode.equiv z).val : ZMod p)=
    omegaCoordinates A R q
      (oldInputEquiv A R q (((chosenCoordinates A R q hq).equiv.symm (Pi.single k 1)).val)) (Pi.single i 1) z := by
  have reads : ∀g : OldOutputIndex A R q → FormIndex A R q,
      MatrixArithmetic.read (List.ofFn (fun j : Fin (FiniteCode.size (OldOutputIndex A R q)) =>
        (FiniteCode.equiv (g ((FiniteCode.equiv (α:=OldOutputIndex A R q)).symm j))).val))
        (FiniteCode.equiv z).val=(FiniteCode.equiv (g z)).val := by
    intro g
    simp [MatrixArithmetic.read]
  have second : MatrixArithmetic.read (wedgeDescriptors p A R q).second (FiniteCode.equiv z).val=
      if formSecond A R q z then 1 else 0 := by simp [wedgeDescriptors,MatrixArithmetic.read]
  unfold WedgeConstraints.value
  rw [ZMod.natCast_mod,Nat.cast_add,second]
  simp only [wedgeDescriptors,reads]
  unfold WedgeConstraints.term
  simp only [wedge_cast,chosenFormMatrix_read,formMatrix_read]
  rw [omega_formValue]
  cases h : formSecond A R q z <;> simp [h,wedge_cast,chosenFormMatrix_read,formMatrix_read]

end GroupWL.ConstructiveIncidence
