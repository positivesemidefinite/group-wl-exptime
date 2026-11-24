import GroupWL.WedgeConstraintEncoding
import GroupWL.MachinePrograms.WedgeKernel
import GroupWL.GeneratedConstraintEntries

/-! Padded numeric wedge entries are exactly the obstruction generators. -/
namespace GroupWL.ConstructiveIncidence
open IncidenceTensor ConstructiveCoordinates MachinePrograms
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [FiniteCode I] [FiniteCode J]
variable (p : ℕ) [Fact p.Prime]
variable {V : J → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module (ZMod p) (V j)]
variable (A : AffineSystem (ZMod p) I J V)
  (R : ∀ j, Coordinates (ZMod p) (ReadoutRadical A j)) (q : ℕ)
local instance wedgeObstructionOldInputDecidable : DecidableEq (OldInputIndex A R q) :=
  (FiniteCode.equiv (α:=OldInputIndex A R q)).decidableEq

def wedgeEntry (hq : 0<q) := WedgeConstraints.entry (wedgeDescriptors p A R q)
  (formMatrix p A R q) (chosenFormMatrix p A R q hq) p
  (FiniteCode.size (OldInputIndex A R q)) (FiniteCode.size (OldOutputIndex A R q))
  (chosenCoordinates A R q hq).dimension (FiniteCode.size (InputIndex A R q))
  (FiniteCode.size (OutputIndex A R q))

private theorem flat_div (a n b : ℕ) (hb : b<n) : (a*n+b)/n=a := by
  rw [Nat.mul_comm a n,Nat.mul_add_div (by omega),Nat.div_eq_of_lt hb,Nat.add_zero]
private theorem flat_mod (a n b : ℕ) (hb : b<n) : (a*n+b)%n=b := by
  rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hb]

theorem wedgeEntry_obstruction (hq : 0<q) (k : Fin (chosenCoordinates A R q hq).dimension)
    (i : InputIndex A R q) (z : OutputIndex A R q) :
    (wedgeEntry p A R q hq ((k.val*FiniteCode.size (InputIndex A R q)+(FiniteCode.equiv i).val)*
      FiniteCode.size (OutputIndex A R q)+(FiniteCode.equiv z).val) : ZMod p)=
    ConstructiveTensor.obstructionMap A R q hq ((chosenCoordinates A R q hq).equiv.symm (Pi.single k 1)) i z := by
  let ni := FiniteCode.size (InputIndex A R q)
  let no := FiniteCode.size (OutputIndex A R q)
  have hi : (FiniteCode.equiv i).val<ni := (FiniteCode.equiv i).isLt
  have hz : (FiniteCode.equiv z).val<no := (FiniteCode.equiv z).isLt
  have hinner : (FiniteCode.equiv i).val*no+(FiniteCode.equiv z).val<ni*no := by nlinarith
  have hrow : ((k.val*ni+(FiniteCode.equiv i).val)*no+(FiniteCode.equiv z).val)/(ni*no)=k.val := by
    have he : (k.val*ni+(FiniteCode.equiv i).val)*no+(FiniteCode.equiv z).val=
      k.val*(ni*no)+((FiniteCode.equiv i).val*no+(FiniteCode.equiv z).val) := by ring
    rw [he,flat_div _ _ _ hinner]
  dsimp only [ni,no] at hi hz hrow
  unfold wedgeEntry WedgeConstraints.entry
  rw [obstruction_entry]
  simp only [flat_mod _ _ _ hz,flat_div _ _ _ hz,flat_mod _ _ _ hi,hrow]
  cases z with
  | inr z =>
    simp [FiniteCode.sum_inr_val,paddedSliceCoordinates]
  | inl z =>
    cases i with
    | inl i =>
      have hi' := (FiniteCode.equiv (α:=OldInputIndex A R q) i).isLt
      have hz' := (FiniteCode.equiv (α:=OldOutputIndex A R q) z).isLt
      simp only [FiniteCode.sum_inl_val,hi',hz',and_self,if_true]
      rw [wedgeValue_cast]
      simp only [paddedSliceCoordinates]
      congr 1
      funext j
      simp [paddedSliceCoordinates,Pi.single_apply]
    | inr i =>
      simp [FiniteCode.sum_inl_val,FiniteCode.sum_inr_val,paddedSliceCoordinates,omegaCoordinates,
        squareZeroProduct,endpointCoordinates,Pi.single_apply]
      cases z <;> rfl

end GroupWL.ConstructiveIncidence
