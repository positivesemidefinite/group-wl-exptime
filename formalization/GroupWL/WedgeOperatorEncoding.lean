import GroupWL.WedgeObstructionEntries
import GroupWL.KernelProgramCorrectness

/-! The executed wedge kernel is the exact constructive operator kernel. -/
namespace GroupWL.ConstructiveIncidence
open IncidenceTensor ConstructiveCoordinates MachinePrograms GeneratedCoordinateEntries GeneratedCoordinates
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [FiniteCode I] [FiniteCode J]
variable (p : ℕ) [Fact p.Prime]
variable {V : J → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module (ZMod p) (V j)]
variable (A : AffineSystem (ZMod p) I J V)
  (R : ∀ j, Coordinates (ZMod p) (ReadoutRadical A j)) (q : ℕ)

def wedgeWord (hq : 0<q) := WedgeKernel.word (wedgeDescriptors p A R q)
  (formMatrix p A R q) (chosenFormMatrix p A R q hq) p
  (FiniteCode.size (OldInputIndex A R q)) (FiniteCode.size (OldOutputIndex A R q))
  (chosenCoordinates A R q hq).dimension (FiniteCode.size (InputIndex A R q))
  (FiniteCode.size (OutputIndex A R q))

theorem wedgeEntry_lt (hq : 0<q) (i : ℕ) : wedgeEntry p A R q hq i<p := by
  unfold wedgeEntry WedgeConstraints.entry
  split_ifs
  · exact Nat.mod_lt _ (Fact.out : p.Prime).pos
  · exact (Fact.out : p.Prime).pos

private theorem position_surjective {F ι κ : Type} [Field F] [DecidableEq F]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [FiniteCode ι] [FiniteCode κ]
    (a : Fin (matrixCoordinates (F:=F) (ι:=ι) (κ:=κ)).dimension) :
    ∃i : Fin (FiniteCode.size ι),∃z : Fin (FiniteCode.size κ),matrixPosition (F:=F) i z=a := by
  let b := (FiniteCode.equiv (α:=Σ _ : ι,Fin (FiniteCode.size κ))).symm a
  refine ⟨FiniteCode.equiv b.1,b.2,?_⟩
  unfold matrixPosition
  rw [Equiv.symm_apply_apply]
  exact (FiniteCode.equiv (α:=Σ _ : ι,Fin (FiniteCode.size κ))).apply_symm_apply a

theorem wedgeWord_matrix (hq : 0<q) : wedgeWord p A R q hq=
    MatrixEncoding.word (CachedElimination.ofLinear
      (constraintMap (chosenCoordinates A R q hq) (ConstructiveTensor.obstructionMap A R q hq))) := by
  let ni := FiniteCode.size (InputIndex A R q)
  let no := FiniteCode.size (OutputIndex A R q)
  let dim := (matrixCoordinates (F:=ZMod p) (ι:=InputIndex A R q) (κ:=OutputIndex A R q)).dimension
  have hd : dim=ni*no := matrixCoordinates_dimension
  have hw : wedgeWord p A R q hq=List.ofFn (fun i : Fin ((chosenCoordinates A R q hq).dimension*dim)=>
      wedgeEntry p A R q hq i.val) := by
    rw [hd]
    unfold wedgeWord WedgeKernel.word
    simp only [Nat.mul_assoc]
    rfl
  rw [hw]
  apply MatrixEncoding.ofFn_eq_word
  intro k j
  obtain ⟨i,z,rfl⟩ := position_surjective j
  erw [CachedElimination.ofLinear_entry]
  rw [constraintMap_entry]
  have h := wedgeEntry_obstruction p A R q hq k
    ((FiniteCode.equiv (α:=InputIndex A R q)).symm i)
    ((FiniteCode.equiv (α:=OutputIndex A R q)).symm z)
  simp only [Equiv.apply_symm_apply] at h
  have hx : k.val*dim+(matrixPosition (F:=ZMod p) i z).val=(k.val*ni+i.val)*no+z.val := by
    rw [hd,matrixPosition_val]
    dsimp [ni,no]
    ring
  rw [hx]
  have hv := congrArg ZMod.val h
  simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt (wedgeEntry_lt p A R q hq _)] using hv

theorem wedgeKernel_data (hq : 0<q) :
    WedgeKernel.data (wedgeDescriptors p A R q) (formMatrix p A R q) (chosenFormMatrix p A R q hq) p
      (FiniteCode.size (OldInputIndex A R q)) (FiniteCode.size (OldOutputIndex A R q))
      (chosenCoordinates A R q hq).dimension (FiniteCode.size (InputIndex A R q))
      (FiniteCode.size (OutputIndex A R q))=
    KernelProgramCorrectness.encode (operatorChart (chosenCoordinates A R q hq)
      (ConstructiveTensor.obstructionMap A R q hq)) := by
  unfold WedgeKernel.data
  change KernelProgram.executeRows (wedgeWord p A R q hq) _ _ _ _=_
  rw [wedgeWord_matrix]
  have h := KernelProgramCorrectness.executeRows_encode
    (constraintMap (chosenCoordinates A R q hq) (ConstructiveTensor.obstructionMap A R q hq))
  simpa only [operatorChart,matrixCoordinates_dimension] using h

end GroupWL.ConstructiveIncidence
