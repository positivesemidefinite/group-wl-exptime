import GroupWL.ConstructiveIncidence
import GroupWL.FiniteCodeValues
import GroupWL.MachinePrograms.FilterRanksSemantics
import GroupWL.MachinePrograms.ArrayScaledOffsets
import GroupWL.MachinePrograms.CoordinateSizeBounds

/-! Arithmetic offsets of the scalar-first incidence input coordinates. -/
namespace GroupWL.ConstructiveIncidence
open IncidenceTensor ConstructiveCoordinates
open scoped BigOperators
variable {F I J : Type} [Field F] [DecidableEq F]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [FiniteCode I] [FiniteCode J]
variable {V : J → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module F (V j)]
variable (A : AffineSystem F I J V) (R : ∀ j, Coordinates F (ReadoutRadical A j)) (q : ℕ)

def ringDimension (v : I⊕J) : ℕ := FiniteCode.size (Option (RadicalIndex A R v))
def ringDimensions : List ℕ :=
  List.ofFn (fun i : Fin (FiniteCode.size (I⊕J)) => ringDimension A R ((FiniteCode.equiv (α:=I⊕J)).symm i))
def inputSizes : List ℕ :=
  List.ofFn (fun i : Fin (FiniteCode.size (I⊕J)) => q*ringDimension A R ((FiniteCode.equiv (α:=I⊕J)).symm i))
def inputOffset (v : I⊕J) : ℕ :=
  MachinePrograms.FilterRanks.count (inputSizes A R q) (FiniteCode.equiv v).val
def inputTotal : ℕ := MachinePrograms.FilterRanks.count (inputSizes A R q) (FiniteCode.size (I⊕J))

def readoutWidths : List ℕ :=
  List.ofFn (fun i : Fin (FiniteCode.size J) => (R ((FiniteCode.equiv (α:=J)).symm i)).dimension)

@[simp] theorem ringDimension_block (i : I) : ringDimension A R (.inl i)=2 := rfl
@[simp] theorem ringDimension_readout (j : J) : ringDimension A R (.inr j)=(R j).dimension+1 := rfl

theorem ringDimension_runtime (v : I⊕J) : ringDimension A R v=
    MachinePrograms.RingDimensions.value (readoutWidths A R) (FiniteCode.size I)
      (FiniteCode.equiv v).val := by
  cases v with
  | inl i =>
    rw [FiniteCode.sum_inl_val]
    simp [MachinePrograms.RingDimensions.value,(FiniteCode.equiv i).isLt]
  | inr j =>
    rw [FiniteCode.sum_inr_val]
    simp [MachinePrograms.RingDimensions.value,readoutWidths]
    erw [Equiv.symm_apply_apply]

theorem ringDimensions_runtime : ringDimensions A R=
    MachinePrograms.RingDimensions.dimensions (readoutWidths A R) (FiniteCode.size I) := by
  unfold ringDimensions MachinePrograms.RingDimensions.dimensions
  simp only [readoutWidths,List.length_ofFn]
  apply congrArg List.ofFn
  funext i
  rw [ringDimension_runtime]
  simp [readoutWidths]

theorem inputIndex_val (v : I⊕J) (a : Fin q) (c : Option (RadicalIndex A R v)) :
    (FiniteCode.equiv (α:=OldInputIndex A R q) ⟨v,(a,c)⟩).val=
      inputOffset A R q v+a.val*ringDimension A R v+(FiniteCode.equiv c).val := by
  rw [FiniteCode.sigma_val,FiniteCode.prod_val,FiniteCode.fin_val]
  unfold inputOffset inputSizes
  rw [MachinePrograms.FilterRanks.count_ofFn _ _ (FiniteCode.equiv v).isLt.le]
  change (∑i : Fin (FiniteCode.equiv v).val,
      q*ringDimension A R ((FiniteCode.equiv (α:=I⊕J)).symm ⟨i.val,_⟩))+
        (a.val*ringDimension A R v+(FiniteCode.equiv c).val)=_
  rw [Nat.add_assoc]

theorem inputTotal_eq : inputTotal A R q=FiniteCode.size (OldInputIndex A R q) := by
  unfold inputTotal inputSizes
  rw [MachinePrograms.FilterRanks.count_ofFn _ _ le_rfl]
  change (∑i : Fin (FiniteCode.size (I⊕J)),
      q*ringDimension A R ((FiniteCode.equiv (α:=I⊕J)).symm ⟨i.val,_⟩))=
    ∑i : Fin (FiniteCode.size (I⊕J)),q*ringDimension A R ((FiniteCode.equiv (α:=I⊕J)).symm i)
  rfl

theorem inputSizes_scaled : inputSizes A R q=MachinePrograms.ArrayScaledOffsets.scaled (ringDimensions A R) q := by
  unfold inputSizes MachinePrograms.ArrayScaledOffsets.scaled ringDimensions
  simp only [List.length_ofFn,List.getElem?_ofFn,dif_pos,Option.getD_some]
  apply congrArg List.ofFn
  funext i
  simp [i.isLt,Nat.mul_comm]

def scalarSelectors (hq : 0<q) : List ℕ :=
  List.ofFn (fun i : Fin (FiniteCode.size (I⊕J)) =>
    (FiniteCode.equiv (α:=OldInputIndex A R q)
      ⟨(FiniteCode.equiv (α:=I⊕J)).symm i,(⟨0,hq⟩,none)⟩).val)

theorem scalarIndex_offset (hq : 0<q) (v : I⊕J) :
    (FiniteCode.equiv (α:=OldInputIndex A R q) ⟨v,(⟨0,hq⟩,none)⟩).val=inputOffset A R q v := by
  rw [inputIndex_val]
  simp

theorem scalarSelectors_offsets (hq : 0<q) :
    scalarSelectors A R q hq=List.ofFn (fun i : Fin (FiniteCode.size (I⊕J)) =>
      MachinePrograms.FilterRanks.count (inputSizes A R q) i.val) := by
  apply congrArg List.ofFn
  funext i
  rw [scalarIndex_offset]
  simp [inputOffset]

end GroupWL.ConstructiveIncidence
