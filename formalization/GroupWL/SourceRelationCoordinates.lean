import GroupWL.SourceRelationTables
import GroupWL.RelationCoordinates
import GroupWL.MatrixWordExt
import GroupWL.KernelProgramCorrectness

/-! The numeric relation table agrees with the exact coordinate map used
by the constructive radical kernel. -/
namespace GroupWL.SourceTableEncoding
open SourceLayout SourceTableCoefficients ConstructiveCoordinates

variable {T E : Type} {r : ℕ} (p : ℕ) [Fact p.Prime]
  (C : ComparisonData (ZMod p) T E r) (L : ℕ)
variable [Fintype T] [Fintype E]
variable [FiniteCode (C.Horizontal L)] [FiniteCode (C.Vertical L)] [FiniteCode (C.Square L)]
local instance : Fintype (C.Block L) := FiniteCode.fintype _
local instance : Fintype (C.Readout L) := FiniteCode.fintype _
local instance : DecidableEq (C.Block L) := (FiniteCode.equiv (α := C.Block L)).decidableEq
local instance : DecidableEq (C.Readout L) := (FiniteCode.equiv (α := C.Readout L)).decidableEq

theorem readout_dimension_le (hdim : ∀ t, C.dim t≤2) (j : C.Readout L) :
    (ComputableSource.readoutCoordinates C j).dimension≤2 := by
  cases j with
  | inl h =>
    rcases h with ⟨t,h⟩
    cases t with
    | inl t => exact hdim t
    | inr x => exact Nat.le_succ 1
  | inr v => exact Nat.le_succ 1

theorem relation_entry_coordinates (hdim : ∀ t, C.dim t≤2) (j : C.Readout L)
    (i : Fin (FiniteCode.size (Neighbor p C L j)))
    (k : Fin (ComputableSource.readoutCoordinates C j).dimension) :
    (MachinePrograms.SourceRelationMatrix.entry (coefficientTable p C L) (neighborWord p C L j)
      (readoutCount p C L) (readoutIndex p C L j) (FiniteCode.size (Neighbor p C L j))
      (k.val*FiniteCode.size (Neighbor p C L j)+i.val) : ZMod p) =
    relationCoordinates (ComputableSource.affineSystem C (L:=L)) j
      (ComputableSource.readoutCoordinates C j) (Pi.single i 1) k := by
  rw [relation_entry p C L j i k.val (k.isLt.trans_le (readout_dimension_le p C L hdim j)),
    relationCoordinates_unit]
  unfold entry unit
  congr 2
  funext a
  simp [Pi.single_apply,Fin.ext_iff]


def relationWord (j : C.Readout L) : List ℕ :=
  List.ofFn (fun i : Fin ((ComputableSource.readoutCoordinates C j).dimension*
      FiniteCode.size (Neighbor p C L j)) =>
    MachinePrograms.SourceRelationMatrix.entry (coefficientTable p C L) (neighborWord p C L j)
      (readoutCount p C L) (readoutIndex p C L j) (FiniteCode.size (Neighbor p C L j)) i.val)

theorem coefficientTable_values : ∀ x∈coefficientTable p C L,x<p := by
  intro x hx
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  unfold MachinePrograms.SourceCoefficientTable.tableEntry MachinePrograms.SourceCoefficients.coefficient
  split
  · exact (Fact.out : p.Prime).pos
  · exact Nat.mod_lt _ (Fact.out : p.Prime).pos

theorem relation_value_lt (j : C.Readout L) (i : ℕ) :
    MachinePrograms.SourceRelationMatrix.entry (coefficientTable p C L) (neighborWord p C L j)
      (readoutCount p C L) (readoutIndex p C L j) (FiniteCode.size (Neighbor p C L j)) i < p := by
  unfold MachinePrograms.SourceRelationMatrix.entry
  cases hx : (coefficientTable p C L)[
      ((neighborWord p C L j)[i%FiniteCode.size (Neighbor p C L j)]?.getD 0*readoutCount p C L+
      readoutIndex p C L j)*2+i/FiniteCode.size (Neighbor p C L j)]? with
  | none => exact (Fact.out : p.Prime).pos
  | some x => exact coefficientTable_values p C L x (List.mem_of_getElem? hx)

theorem relationWord_matrix (hdim : ∀ t, C.dim t≤2) (j : C.Readout L) :
    relationWord p C L j = MatrixEncoding.word (CachedElimination.ofLinear
      (relationCoordinates (ComputableSource.affineSystem C (L:=L)) j
        (ComputableSource.readoutCoordinates C j))) := by
  apply MatrixEncoding.ofFn_eq_word
  intro k i
  erw [CachedElimination.ofLinear_entry]
  have h := congrArg ZMod.val (relation_entry_coordinates p C L hdim j i k)
  simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt (relation_value_lt p C L j _)] using h


def radicalChart (j : C.Readout L) :=
  PivotElimination.kernelChart (ComputableSource.readoutCoordinates C j).dimension
    (FiniteCode.size (Neighbor p C L j))
    (relationCoordinates (ComputableSource.affineSystem C (L:=L)) j
      (ComputableSource.readoutCoordinates C j))

theorem relation_executeRows (hdim : ∀ t, C.dim t≤2) (j : C.Readout L) :
    MachinePrograms.KernelProgram.executeRows (relationWord p C L j) p
      (FiniteCode.size (Neighbor p C L j)) (ComputableSource.readoutCoordinates C j).dimension
      (MachinePrograms.KernelProgram.initial (FiniteCode.size (Neighbor p C L j))) =
      KernelProgramCorrectness.encode (radicalChart p C L j) := by
  rw [relationWord_matrix p C L hdim j]
  exact KernelProgramCorrectness.executeRows_encode _

end GroupWL.SourceTableEncoding
