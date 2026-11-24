import GroupWL.IncidenceTensor
import GroupWL.FiniteCodeEnumeration
import GroupWL.FiniteCodeValues
import GroupWL.MachinePrograms.PairFlags
import GroupWL.MachinePrograms.SourceNeighbors

/-! The sorted frame-pair enumeration used by both finite codes and runtime flags. -/
namespace GroupWL.FramePairEncoding
open IncidenceTensor MachinePrograms

def word (q : ℕ) : List ℕ := List.ofFn (fun i : Fin (FiniteCode.size (Pair q)) =>
  (FiniteCode.equiv (α:=Fin q×Fin q) ((FiniteCode.equiv (α:=Pair q)).symm i).val).val)

theorem word_filter (q : ℕ) : word q=(List.range (q*q)).filter (fun i => decide (i/q < i%q)) := by
  apply FiniteCode.subtype_values_filter
  intro i
  rfl

theorem word_selected (q : ℕ) : word q=SourceNeighbors.selected (PairFlags.flags q) 1 0 (q*q) := by
  rw [word_filter]
  unfold SourceNeighbors.selected
  apply List.filter_congr
  intro i hi
  have hi' : i<q*q := List.mem_range.mp hi
  simp [PairFlags.flags,PairFlags.entry,hi']
  split_ifs <;> simp_all

theorem word_read (q : ℕ) (ab : Pair q) :
    (word q)[(FiniteCode.equiv ab).val]?.getD 0=ab.val.1.val*q+ab.val.2.val := by
  simp only [word,List.getElem?_ofFn,(FiniteCode.equiv ab).isLt,dif_pos,Option.getD_some]
  erw [Equiv.symm_apply_apply]
  exact FiniteCode.prod_val ab.val.1 ab.val.2

theorem selected_length (q : ℕ) :
    (SourceNeighbors.selected (PairFlags.flags q) 1 0 (q*q)).length=FiniteCode.size (Pair q) := by
  rw [←word_selected]
  exact List.length_ofFn

end GroupWL.FramePairEncoding
