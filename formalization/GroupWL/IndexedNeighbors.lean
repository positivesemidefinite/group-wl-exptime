import GroupWL.MachinePrograms.NeighborScan
import GroupWL.MachinePrograms.GraphInitial

/-! Numeric neighbor-list data for ordinary one-dimensional graph refinement. -/
namespace GroupWL.IndexedNeighbors
open IndexedRefinement
variable {n : ℕ}

def rowList (adj : Fin n → Fin n → Bool) (a : Fin n) : List (Fin n) :=
  (List.finRange n).filter (adj a)

theorem rowList_length_le (adj : Fin n → Fin n → Bool) (a : Fin n) : (rowList adj a).length≤n := by
  simpa [rowList] using List.length_filter_le (adj a) (List.finRange n)

private theorem range_eq_map_finRange (m : ℕ) : List.range m=(List.finRange m).map Fin.val := by
  apply List.ext_getElem?
  intro i
  by_cases h : i<m
  · simp [List.finRange,h]
  · have hh : (List.range m)[i]?=none := List.getElem?_eq_none (by simpa using Nat.le_of_not_gt h)
    simp [List.finRange,h,hh]

theorem scan_neighbors (adj : Fin n → Fin n → Bool) (a : Fin n) :
    MachinePrograms.NeighborScan.neighbors (MachinePrograms.GraphInitial.tableWord adj) n a.val n=
      (rowList adj a).map Fin.val := by
  unfold MachinePrograms.NeighborScan.neighbors
  rw [range_eq_map_finRange,List.filter_map]
  congr 1
  apply List.filter_congr
  intro b hb
  simp only [Function.comp_apply,IndexedRefinement.read,MachinePrograms.GraphInitial.tableWord_read]
  cases adj a b <;> rfl

def data (hn : 0<n) (adj : Fin n → Fin n → Bool) : Data n 1 n where
  positive := hn
  fanout a := (rowList adj a).length
  fanout_le := rowList_length_le adj
  target a x _ := ((rowList adj a)[x.val]?).getD ⟨0,hn⟩

theorem data_fanout (hn : 0<n) (adj : Fin n → Fin n → Bool) (a : Fin n) :
    (data hn adj).fanout a=
      (MachinePrograms.NeighborScan.neighbors (MachinePrograms.GraphInitial.tableWord adj) n a.val n).length := by
  simp [data,scan_neighbors]

theorem data_target (hn : 0<n) (adj : Fin n → Fin n → Bool) (a x : Fin n) (i : Fin 1) :
    ((data hn adj).target a x i).val=
      read (MachinePrograms.NeighborScan.neighbors (MachinePrograms.GraphInitial.tableWord adj) n a.val n) x.val := by
  rw [scan_neighbors]
  simp only [data,IndexedRefinement.read,List.getElem?_map]
  cases h : (rowList adj a)[x.val]? <;> rfl

theorem data_neighbors (hn : 0<n) (adj : Fin n → Fin n → Bool) (a : Fin n) :
    (data hn adj).neighbors a=(rowList adj a).map (fun v => fun _ : Fin 1 => v) := by
  apply List.ext_getElem
  · simp [Data.neighbors,data]
  · intro j hj hj'
    have hlt : j<(rowList adj a).length := by simpa using hj'
    funext i
    simp [Data.neighbors,data,List.getElem_ofFn,List.getElem?_eq_getElem hlt]

theorem rowList_multiset (adj : Fin n → Fin n → Bool) (a : Fin n) :
    (rowList adj a : Multiset _)=(Finset.univ.filter (fun x => adj a x=true)).val := by
  ext x
  simp [rowList,Fin.univ_def]

theorem data_edges (hn : 0<n) (adj : Fin n → Fin n → Bool) (a : Fin n) :
    (data hn adj).edges a=(Finset.univ.filter (fun x => adj a x=true)).val.map (fun x => fun _ : Fin 1 => x) := by
  unfold Data.edges
  rw [data_neighbors]
  simpa using congrArg (Multiset.map (fun x => fun _ : Fin 1 => x)) (rowList_multiset adj a)
end GroupWL.IndexedNeighbors
