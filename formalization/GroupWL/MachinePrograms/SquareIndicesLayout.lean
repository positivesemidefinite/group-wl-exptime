import GroupWL.MachinePrograms.SquareIndices
import GroupWL.MachinePrograms.LinkNodes
import GroupWL.MachinePrograms.PrefixSums
import GroupWL.LayoutMetadata

/-! Exact agreement between executable square endpoints and layout metadata. -/
namespace GroupWL.MachinePrograms.SquareIndices
open NatArrayLanguage LayoutMetadata
set_option maxHeartbeats 2000000

def layoutData (C : ComparisonMetadata.Table) (L : ℕ) : Data where
  width := C.coordinates
  cutoff := C.comparisons+C.comparisons*L
  comparisons := C.comparisons
  nodes := nodeCount C L
  hcount := horizontalCount C L
  leftNodes := List.ofFn (fun i : Fin (linkCount C L) => leftNode C L i)
  rightNodes := List.ofFn (fun i : Fin (linkCount C L) => rightNode C L i)
  permutation := C.permutation
  horizontalRanks := List.ofFn (fun i : Fin (horizontalFlags C L).length => horizontalRank C L i)
  verticalRanks := List.ofFn (fun i : Fin (linkLabels C L).length => verticalRank C L i)

def layoutEntry (C : ComparisonMetadata.Table) (L : ℕ) : Endpoint→ℕ→ℕ
  | .left => squareLeft C L
  | .right => squareRight C L
  | .before => squareBefore C L
  | .after => squareAfter C L

theorem layoutData_valid (C : ComparisonMetadata.Table) (L M : ℕ) (positive : 0<L)
    (sourceLength : C.source.length=C.comparisons) (targetLength : C.target.length=C.comparisons)
    (sourceValues : ∀x∈C.source,x<C.types) (targetValues : ∀x∈C.target,x<C.types)
    (permutationLength : C.permutation.length=C.comparisons*C.coordinates)
    (rankRoom : horizontalCount C L+verticalCount C L≤M) : Data.Valid (layoutData C L) M := by
  have endpoints (i : Fin (linkCount C L)) :
      leftNode C L i<nodeCount C L ∧ rightNode C L i<nodeCount C L :=
    LinkNodes.endpoint_bounds positive i.isLt sourceLength targetLength sourceValues targetValues
  refine ⟨by simp [layoutData,Data.links,linkCount],by simp [layoutData,Data.links,linkCount],
    ?_,?_,permutationLength,?_,?_,?_⟩
  · intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact (endpoints i).1
  · intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact (endpoints i).2
  · simp [layoutData,horizontalFlags,Nat.mul_comm]
  · simp [layoutData,linkLabels,Data.links,linkCount,Nat.mul_comm]
  · intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact (Nat.add_le_add_left (FilterRanks.count_mono (linkLabels C L) (Nat.le_of_lt i.isLt)) _).trans rankRoom

theorem layoutData_label (C : ComparisonMetadata.Table) (L l i a : ℕ) :
    (layoutData C L).label l i a=rightLabel C L l i a := by
  unfold Data.label layoutData rightLabel
  dsimp only
  by_cases h : l<C.comparisons+C.comparisons*L
  · simp [h]
  · have h' : ¬l<C.comparisons := by omega
    simp [h,h',linkComparison]

private theorem read_ofFn (n i : ℕ) (f : Fin n→ℕ) (hi : i<n) :
    ((List.ofFn f)[i]?).getD 0=f ⟨i,hi⟩ := by simp [hi]

theorem layoutData_entry (which : Endpoint) (C : ComparisonMetadata.Table) (L M key : ℕ)
    (valid : Data.Valid (layoutData C L) M) (index : key<(layoutData C L).count) :
    (layoutData C L).entry which key=layoutEntry C L which key := by
  let d := layoutData C L
  have hw : 0<C.coordinates := by
    have : 0<d.links*d.width := by change key<d.links*d.width*4 at index;nlinarith
    exact Nat.pos_of_mul_pos_left this
  have hq : key/4<linkCount C L*C.coordinates :=
    (Nat.div_lt_iff_lt_mul (by decide : 0<4)).mpr index
  have hl : key/4/C.coordinates<linkCount C L := (Nat.div_lt_iff_lt_mul hw).mpr hq
  have hi := Nat.mod_lt (key/4) hw
  have hn := Nat.mod_lt (key/4%C.coordinates+1) hw
  have ha : key%4/2<2 := by omega
  have hb : key%4%2<2 := by omega
  have leftRead : ((layoutData C L).leftNodes[key/4/C.coordinates]?).getD 0=leftNode C L (key/4/C.coordinates) :=
    read_ofFn _ _ _ hl
  have rightRead : ((layoutData C L).rightNodes[key/4/C.coordinates]?).getD 0=rightNode C L (key/4/C.coordinates) :=
    read_ofFn _ _ _ hl
  have leftBound : leftNode C L (key/4/C.coordinates)<nodeCount C L := by
    have hlen : key/4/C.coordinates<(layoutData C L).leftNodes.length := by rw [valid.left_length];exact hl
    have h := valid.left_values _ (List.getElem_mem hlen)
    rw [←leftRead,List.getElem?_eq_getElem hlen];exact h
  have rightBound : rightNode C L (key/4/C.coordinates)<nodeCount C L := by
    have hlen : key/4/C.coordinates<(layoutData C L).rightNodes.length := by rw [valid.right_length];exact hl
    have h := valid.right_values _ (List.getElem_mem hlen)
    rw [←rightRead,List.getElem?_eq_getElem hlen];exact h
  have horizontal (node i a b : ℕ) (hnode : node<nodeCount C L) (hi : i<C.coordinates)
      (ha : a<2) (hb : b<2) : horizontalKey C node i a b<(horizontalFlags C L).length := by
    have hm := Nat.mul_le_mul_right C.coordinates (Nat.succ_le_of_lt hnode)
    simp only [horizontalFlags,List.length_ofFn,horizontalKey]
    nlinarith
  have vertical (i a : ℕ) (hi : i<C.coordinates) (ha : a<2) :
      verticalKey C (key/4/C.coordinates) i a<(linkLabels C L).length := by
    have hm := Nat.mul_le_mul_right C.coordinates (Nat.succ_le_of_lt hl)
    simp only [linkLabels,List.length_ofFn,verticalKey]
    nlinarith
  have hrank (j : ℕ) (hj : j<(horizontalFlags C L).length) :
      ((layoutData C L).horizontalRanks[j]?).getD 0=horizontalRank C L j := read_ofFn _ _ _ hj
  have vrank (j : ℕ) (hj : j<(linkLabels C L).length) :
      ((layoutData C L).verticalRanks[j]?).getD 0=verticalRank C L j := read_ofFn _ _ _ hj
  cases which with
  | left =>
    change ((layoutData C L).horizontalRanks[horizontalKey C
      (((layoutData C L).leftNodes[key/4/C.coordinates]?).getD 0) (key/4%C.coordinates) (key%4/2) (key%4%2)]?).getD 0=_
    rw [leftRead]
    exact read_ofFn _ _ _ (horizontal _ _ _ _ leftBound hi ha hb)
  | right =>
    change ((layoutData C L).horizontalRanks[horizontalKey C
      (((layoutData C L).rightNodes[key/4/C.coordinates]?).getD 0) (key/4%C.coordinates)
      ((layoutData C L).label (key/4/C.coordinates) (key/4%C.coordinates) (key%4/2))
      ((layoutData C L).label (key/4/C.coordinates) ((key/4%C.coordinates+1)%C.coordinates) (key%4%2))]?).getD 0=_
    rw [rightRead]
    rw [hrank _ (horizontal _ _ _ _ rightBound hi
      (label_lt (layoutData C L) _ _ _ ha) (label_lt (layoutData C L) _ _ _ hb))]
    simp only [layoutData_label]
    rfl
  | before =>
    change horizontalCount C L+((layoutData C L).verticalRanks[verticalKey C (key/4/C.coordinates)
      (key/4%C.coordinates) (key%4/2)]?).getD 0=_
    rw [vrank _ (vertical _ _ hi ha)]
    rfl
  | after =>
    change horizontalCount C L+((layoutData C L).verticalRanks[verticalKey C (key/4/C.coordinates)
      ((key/4%C.coordinates+1)%C.coordinates) (key%4%2)]?).getD 0=_
    rw [vrank _ (vertical _ _ hn hb)]
    rfl

theorem layout_program_runs (which : Endpoint) (C : ComparisonMetadata.Table) (L M : ℕ) (S : State)
    (bounded : S.Bounded M) (context : Context (layoutData C L) S)
    (valid : Data.Valid (layoutData C L) M)
    (total : S.scalar .total=linkCount C L*C.coordinates*4) :
    ∃t≤41*(linkCount C L*C.coordinates*4)+4,∃T,
      Runs (storageBound Reg Arr M) (program which) S t T ∧ T.Bounded M ∧
      Context (layoutData C L) T ∧ T.array .output=List.ofFn
        (fun i : Fin (linkCount C L*C.coordinates*4) => layoutEntry C L which i) := by
  obtain ⟨t,ht,T,run,hT,hc,hout⟩ := program_runs which (layoutData C L) S M bounded context valid total
  refine ⟨t,ht,T,run,hT,hc,hout.trans ?_⟩
  apply congrArg List.ofFn
  funext i
  exact layoutData_entry which C L M i valid i.isLt

end GroupWL.MachinePrograms.SquareIndices
