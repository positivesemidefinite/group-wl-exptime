import GroupWL.IndexedTuples
import GroupWL.MachinePrograms.NatArrayRange

/-! The numeric arrays enumerate precisely the ordinary group tuple transitions. -/
namespace GroupWL.IndexedTuples
open IndexedRefinement

theorem edges_left (n m k : ℕ) (hn : 0 < n) (a : Fin k → Fin n) :
    (data n m k hn).edges (enumeration n m k (.inl a)) =
      (FiniteWL.edges (B := Fin m) (.inl a)).map
        (fun v i => enumeration n m k (v i)) := by
  have hf : (data n m k hn).fanout (enumeration n m k (.inl a))=n := by
    simp only [data_fanout,fanout,enumeration_left,if_pos (finFunctionFinEquiv a).isLt]
  unfold Data.edges Data.neighbors
  simp only [hf,FiniteWL.edges,Multiset.map_map]
  rw [Fin.univ_val_map]
  congr 1
  apply congrArg List.ofFn
  funext x i
  apply Fin.ext
  exact target_left a i x

theorem edges_right (n m k : ℕ) (hn : 0 < n) (a : Fin k → Fin m) :
    (data n m k hn).edges (enumeration n m k (.inr a)) =
      (FiniteWL.edges (A := Fin n) (.inr a)).map
        (fun v i => enumeration n m k (v i)) := by
  have hf : (data n m k hn).fanout (enumeration n m k (.inr a))=m := by
    simp [data_fanout,fanout]
  unfold Data.edges Data.neighbors
  simp only [hf,FiniteWL.edges,Multiset.map_map]
  rw [Fin.univ_val_map]
  congr 1
  apply congrArg List.ofFn
  funext x i
  apply Fin.ext
  exact target_right a i x

theorem edges_enumeration (n m k : ℕ) (hn : 0 < n) (a : FiniteWL.Index (Fin n) (Fin m) k) :
    (data n m k hn).edges (enumeration n m k a) =
      (FiniteWL.edges a).map (fun v i => enumeration n m k (v i)) := by
  cases a with
  | inl a => exact edges_left n m k hn a
  | inr a => exact edges_right n m k hn a

def leftSelection (n m k : ℕ) : List (Fin (n^k+m^k)) :=
  List.ofFn (fun i : Fin (n^k) => ⟨i.val,lt_of_lt_of_le i.isLt (Nat.le_add_right _ _)⟩)

def rightSelection (n m k : ℕ) : List (Fin (n^k+m^k)) :=
  List.ofFn (fun i : Fin (m^k) => ⟨n^k+i.val,Nat.add_lt_add_left i.isLt _⟩)

@[simp] theorem leftSelection_length (n m k : ℕ) : (leftSelection n m k).length=n^k := List.length_ofFn
@[simp] theorem rightSelection_length (n m k : ℕ) : (rightSelection n m k).length=m^k := List.length_ofFn

theorem leftSelection_word (n m k : ℕ) :
    (leftSelection n m k).map Fin.val=MachinePrograms.NatArrayRange.word (n^k) 0 := by
  simp [leftSelection,MachinePrograms.NatArrayRange.word,List.map_ofFn,Function.comp_def]

theorem rightSelection_word (n m k : ℕ) :
    (rightSelection n m k).map Fin.val=MachinePrograms.NatArrayRange.word (m^k) (n^k) := by
  simp [rightSelection,MachinePrograms.NatArrayRange.word,List.map_ofFn,Function.comp_def]

theorem leftSelection_correct (n m k : ℕ) :
    (leftSelection n m k : Multiset _) =
      (FiniteWL.leftTuples (A := Fin n) (B := Fin m) (k := k)).map (enumeration n m k) := by
  have he := Multiset.map_univ_val_equiv (finFunctionFinEquiv : (Fin k → Fin n) ≃ Fin (n^k))
  rw [FiniteWL.leftTuples,Multiset.map_map]
  change _=Finset.univ.val.map ((fun i : Fin (n^k) => (⟨i.val,lt_of_lt_of_le i.isLt (Nat.le_add_right _ _)⟩ : Fin (n^k+m^k))) ∘ finFunctionFinEquiv)
  rw [← Multiset.map_map,he,Fin.univ_val_map]
  rfl

theorem rightSelection_correct (n m k : ℕ) :
    (rightSelection n m k : Multiset _) =
      (FiniteWL.rightTuples (A := Fin n) (B := Fin m) (k := k)).map (enumeration n m k) := by
  have he := Multiset.map_univ_val_equiv (finFunctionFinEquiv : (Fin k → Fin m) ≃ Fin (m^k))
  rw [FiniteWL.rightTuples,Multiset.map_map]
  change _=Finset.univ.val.map ((fun i : Fin (m^k) => (⟨n^k+i.val,Nat.add_lt_add_left i.isLt _⟩ : Fin (n^k+m^k))) ∘ finFunctionFinEquiv)
  rw [← Multiset.map_map,he,Fin.univ_val_map]
  rfl
end GroupWL.IndexedTuples
