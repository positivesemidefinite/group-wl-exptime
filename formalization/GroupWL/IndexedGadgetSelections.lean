import GroupWL.IndexedGadgetGroup
import GroupWL.TupleTransport
import GroupWL.MachinePrograms.RadixSelection

/-! The graph refinement compares exactly tuples of original group vertices. -/
namespace GroupWL.IndexedGadget
open Refinement

def leftGroupSelection (n m k : ℕ) : List (Fin ((size n)^k+(size m)^k)) :=
  List.ofFn (fun a : Fin (n^k) => IndexedTuples.enumeration (size n) (size m) k
    (.inl (fun i => enumeration n (.inl (finFunctionFinEquiv.symm a i)))))
def rightGroupSelection (n m k : ℕ) : List (Fin ((size n)^k+(size m)^k)) :=
  List.ofFn (fun a : Fin (m^k) => IndexedTuples.enumeration (size n) (size m) k
    (.inr (fun i => enumeration m (.inl (finFunctionFinEquiv.symm a i)))))

@[simp] theorem leftGroupSelection_length (n m k : ℕ) : (leftGroupSelection n m k).length=n^k := List.length_ofFn
@[simp] theorem rightGroupSelection_length (n m k : ℕ) : (rightGroupSelection n m k).length=m^k := List.length_ofFn

theorem leftGroupSelection_word (n m k : ℕ) (hn : 0<n) :
    (leftGroupSelection n m k).map Fin.val=MachinePrograms.RadixSelection.word n (size n) k 0 := by
  simp only [leftGroupSelection,List.map_ofFn,MachinePrograms.RadixSelection.word]
  apply congrArg List.ofFn
  funext a
  simp only [Function.comp_apply,IndexedTuples.enumeration_left,zero_add]
  have hle : n≤size n := Nat.le_add_right _ _
  have hh := MachinePrograms.NatArrayRadix.recode_tuple hn hle (finFunctionFinEquiv.symm a)
  rw [Equiv.apply_symm_apply] at hh
  rw [hh]
  congr 1

theorem rightGroupSelection_word (n m k : ℕ) (hm : 0<m) :
    (rightGroupSelection n m k).map Fin.val=MachinePrograms.RadixSelection.word m (size m) k ((size n)^k) := by
  simp only [rightGroupSelection,List.map_ofFn,MachinePrograms.RadixSelection.word]
  apply congrArg List.ofFn
  funext a
  simp only [Function.comp_apply,IndexedTuples.enumeration_right]
  have hle : m≤size m := Nat.le_add_right _ _
  have hh := MachinePrograms.NatArrayRadix.recode_tuple hm hle (finFunctionFinEquiv.symm a)
  rw [Equiv.apply_symm_apply] at hh
  rw [hh]
  congr 2

variable {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
  [DecidableEq G] [DecidableEq H] {n m k : ℕ}

def tupleEnumeration (e : G ≃ Fin n) (e' : H ≃ Fin m) :
    FiniteWL.Index (GadgetVertex G) (GadgetVertex H) k ≃ Fin ((size n)^k+(size m)^k) :=
  FiniteWL.numericEnumeration (groupEnumeration e) (groupEnumeration e')

theorem leftGroupSelection_correct (e : G ≃ Fin n) (e' : H ≃ Fin m) :
    (leftGroupSelection n m k : Multiset _) =
      (FiniteWL.leftGroupTuples (G := G) (H := H) (k := k)).map (tupleEnumeration e e') := by
  let code : (Fin k → G) ≃ Fin (n^k) :=
    (Equiv.piCongrRight (fun _ : Fin k => e)).trans finFunctionFinEquiv
  have he := Multiset.map_univ_val_equiv code
  unfold leftGroupSelection
  rw [←Fin.univ_val_map,←he,Multiset.map_map,FiniteWL.leftGroupTuples,Multiset.map_map]
  apply Multiset.map_congr rfl
  intro a ha
  simp [code,tupleEnumeration,FiniteWL.numericEnumeration,FiniteWL.reindex,groupEnumeration,vertexEquiv,
    Equiv.piCongrRight_apply]
  rfl

theorem rightGroupSelection_correct (e : G ≃ Fin n) (e' : H ≃ Fin m) :
    (rightGroupSelection n m k : Multiset _) =
      (FiniteWL.rightGroupTuples (G := G) (H := H) (k := k)).map (tupleEnumeration e e') := by
  let code : (Fin k → H) ≃ Fin (m^k) :=
    (Equiv.piCongrRight (fun _ : Fin k => e')).trans finFunctionFinEquiv
  have he := Multiset.map_univ_val_equiv code
  unfold rightGroupSelection
  rw [←Fin.univ_val_map,←he,Multiset.map_map,FiniteWL.rightGroupTuples,Multiset.map_map]
  apply Multiset.map_congr rfl
  intro a ha
  simp [code,tupleEnumeration,FiniteWL.numericEnumeration,FiniteWL.reindex,groupEnumeration,vertexEquiv,
    Equiv.piCongrRight_apply]
  rfl

theorem edges_tupleEnumeration (e : G ≃ Fin n) (e' : H ≃ Fin m)
    (a : FiniteWL.Index (GadgetVertex G) (GadgetVertex H) k) :
    (IndexedTuples.data (size n) (size m) k (by have := (e 1).isLt;unfold size;omega)).edges
      (tupleEnumeration e e' a)=
      (FiniteWL.edges a).map (fun v i => tupleEnumeration e e' (v i)) :=
  FiniteWL.edges_numericEnumeration _ (groupEnumeration e) (groupEnumeration e') a
end GroupWL.IndexedGadget
