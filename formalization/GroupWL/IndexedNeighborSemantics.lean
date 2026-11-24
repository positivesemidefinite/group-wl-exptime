import GroupWL.FiniteNeighborWL
import GroupWL.IndexedGadgetGroup
import GroupWL.IndexedNeighbors
import GroupWL.IndexedTransport
import GroupWL.MachinePrograms.DisjointGraphTable
import GroupWL.MachinePrograms.NatArrayRange

/-! Numeric ordinary-neighbor refinement agrees with Version III at dimension one. -/
namespace GroupWL.IndexedNeighbors
open Refinement CompressedRefinement

def edgesOf {A : Type*} [Fintype A] [DecidableEq A] (adj : A → A → Bool) (a : A) : Multiset (Fin 1 → A) :=
  (Finset.univ.filter (fun b => adj a b=true)).val.map (fun b => fun _ => b)

theorem edgesOf_transport {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (e : A ≃ B) (adjA : A → A → Bool) (adjB : B → B → Bool)
    (h : ∀ a b,adjB (e a) (e b)=adjA a b) (a : A) :
    edgesOf adjB (e a)=(edgesOf adjA a).map (fun v i => e (v i)) := by
  have hs : (Finset.univ.filter (fun b => adjB (e a) b=true))=
      (Finset.univ.filter (fun b => adjA a b=true)).map e.toEmbedding := by
    rw [←Finset.map_univ_equiv e,Finset.filter_map]
    congr 1
    ext b
    simp [h]
  rw [edgesOf,hs,Finset.map_val,Multiset.map_map,edgesOf,Multiset.map_map]
  rfl

variable {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
  [DecidableEq G] [DecidableEq H] {n m : ℕ}

def gadgetUnionAdj : FiniteWL.NeighborIndex G H → FiniteWL.NeighborIndex G H → Bool
  | .inl a,.inl b => FiniteWL.gadgetAdjTest a b
  | .inr a,.inr b => FiniteWL.gadgetAdjTest a b
  | _,_ => false

theorem edgesOf_gadgetUnion (a : FiniteWL.NeighborIndex G H) :
    edgesOf gadgetUnionAdj a=FiniteWL.neighborEdges a := by
  classical
  cases a with
  | inl a =>
    have hs : (Finset.univ.filter (fun b : FiniteWL.NeighborIndex G H => gadgetUnionAdj (.inl a) b=true))=
        (Finset.univ.filter (gadgetAdj a)).map Function.Embedding.inl := by
      ext b;cases b <;> simp [gadgetUnionAdj,FiniteWL.gadgetAdjTest_correct]
    rw [edgesOf,hs,Finset.map_val,Multiset.map_map]
    rfl
  | inr a =>
    have hs : (Finset.univ.filter (fun b : FiniteWL.NeighborIndex G H => gadgetUnionAdj (.inr a) b=true))=
        (Finset.univ.filter (gadgetAdj a)).map Function.Embedding.inr := by
      ext b;cases b <;> simp [gadgetUnionAdj,FiniteWL.gadgetAdjTest_correct]
    rw [edgesOf,hs,Finset.map_val,Multiset.map_map]
    rfl

def neighborEnumeration (e : G ≃ Fin n) (e' : H ≃ Fin m) :
    FiniteWL.NeighborIndex G H ≃ Fin (IndexedGadget.size n+IndexedGadget.size m) :=
  (Equiv.sumCongr (IndexedGadget.groupEnumeration e) (IndexedGadget.groupEnumeration e')).trans finSumFinEquiv

def unionNumericAdj (e : G ≃ Fin n) (e' : H ≃ Fin m) :=
  MachinePrograms.DisjointGraphTable.sumAdj (IndexedGadget.numericAdj (MachinePrograms.GroupInitial.encodedMul e))
    (IndexedGadget.numericAdj (MachinePrograms.GroupInitial.encodedMul e'))

theorem unionNumericAdj_correct (e : G ≃ Fin n) (e' : H ≃ Fin m) (a b : FiniteWL.NeighborIndex G H) :
    unionNumericAdj e e' (neighborEnumeration e e' a) (neighborEnumeration e e' b)=gadgetUnionAdj a b := by
  cases a <;> cases b <;>
    simp [unionNumericAdj,neighborEnumeration,MachinePrograms.DisjointGraphTable.sumAdj,gadgetUnionAdj,
      IndexedGadget.numericAdj_groupEnumeration]

def neighborData (e : G ≃ Fin n) (e' : H ≃ Fin m) :
    IndexedRefinement.Data (IndexedGadget.size n+IndexedGadget.size m) 1 (IndexedGadget.size n+IndexedGadget.size m) :=
  data (by have := (e 1).isLt;unfold IndexedGadget.size;omega) (unionNumericAdj e e')

theorem edges_neighborEnumeration (e : G ≃ Fin n) (e' : H ≃ Fin m) (a : FiniteWL.NeighborIndex G H) :
    (neighborData e e').edges (neighborEnumeration e e' a)=
      (FiniteWL.neighborEdges a).map (fun v i => neighborEnumeration e e' (v i)) := by
  rw [neighborData,data_edges]
  change edgesOf (unionNumericAdj e e') (neighborEnumeration e e' a)=_
  rw [edgesOf_transport (neighborEnumeration e e') gadgetUnionAdj _ (unionNumericAdj_correct e e'),edgesOf_gadgetUnion]

def leftVertexSelection (n m : ℕ) : List (Fin (IndexedGadget.size n+IndexedGadget.size m)) :=
  List.ofFn (fun x : Fin n => finSumFinEquiv (.inl (IndexedGadget.enumeration n (.inl x))))
def rightVertexSelection (n m : ℕ) : List (Fin (IndexedGadget.size n+IndexedGadget.size m)) :=
  List.ofFn (fun x : Fin m => finSumFinEquiv (.inr (IndexedGadget.enumeration m (.inl x))))

@[simp] theorem leftVertexSelection_length (n m : ℕ) : (leftVertexSelection n m).length=n := List.length_ofFn
@[simp] theorem rightVertexSelection_length (n m : ℕ) : (rightVertexSelection n m).length=m := List.length_ofFn

theorem leftVertexSelection_word (n m : ℕ) :
    (leftVertexSelection n m).map Fin.val=MachinePrograms.NatArrayRange.word n 0 := by
  simp [leftVertexSelection,List.map_ofFn,MachinePrograms.NatArrayRange.word,Function.comp_def]

theorem rightVertexSelection_word (n m : ℕ) :
    (rightVertexSelection n m).map Fin.val=MachinePrograms.NatArrayRange.word m (IndexedGadget.size n) := by
  simp [rightVertexSelection,List.map_ofFn,MachinePrograms.NatArrayRange.word,Function.comp_def]

theorem leftVertexSelection_correct (e : G ≃ Fin n) (e' : H ≃ Fin m) :
    (leftVertexSelection n m : Multiset _)=(FiniteWL.leftGroupVertices (G := G) (H := H)).map (neighborEnumeration e e') := by
  unfold leftVertexSelection
  rw [←Fin.univ_val_map,←Multiset.map_univ_val_equiv e,Multiset.map_map,
    FiniteWL.leftGroupVertices,Multiset.map_map]
  rfl

theorem rightVertexSelection_correct (e : G ≃ Fin n) (e' : H ≃ Fin m) :
    (rightVertexSelection n m : Multiset _)=(FiniteWL.rightGroupVertices (G := G) (H := H)).map (neighborEnumeration e e') := by
  unfold rightVertexSelection
  rw [←Fin.univ_val_map,←Multiset.map_univ_val_equiv e',Multiset.map_map,
    FiniteWL.rightGroupVertices,Multiset.map_map]
  rfl

theorem neighbor_histograms_correct (e : G ≃ Fin n) (e' : H ≃ Fin m) :
    (∀ r,(leftVertexSelection n m : Multiset _).map (labels (neighborData e e').edges (fun _ => ()) r)=
      (rightVertexSelection n m : Multiset _).map (labels (neighborData e e').edges (fun _ => ()) r)) ↔
      ∀ r,neighborGroupHistogram (G := G) r=neighborGroupHistogram (G := H) r := by
  classical
  rw [leftVertexSelection_correct e e',rightVertexSelection_correct e e']
  rw [histogram_equivalence_transport (neighborEnumeration e e') FiniteWL.neighborEdges _
    (edges_neighborEnumeration e e') (fun _ => ()) (fun _ => ()) (by intro a;rfl)]
  have hl (r : ℕ) : (FiniteWL.leftGroupVertices (G := G) (H := H)).map
      (labels FiniteWL.neighborEdges (fun _ => ()) r)=
        (neighborGroupHistogram (G := G) r).map (FiniteWL.liftNeighbor r) := by
    simp only [FiniteWL.leftGroupVertices,Multiset.map_map,neighborGroupHistogram,Multiset.map_map]
    exact Multiset.map_congr rfl (fun a _ => FiniteWL.neighbor_labels_left r (.inl a))
  have hr (r : ℕ) : (FiniteWL.rightGroupVertices (G := G) (H := H)).map
      (labels FiniteWL.neighborEdges (fun _ => ()) r)=
        (neighborGroupHistogram (G := H) r).map (FiniteWL.liftNeighbor r) := by
    simp only [FiniteWL.rightGroupVertices,Multiset.map_map,neighborGroupHistogram,Multiset.map_map]
    exact Multiset.map_congr rfl (fun a _ => FiniteWL.neighbor_labels_right r (.inl a))
  simp only [hl,hr]
  exact forall_congr' (fun r => (Multiset.map_injective (FiniteWL.liftNeighbor_injective r)).eq_iff)
end GroupWL.IndexedNeighbors
