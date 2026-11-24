import GroupWL.MachinePrograms.GraphMatrixSemantics
import GroupWL.IndexedGadgetSelections
import GroupWL.IndexedTransport

/-! The concrete graph refinement input decides the manuscript's graph histogram comparison. -/
namespace GroupWL.MachinePrograms.GraphMatrixPrograms
open Refinement CompressedRefinement
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
variable {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
  [DecidableEq G] [DecidableEq H] {n m k : ℕ}

theorem pointSignature_gadget (e : G ≃ Fin n) (e' : H ≃ Fin m)
    (a : FiniteWL.Index (GadgetVertex G) (GadgetVertex H) k) :
    pointSignature (IndexedGadget.numericAdj (GroupInitial.encodedMul e))
      (IndexedGadget.numericAdj (GroupInitial.encodedMul e')) (IndexedGadget.tupleEnumeration e e' a)=
      FiniteWL.initial FiniteWL.atomicGraph FiniteWL.atomicGraph a := by
  cases a with
  | inl a =>
    change pointSignature _ _ (IndexedTuples.enumeration _ _ k (.inl (IndexedGadget.groupEnumeration e ∘ a)))=_
    rw [pointSignature_left,IndexedGadget.signature_groupEnumeration]
    rfl
  | inr a =>
    change pointSignature _ _ (IndexedTuples.enumeration _ _ k (.inr (IndexedGadget.groupEnumeration e' ∘ a)))=_
    rw [pointSignature_right,IndexedGadget.signature_groupEnumeration]
    rfl

theorem gadget_histograms_correct (e : G ≃ Fin n) (e' : H ≃ Fin m) :
    (∀ r,(IndexedGadget.leftGroupSelection n m k : Multiset _).map
      (labels (IndexedTuples.data (IndexedGadget.size n) (IndexedGadget.size m) k
        (by have := (e 1).isLt;unfold IndexedGadget.size;omega)).edges
        (pointSignature (IndexedGadget.numericAdj (GroupInitial.encodedMul e))
          (IndexedGadget.numericAdj (GroupInitial.encodedMul e'))) r)=
      (IndexedGadget.rightGroupSelection n m k : Multiset _).map
      (labels (IndexedTuples.data (IndexedGadget.size n) (IndexedGadget.size m) k
        (by have := (e 1).isLt;unfold IndexedGadget.size;omega)).edges
        (pointSignature (IndexedGadget.numericAdj (GroupInitial.encodedMul e))
          (IndexedGadget.numericAdj (GroupInitial.encodedMul e'))) r)) ↔
      ∀ r,graphGroupHistogram (G := G) k r=graphGroupHistogram (G := H) k r := by
  classical
  rw [IndexedGadget.leftGroupSelection_correct e e',IndexedGadget.rightGroupSelection_correct e e']
  rw [histogram_equivalence_transport (IndexedGadget.tupleEnumeration e e') FiniteWL.edges _
    (IndexedGadget.edges_tupleEnumeration e e') (FiniteWL.initial FiniteWL.atomicGraph FiniteWL.atomicGraph) _
    (pointSignature_gadget e e')]
  have hG : (FiniteWL.atomicGraph : (Fin k → GadgetVertex G) → _)=graphInitial (gadgetAdj (G := G)) k :=
    funext FiniteWL.atomicGraph_eq
  have hH : (FiniteWL.atomicGraph : (Fin k → GadgetVertex H) → _)=graphInitial (gadgetAdj (G := H)) k :=
    funext FiniteWL.atomicGraph_eq
  simp only [FiniteWL.leftGroupTuples,FiniteWL.rightGroupTuples,Multiset.map_map,Function.comp_def,
    FiniteWL.labels_left,FiniteWL.labels_right,hG,hH,graphGroupHistogram]
end GroupWL.MachinePrograms.GraphMatrixPrograms
