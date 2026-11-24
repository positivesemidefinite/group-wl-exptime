import GroupWL.MachinePrograms.InitialMatrixSemantics
import GroupWL.MachinePrograms.WordMatrixSemantics
import GroupWL.TupleTransport
import GroupWL.IndexedTransport

/-! Both group-tuple initial relations recover the manuscript's exact I/II tests. -/
namespace GroupWL.MachinePrograms.GroupTupleSemantics
open Refinement CompressedRefinement
variable {G H : Type} [Group G] [Group H] [Fintype G] [Fintype H]
  [DecidableEq G] [DecidableEq H] {n m k : ℕ}

theorem leftSelection_correct (e : G≃Fin n) (e' : H≃Fin m) :
    (IndexedTuples.leftSelection n m k : Multiset _) =
      (FiniteWL.leftTuples (A:=G) (B:=H) (k:=k)).map (FiniteWL.numericEnumeration e e') := by
  let code : (Fin k→G)≃Fin (n^k) := (Equiv.piCongrRight (fun _ : Fin k=>e)).trans finFunctionFinEquiv
  have he := Multiset.map_univ_val_equiv code
  unfold IndexedTuples.leftSelection
  rw [←Fin.univ_val_map,←he,Multiset.map_map,FiniteWL.leftTuples,Multiset.map_map]
  apply Multiset.map_congr rfl
  intro a ha
  rfl

theorem rightSelection_correct (e : G≃Fin n) (e' : H≃Fin m) :
    (IndexedTuples.rightSelection n m k : Multiset _) =
      (FiniteWL.rightTuples (A:=G) (B:=H) (k:=k)).map (FiniteWL.numericEnumeration e e') := by
  let code : (Fin k→H)≃Fin (m^k) := (Equiv.piCongrRight (fun _ : Fin k=>e')).trans finFunctionFinEquiv
  have he := Multiset.map_univ_val_equiv code
  unfold IndexedTuples.rightSelection
  rw [←Fin.univ_val_map,←he,Multiset.map_map,FiniteWL.rightTuples,Multiset.map_map]
  apply Multiset.map_congr rfl
  intro a ha
  rfl

theorem pointSignature_enumeration (e : G≃Fin n) (e' : H≃Fin m)
    (a : FiniteWL.Index G H k) :
    InitialMatrixPrograms.pointSignature (GroupInitial.encodedMul e) (GroupInitial.encodedMul e')
      (FiniteWL.numericEnumeration e e' a)=FiniteWL.initial FiniteWL.atomicI FiniteWL.atomicI a := by
  cases a with
  | inl a =>
      change InitialMatrixPrograms.pointSignature _ _ (IndexedTuples.enumeration n m k (.inl (e ∘ a)))=_
      rw [InitialMatrixPrograms.pointSignature_left,GroupInitial.signature_encoded]
      rfl
  | inr a =>
      change InitialMatrixPrograms.pointSignature _ _ (IndexedTuples.enumeration n m k (.inr (e' ∘ a)))=_
      rw [InitialMatrixPrograms.pointSignature_right,GroupInitial.signature_encoded]
      rfl

theorem original_histograms_correct (e : G≃Fin n) (e' : H≃Fin m) :
    (∀r,(IndexedTuples.leftSelection n m k : Multiset _).map
      (labels (IndexedTuples.data n m k (by have := (e 1).isLt;omega)).edges
        (InitialMatrixPrograms.pointSignature (GroupInitial.encodedMul e) (GroupInitial.encodedMul e')) r)=
      (IndexedTuples.rightSelection n m k : Multiset _).map
      (labels (IndexedTuples.data n m k (by have := (e 1).isLt;omega)).edges
        (InitialMatrixPrograms.pointSignature (GroupInitial.encodedMul e) (GroupInitial.encodedMul e')) r)) ↔
      EquivalentI k G H := by
  classical
  rw [leftSelection_correct e e',rightSelection_correct e e']
  rw [histogram_equivalence_transport (FiniteWL.numericEnumeration e e') FiniteWL.edges _
    (FiniteWL.edges_numericEnumeration _ e e') (FiniteWL.initial FiniteWL.atomicI FiniteWL.atomicI) _
    (pointSignature_enumeration e e')]
  have hG : (FiniteWL.atomicI : (Fin k→G)→_)=initialI k := funext FiniteWL.atomicI_eq
  have hH : (FiniteWL.atomicI : (Fin k→H)→_)=initialI k := funext FiniteWL.atomicI_eq
  simp only [FiniteWL.leftTuples,FiniteWL.rightTuples,Multiset.map_map,Function.comp_def,
    FiniteWL.labels_left,FiniteWL.labels_right,hG,hH,EquivalentI,Equivalent,histogram]

theorem word_histograms_correct (e : G≃Fin n) (e' : H≃Fin m) :
    (∀r,(IndexedTuples.leftSelection n m k : Multiset _).map
      (labels (IndexedTuples.data n m k (by have := (e 1).isLt;omega)).edges
        (WordMatrixSemantics.pointInitial e e') r)=
      (IndexedTuples.rightSelection n m k : Multiset _).map
      (labels (IndexedTuples.data n m k (by have := (e 1).isLt;omega)).edges
        (WordMatrixSemantics.pointInitial e e') r)) ↔ EquivalentII k G H := by
  classical
  rw [leftSelection_correct e e',rightSelection_correct e e']
  rw [histogram_equivalence_transport (FiniteWL.numericEnumeration e e') FiniteWL.edges _
    (FiniteWL.edges_numericEnumeration _ e e') (FiniteWL.initial (initialII k) (initialII k)) _
    (WordMatrixSemantics.pointInitial_enumeration e e')]
  simp only [FiniteWL.leftTuples,FiniteWL.rightTuples,Multiset.map_map,Function.comp_def,
    FiniteWL.labels_left,FiniteWL.labels_right,EquivalentII,Equivalent,histogram]

end GroupWL.MachinePrograms.GroupTupleSemantics
