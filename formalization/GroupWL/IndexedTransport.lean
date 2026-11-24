import GroupWL.CompressedRefinement

/-! Coordinate changes of materialized-refinement input data. These lemmas
transport the verified indexed algorithm to the original finite structures. -/
namespace GroupWL.CompressedRefinement
open Refinement
universe u v w
variable {A : Type u} {B : Type v} [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B] {k : ℕ}

theorem labels_transport (e : A ≃ B)
    (edgesA : A → Multiset (Fin k → A)) (edgesB : B → Multiset (Fin k → B))
    (hedges : ∀ a,edgesB (e a)=(edgesA a).map (fun v => e ∘ v))
    {C : Type w} (initialA : A → C) (initialB : B → C)
    (hinitial : ∀ a,initialB (e a)=initialA a) (r : ℕ) (a : A) :
    labels edgesB initialB r (e a)=labels edgesA initialA r a := by
  induction r generalizing a with
  | zero => exact hinitial a
  | succ r ih =>
      apply Prod.ext
      · exact ih a
      · simp only [labels,hedges,Multiset.map_map]
        apply Multiset.map_congr rfl
        intro v hv
        funext i
        exact ih (v i)

theorem histogram_transport (e : A ≃ B)
    (edgesA : A → Multiset (Fin k → A)) (edgesB : B → Multiset (Fin k → B))
    (hedges : ∀ a,edgesB (e a)=(edgesA a).map (fun v => e ∘ v))
    {C : Type w} (initialA : A → C) (initialB : B → C)
    (hinitial : ∀ a,initialB (e a)=initialA a) (r : ℕ) (s : Multiset A) :
    (s.map e).map (labels edgesB initialB r)=s.map (labels edgesA initialA r) := by
  rw [Multiset.map_map]
  apply Multiset.map_congr rfl
  intro a ha
  exact labels_transport e edgesA edgesB hedges initialA initialB hinitial r a

theorem histogram_equivalence_transport (e : A ≃ B)
    (edgesA : A → Multiset (Fin k → A)) (edgesB : B → Multiset (Fin k → B))
    (hedges : ∀ a,edgesB (e a)=(edgesA a).map (fun v => e ∘ v))
    {C : Type w} (initialA : A → C) (initialB : B → C)
    (hinitial : ∀ a,initialB (e a)=initialA a) (s t : Multiset A) :
    (∀r,(s.map e).map (labels edgesB initialB r)=(t.map e).map (labels edgesB initialB r)) ↔
      ∀r,s.map (labels edgesA initialA r)=t.map (labels edgesA initialA r) := by
  simp only [histogram_transport e edgesA edgesB hedges initialA initialB hinitial]

end GroupWL.CompressedRefinement

