import GroupWL.GadgetRefinement
import GroupWL.StableTuples
import GroupWL.ConcreteVersionI

/-! # Concrete multiplication-graph comparison -/
namespace GroupWL.ConcreteVersionIII

open Refinement InitialIWords GadgetInterpretation GadgetRefinement
universe u v w
variable {G : Type u} {H : Type v} [Group G] [Group H] [Fintype G] [Fintype H]
variable {k d : ℕ}

def pairSlotsOfLE (hkd : k*2+1 ≤ d) : PairSlots k d where
  tuple := (PairSlots.standard k).tuple.trans
    ⟨Fin.castLE hkd,Fin.castLE_injective _⟩
  spare := Fin.castLE hkd (PairSlots.standard k).spare
  outside i h := (PairSlots.standard k).outside i (Fin.castLE_injective hkd h)

private theorem map_univ_congr {A : Type u} {B : Type v} {C : Type w}
    [Fintype A] [Fintype B] (e : A ≃ B) (f : A → C) (g : B → C)
    (h : ∀ a,f a = g (e a)) : Finset.univ.val.map f = Finset.univ.val.map g := by
  calc
    _ = Finset.univ.val.map (g ∘ e) := by congr 1; funext a; exact h a
    _ = (Finset.univ.val.map e).map g := by rw [Multiset.map_map]
    _ = _ := by rw [Multiset.map_univ_val_equiv]

/-- Equality of actual group-restricted graph-color histograms follows from
Version-I equivalence with two coordinates per graph vertex and one spare. -/
theorem graphGroupHistogram_eq_of_equivalentI (hkd : k*2+1 ≤ d)
    (h : EquivalentI d G H) (r : ℕ) :
    graphGroupHistogram (G := G) k r = graphGroupHistogram (G := H) k r := by
  classical
  let s := pairSlotsOfLE hkd
  let slot : Fin k ↪ Fin d := ⟨fun i => s.tuple (i,0),fun i j h =>
    congrArg Prod.fst (s.tuple.injective h)⟩
  obtain ⟨e,he⟩ := Stable.complete_tuples k slot (ConcreteVersionI.sameI_identity_tuple h)
  apply map_univ_congr e
  intro t
  obtain ⟨a,b,hab,hm,_⟩ := he t
  have ha : vertexTuple s (fun _ => none) a = Sum.inl ∘ t := by
    funext i
    exact congrArg Sum.inl (hm i).1
  have hb : vertexTuple s (fun _ => none) b = Sum.inl ∘ (e t) := by
    funext i
    exact congrArg Sum.inl (hm i).2
  rw [← ha,← hb]
  exact graph_color_eq r s (fun _ => none) hab

/-- The concrete Version-I to Version-III comparison, in the joint-vector
refinement convention used for dimensions other than one. -/
theorem equivalentIII_of_equivalentI (hk : k ≠ 1) (hkd : 2*k+1 ≤ d)
    (h : EquivalentI d G H) : EquivalentIII k G H := by
  simp only [EquivalentIII,hk,if_false]
  exact graphGroupHistogram_eq_of_equivalentI (by omega) h

theorem equivalentIII_of_equivalentI_twice (hk : k ≠ 1)
    (h : EquivalentI (2*k+1) G H) : EquivalentIII k G H :=
  equivalentIII_of_equivalentI hk (by omega) h

end GroupWL.ConcreteVersionIII
