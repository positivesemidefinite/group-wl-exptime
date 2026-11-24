import GroupWL.PackedGraph

/-! # The concrete half-dimension Version-III to Version-II comparison -/
namespace GroupWL.GraphToGroup

open Refinement InitialIWords GadgetDecoding GadgetWords PackedGraph
universe u v
variable {G : Type u} {H : Type v} [Group G] [Group H] [Fintype G] [Fintype H]
variable {k d : ℕ}

/-- Consecutive pairs share a graph slot; two final slots are helpers. -/
def packingOfLE (hkd : (k+1)/2+2 ≤ d) : Packing k d where
  input :=
    { toFun := fun i => (⟨i.val/2,by omega⟩,⟨i.val%2,by omega⟩)
      inj' := by
        intro i j he
        have hdiv := congrArg (fun p : Fin d × Fin 2 => p.1.val) he
        have hmod := congrArg (fun p : Fin d × Fin 2 => p.2.val) he
        apply Fin.ext
        change i.val/2=j.val/2 at hdiv
        change i.val%2=j.val%2 at hmod
        omega }
  helpers :=
    { toFun := fun j => ⟨(k+1)/2+j.val,by omega⟩
      inj' := by
        intro i j he
        apply Fin.ext
        have hh := congrArg Fin.val he
        change (k+1)/2+i.val=(k+1)/2+j.val at hh
        omega }
  outside i j he := by
    have hh := congrArg Fin.val he
    change i.val/2=(k+1)/2+j.val at hh
    have := i.isLt
    omega

theorem card_eq_of_graph_histograms (hd : d ≠ 0)
    (h : ∀ r,graphGroupHistogram (G := G) d r = graphGroupHistogram (G := H) d r) :
    Fintype.card G=Fintype.card H := by
  have he := congrArg Multiset.card (h 0)
  simp only [graphGroupHistogram,Multiset.card_map] at he
  change Fintype.card (Fin d → G)=Fintype.card (Fin d → H) at he
  simp only [Fintype.card_fun,Fintype.card_fin] at he
  exact Nat.pow_left_injective hd he

/-- A single stable group-only graph tuple match follows from the actual
restricted graph histograms, by finiteness of the set of candidate tuples. -/
theorem exists_stable_group_tuple
    (h : ∀ r,graphGroupHistogram (G := G) d r = graphGroupHistogram (G := H) d r) :
    ∃ b : Fin d → H,SameGraph (fun _ => .inl (1:G)) (Sum.inl ∘ b) := by
  classical
  have hr (r : ℕ) : ∃ b : Fin d → GadgetVertex H,
      (∃ t : Fin d → H,b=Sum.inl ∘ t) ∧
      color (graphInitial gadgetAdj d) r (fun _ => Sum.inl (1:G)) =
        color (graphInitial gadgetAdj d) r b := by
    have hm : color (graphInitial gadgetAdj d) r (fun _ => Sum.inl (1:G)) ∈
        graphGroupHistogram (G := G) d r :=
      Multiset.mem_map.mpr ⟨fun _ => 1,Finset.mem_univ _,rfl⟩
    rw [h r] at hm
    obtain ⟨t,_,ht⟩ := Multiset.mem_map.mp hm
    exact ⟨Sum.inl ∘ t,⟨t,rfl⟩,ht.symm⟩
  obtain ⟨b,⟨t,rfl⟩,hs⟩ := exists_stable_of_forall_exists (fun _ => Sum.inl (1:G))
    (fun b => ∃ t : Fin d → H,b=Sum.inl ∘ t) hr
  exact ⟨t,hs⟩

/-- Packed recursive colors establish the comparison for nontrivial groups. -/
theorem equivalentII_of_graph_histograms_nontrivial [Nontrivial G] [Nontrivial H]
    (hd : 3 ≤ d) (hkd : (k+1)/2+2 ≤ d)
    (h : ∀ r,graphGroupHistogram (G := G) d r = graphGroupHistogram (G := H) d r) :
    EquivalentII k G H := by
  obtain ⟨b,hb⟩ := exists_stable_group_tuple h
  let s := packingOfLE hkd
  have hs : Stable (initialII k) (initialII k)
      (tuple s (fun _ => Sum.inl (1:G))) (tuple s (Sum.inl ∘ b)) :=
    fun r => PackedGraph.color_eq hd r s hb (fun _ => usable_group _) (fun _ => usable_group _)
  exact hs.equivalent

/-- The concrete comparison in the manuscript: `ceil(k/2)+2` graph dimensions
suffice for the `k`-dimensional generated-subgroup colors. -/
theorem equivalentII_of_equivalentIII (hk : 0 < k) (hkd : (k+1)/2+2 ≤ d)
    (h : EquivalentIII d G H) : EquivalentII k G H := by
  have hd : 3 ≤ d := by omega
  have hg : ∀ r,graphGroupHistogram (G := G) d r = graphGroupHistogram (G := H) d r := by
    simpa only [EquivalentIII,show d ≠ 1 by omega,if_false] using h
  have hc := card_eq_of_graph_histograms (by omega : d ≠ 0) hg
  by_cases hG : Nontrivial G
  · letI := hG
    have hH : Nontrivial H := Fintype.one_lt_card_iff_nontrivial.mp
      (by rw [← hc]; exact Fintype.one_lt_card)
    letI := hH
    exact equivalentII_of_graph_histograms_nontrivial hd hkd hg
  · have hGs : Subsingleton G := not_nontrivial_iff_subsingleton.mp hG
    letI := hGs
    have hHs : Subsingleton H := Fintype.card_le_one_iff_subsingleton.mp
      (by rw [← hc]; exact Fintype.card_le_one_iff_subsingleton.mpr hGs)
    letI := hHs
    letI : Unique G := ⟨⟨1⟩,fun _ => Subsingleton.elim _ _⟩
    letI : Unique H := ⟨⟨1⟩,fun _ => Subsingleton.elim _ _⟩
    exact equivalentII_of_isomorphic (MulEquiv.ofUnique : G ≃* H) k

theorem equivalentII_of_equivalentIII_half (hk : 0 < k)
    (h : EquivalentIII ((k+1)/2+2) G H) : EquivalentII k G H :=
  equivalentII_of_equivalentIII hk (by omega) h

end GroupWL.GraphToGroup
