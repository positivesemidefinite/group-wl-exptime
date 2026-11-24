import GroupWL.GadgetWords

/-! # Bijections on group vertices and replacement of packed coordinates -/
namespace GroupWL.GadgetMatching

open Refinement InitialIWords GadgetDecoding GadgetRelations GadgetWords
universe u v
variable {G : Type u} {H : Type v} [Group G] [Group H]
variable [Fintype G] [Fintype H] [Nontrivial G] [Nontrivial H] {d : ℕ}

theorem sort_four_iff (v : GadgetVertex G) : vertexSort v=4 ↔ ∃ g,v=.inl g := by
  cases v with
  | inl g => simp [vertexSort]
  | inr v =>
      rcases v with ⟨g,h,j⟩
      fin_cases j <;> simp [vertexSort]

/-- Replacement bijections restrict to genuine group bijections because the
uncolored graph colors recognize the group sort. -/
theorem group_matching {a : Fin d → GadgetVertex G} {b : Fin d → GadgetVertex H}
    (h : SameGraph a b) (i j : Fin d) (hij : i ≠ j) :
    ∃ f : G ≃ H, ∀ x,SameGraph (Function.update a i (.inl x))
      (Function.update b i (.inl (f x))) := by
  classical
  obtain ⟨F,hF⟩ := h.matching
  have hs (v : GadgetVertex G) : vertexSort v = vertexSort (F v) := by
    simpa only [Function.update_self] using SameGraph.sort_eq (hF v i) i j hij
  have hg (x : G) : ∃ y : H,F (.inl x)=.inl y :=
    (sort_four_iff _).mp (by simpa only [vertexSort] using (hs (.inl x)).symm)
  choose f hf using hg
  have hinj : Function.Injective f := by
    intro x y he
    apply Sum.inl.inj
    apply F.injective
    rw [hf,hf,he]
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨v,hv⟩ := F.surjective (.inl y)
    have hv4 : vertexSort v=4 := by rw [hs v,hv]; rfl
    obtain ⟨x,rfl⟩ := (sort_four_iff v).mp hv4
    exact ⟨x,Sum.inl.inj ((hf x).symm.trans hv)⟩
  refine ⟨Equiv.ofBijective f ⟨hinj,hsurj⟩,fun x => ?_⟩
  simpa only [Equiv.ofBijective_apply,hf] using hF (.inl x) i

/-- Replace one of the two inputs represented by a gadget vertex. -/
def newPair (role : Fin 2) (x : G) (old : GadgetVertex G) : GadgetVertex G :=
  if role=0 then .inr (x,coord 1 old,1) else .inr (coord 0 old,x,1)

@[simp] theorem newPair_sort (role : Fin 2) (x : G) (old : GadgetVertex G) :
    vertexSort (newPair role x old)=1 := by
  unfold newPair
  split_ifs <;> rfl

@[simp] theorem newPair_usable (role : Fin 2) (x : G) (old : GadgetVertex G) :
    Usable (newPair role x old) := Or.inr (newPair_sort _ _ _)

/-- Stable colors force the image of a new gadget from its two retained
implicit endpoint equalities. -/
theorem repack (hd : 3 ≤ d) {a : Fin d → GadgetVertex G} {b : Fin d → GadgetVertex H}
    (h : SameGraph a b) (old fresh value : Fin d)
    (hof : old ≠ fresh) (hvf : value ≠ fresh)
    (role : Fin 2) (x : G) (y : H)
    (hx : a value=.inl x) (hy : b value=.inl y)
    (ha : Usable (a old)) (hb : Usable (b old)) :
    SameGraph (Function.update a fresh (newPair role x (a old)))
      (Function.update b fresh (newPair role y (b old))) := by
  obtain ⟨F,hF⟩ := h.matching
  let v := newPair role x (a old)
  have hh := hF v fresh
  have hs : vertexSort (F v)=1 := by
    have hs := SameGraph.sort_eq hh fresh value hvf.symm
    simpa only [Function.update_self,v,newPair_sort] using hs.symm
  obtain ⟨g,t,hgt⟩ := (sort_one_iff _).mp hs
  have huf : Usable (F v) := Or.inr hs
  have hnew (r : Fin 3) :
      coord r v = x ↔ coord r (F v) = y := by
    have he := coord_eq_iff hd hh fresh value r 0
      (by simpa only [Function.update_self] using newPair_usable role x (a old))
      (by simpa only [Function.update_of_ne hvf,hx] using usable_group x)
      (by simpa using huf)
      (by simpa only [Function.update_of_ne hvf,hy] using usable_group y)
    simpa only [Function.update_self,Function.update_of_ne hvf,hx,hy,coord_group] using he
  have hold (r : Fin 3) :
      coord r v = coord r (a old) ↔ coord r (F v) = coord r (b old) := by
    have he := coord_eq_iff hd hh fresh old r r
      (by simpa only [Function.update_self] using newPair_usable role x (a old))
      (by simpa only [Function.update_of_ne hof] using ha)
      (by simpa using huf)
      (by simpa only [Function.update_of_ne hof] using hb)
    simpa only [Function.update_self,Function.update_of_ne hof] using he
  have he : F v = newPair role y (b old) := by
    fin_cases role
    · have hg : coord 0 (F v)=y := (hnew 0).mp (by simp [v,newPair])
      have ht : coord 1 (F v)=coord 1 (b old) := (hold 1).mp (by simp [v,newPair])
      rw [hgt] at hg ht ⊢
      simp only [coord_pair_zero,coord_pair_one] at hg ht
      simp [newPair,hg,ht]
    · have hg : coord 0 (F v)=coord 0 (b old) := (hold 0).mp (by simp [v,newPair])
      have ht : coord 1 (F v)=y := (hnew 1).mp (by simp [v,newPair])
      rw [hgt] at hg ht ⊢
      simp only [coord_pair_zero,coord_pair_one] at hg ht
      simp [newPair,hg,ht]
  simpa only [he] using hh

end GroupWL.GadgetMatching
