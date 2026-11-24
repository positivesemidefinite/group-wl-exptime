import GroupWL.GadgetInterpretation

/-! # Simulating one graph-refinement step with group-coordinate replacements -/
namespace GroupWL.GadgetRefinement

open Refinement InitialIWords GadgetInterpretation

universe u v w
variable {G : Type u} {H : Type v} [Group G] [Group H] {k d : ℕ}

private theorem pair_ne (s : PairSlots k d) (i : Fin k) : s.tuple (i,0) ≠ s.tuple (i,1) := by
  intro h
  have hh := congrArg Prod.snd (s.tuple.injective h)
  norm_num at hh

private theorem pair_other_ne (s : PairSlots k d) {i j : Fin k} (hji : j ≠ i)
    (a b : Fin 2) : s.tuple (j,a) ≠ s.tuple (i,b) := by
  intro h
  exact hji (congrArg Prod.fst (s.tuple.injective h))

/-- Cycle the first slot, second slot and spare of one represented vertex. -/
def rotation (s : PairSlots k d) (i : Fin k) : Fin d ≃ Fin d :=
  (Equiv.swap s.spare (s.tuple (i,0))).trans (Equiv.swap (s.tuple (i,0)) (s.tuple (i,1)))

@[simp] theorem rotation_left (s : PairSlots k d) (i : Fin k) :
    rotation s i (s.tuple (i,0)) = s.spare := by
  simp [rotation,Equiv.trans_apply,Equiv.swap_apply_of_ne_of_ne,
    (s.outside (i,0)).symm,(s.outside (i,1)).symm]

@[simp] theorem rotation_right (s : PairSlots k d) (i : Fin k) :
    rotation s i (s.tuple (i,1)) = s.tuple (i,0) := by
  simp [rotation,Equiv.trans_apply,Equiv.swap_apply_of_ne_of_ne,s.outside,pair_ne,
    (pair_ne s i).symm]

@[simp] theorem rotation_spare (s : PairSlots k d) (i : Fin k) :
    rotation s i s.spare = s.tuple (i,1) := by simp [rotation,Equiv.trans_apply]

theorem rotation_other (s : PairSlots k d) {i j : Fin k} (hji : j ≠ i) (a : Fin 2) :
    rotation s i (s.tuple (j,a)) = s.tuple (j,a) := by
  simp [rotation,Equiv.trans_apply,Equiv.swap_apply_of_ne_of_ne,s.outside,
    pair_other_ne s hji a 0,pair_other_ne s hji a 1]

def replacedSlots (s : PairSlots k d) (i : Fin k) : PairSlots k d where
  tuple := s.tuple.trans (rotation s i).toEmbedding
  spare := s.tuple (i,1)
  outside j := by
    intro h
    have hs : rotation s i (s.tuple j) = rotation s i s.spare := by simpa using h
    exact s.outside j ((rotation s i).injective hs)

@[simp] theorem replacedSlots_left (s : PairSlots k d) (i : Fin k) :
    (replacedSlots s i).tuple (i,0) = s.spare := rotation_left s i
@[simp] theorem replacedSlots_right (s : PairSlots k d) (i : Fin k) :
    (replacedSlots s i).tuple (i,1) = s.tuple (i,0) := rotation_right s i

theorem replacedSlots_other (s : PairSlots k d) {i j : Fin k} (hji : j ≠ i) (a : Fin 2) :
    (replacedSlots s i).tuple (j,a) = s.tuple (j,a) := rotation_other s hji a

def afterPair (s : PairSlots k d) (i : Fin k) (a : Fin d → G) (x y : G) : Fin d → G :=
  Function.update (Function.update a s.spare x) (s.tuple (i,0)) y

/-- The two coordinate replacements realize exactly one graph-vertex replacement. -/
theorem vertexTuple_afterPair (s : PairSlots k d) (tags : Fin k → Option (Fin 4))
    (i : Fin k) (tag : Option (Fin 4)) (a : Fin d → G) (x y : G) :
    vertexTuple (replacedSlots s i) (Function.update tags i tag) (afterPair s i a x y) =
      Function.update (vertexTuple s tags a) i (decode tag x y) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [vertexTuple,afterPair,Function.update, (s.outside (i,0)).symm]
  · simp [vertexTuple,afterPair,Function.update,hji,replacedSlots_other s hji,
      s.outside,pair_other_ne s hji 0 0,pair_other_ne s hji 1 0]

private theorem map_univ_congr {A : Type u} {B : Type v} {C : Type w}
    [Fintype A] [Fintype B] (e : A ≃ B) (f : A → C) (g : B → C)
    (h : ∀ a, f a = g (e a)) :
    Finset.univ.val.map f = Finset.univ.val.map g := by
  calc
    _ = Finset.univ.val.map (g ∘ e) := by congr 1; funext a; exact h a
    _ = (Finset.univ.val.map e).map g := by rw [Multiset.map_map]
    _ = _ := by rw [Multiset.map_univ_val_equiv]

/-- Actual shared graph colors are preserved, at every round, by stable
Version-I colors of the two-coordinate representation. -/
theorem graph_color_eq [Fintype G] [Fintype H] (r : ℕ)
    (s : PairSlots k d) (tags : Fin k → Option (Fin 4))
    {a : Fin d → G} {b : Fin d → H} (h : SameI a b) :
    color (graphInitial (gadgetAdj (G := G)) k) r (vertexTuple s tags a) =
      color (graphInitial (gadgetAdj (G := H)) k) r (vertexTuple s tags b) := by
  classical
  induction r generalizing s tags a b with
  | zero => exact graphInitial_eq s tags (h 0)
  | succ r ih =>
      apply Prod.ext
      · exact ih s tags h
      · obtain ⟨f,hf⟩ := Stable.matching h
        have hnext : ∀ x : G, ∃ next : G ≃ H, ∀ y j,
            Stable (initialI d) (initialI d)
              (Function.update (Function.update a s.spare x) j y)
              (Function.update (Function.update b s.spare (f x)) j (next y)) :=
          fun x => Stable.matching (hf x s.spare)
        choose next hn using hnext
        apply map_univ_congr (gadgetEquiv f next)
        intro v
        funext i
        cases v with
        | inl x =>
            have hc := ih (replacedSlots s i) (Function.update tags i none)
              (hn x 1 (s.tuple (i,0)))
            change color _ r (vertexTuple (replacedSlots s i) (Function.update tags i none)
                (afterPair s i a x 1)) =
              color _ r (vertexTuple (replacedSlots s i) (Function.update tags i none)
                (afterPair s i b (f x) (next x 1))) at hc
            simpa only [vertexTuple_afterPair,decode,gadgetEquiv_inl] using hc
        | inr v =>
            rcases v with ⟨x,y,j⟩
            have hc := ih (replacedSlots s i) (Function.update tags i (some j))
              (hn x y (s.tuple (i,0)))
            change color _ r (vertexTuple (replacedSlots s i) (Function.update tags i (some j))
                (afterPair s i a x y)) =
              color _ r (vertexTuple (replacedSlots s i) (Function.update tags i (some j))
                (afterPair s i b (f x) (next x y))) at hc
            simpa only [vertexTuple_afterPair,decode,gadgetEquiv_inr] using hc

end GroupWL.GadgetRefinement
