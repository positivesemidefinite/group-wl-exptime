import GroupWL.SourceLayout.Images

namespace GroupWL.SourceLayout.ComparisonData

open scoped BigOperators

private theorem translate_image_trans {F : Type*} [AddSemigroup F]
    (a b : F) (S : Set F) :
    (fun z => a + z) '' ((fun z => b + z) '' S) = (fun z => (a + b) + z) '' S := by
  rw [Set.image_image]
  congr 1
  funext z
  exact (add_assoc a b z).symm

/-- Set-valued comparisons telescope just as individual scalar equations do. -/
theorem translated_chain {F : Type*} [AddCommMonoid F] {n : ℕ}
    (S : Fin (n + 1) → Set F) (δ : Fin n → F)
    (h : ∀ i : Fin n, S i.castSucc = (fun z => δ i + z) '' S i.succ) :
    S 0 = (fun z => (∑ i, δ i) + z) '' S (Fin.last n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ht := ih (fun i => S i.succ) (fun i => δ i.succ) (fun i => h i.succ)
    dsimp only at ht
    have h₀ := h (0 : Fin (n + 1))
    change S 0 = (fun z => δ 0 + z) '' S (Fin.succ 0) at h₀
    rw [h₀, ht, translate_image_trans, Fin.sum_univ_succ]
    rfl

variable {F T E : Type*} [Field F] {r L : ℕ}
variable (C : ComparisonData F T E r)

abbrev NodeImages := ∀ t : Node T E L,
  C.NodeAddress t → Set (C.nodeSpace L t)

/-- Restrict image sets at all buffered nodes to the real circuit types. -/
def realImages (Q : C.NodeImages (L := L)) : C.ImageSets :=
  fun t a => Q (.inl t) (fun i => ⟨a i, Finset.mem_univ _⟩)

/-- The private wire transfers the complete scalar image, including the sum
of all link shifts. No selection of a scalar representative is needed. -/
theorem scalarImages_of_link_images (beta : C.Block L → F)
    (Q : C.NodeImages (L := L)) (hQ : ∀ t a, (Q t a).Nonempty)
    (hlink : ∀ (l : Link E L) (a : C.DomainAddress l.comparison),
      C.leftForm L l '' Q (C.leftNode L l) (C.leftAddress l a) =
        (fun z => C.linkDelta beta l a + z) ''
          (C.rightForm L l '' Q (C.rightNode L l) (C.rightAddress l a))) :
    C.ScalarImages beta (C.realImages Q) := by
  refine ⟨fun t a => hQ _ _, ?_⟩
  intro e a
  have hf := hlink (.first e) a
  have hl := hlink (.last e) a
  have hm (i : Fin L) := hlink (.middle e i) a
  change C.sourceForm e '' C.realImages Q (C.source e) (C.sourceAddress a) =
    (fun z => C.linkDelta beta (.first e) a + z) ''
      ((LinearMap.id : F →ₗ[F] F) '' Q (.inr (e, 0)) a) at hf
  change (LinearMap.id : F →ₗ[F] F) '' Q (.inr (e, Fin.last L)) a =
    (fun z => C.linkDelta beta (.last e) a + z) ''
      (C.targetForm e '' C.realImages Q (C.target e) (C.targetAddress a)) at hl
  change ∀ i : Fin L, (LinearMap.id : F →ₗ[F] F) '' Q (.inr (e, i.castSucc)) a =
    (fun z => C.linkDelta beta (.middle e i) a + z) ''
      ((LinearMap.id : F →ₗ[F] F) '' Q (.inr (e, i.succ)) a) at hm
  simp only [LinearMap.id_coe, Set.image_id] at hf hl hm
  have ht := translated_chain (fun i : Fin (L + 1) => Q (.inr (e, i)) a)
    (fun i => C.linkDelta beta (.middle e i) a) hm
  dsimp only at ht
  rw [hf, ht, hl, translate_image_trans, translate_image_trans]
  rfl

end GroupWL.SourceLayout.ComparisonData
