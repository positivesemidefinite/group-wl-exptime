import GroupWL.SourceLayout.WireCuts

namespace GroupWL.SourceLayout.ComparisonData

open scoped BigOperators

variable {F T E : Type*} [Field F] {r L : ℕ}
variable (C : ComparisonData F T E r)

def blockLinks : C.Block L → Finset (Link E L)
  | .inl _ => ∅
  | .inr s => {s.1}

noncomputable def activeLinks (S : Finset (C.Block L)) : Finset (Link E L) := by
  classical
  exact S.biUnion C.blockLinks

theorem card_activeLinks_le (S : Finset (C.Block L)) : (C.activeLinks S).card ≤ S.card := by
  classical
  calc
    (C.activeLinks S).card ≤ ∑ B ∈ S, (C.blockLinks B).card := Finset.card_biUnion_le
    _ ≤ ∑ _B ∈ S, 1 := Finset.sum_le_sum (fun B _ => by cases B <;> simp [blockLinks])
    _ = S.card := by simp

theorem square_link_mem_active {S : Finset (C.Block L)} {s : C.Square L}
    (hs : Sum.inr s ∈ S) : s.1 ∈ C.activeLinks S := by
  classical
  exact Finset.mem_biUnion.mpr ⟨Sum.inr s, hs, by simp [blockLinks]⟩

theorem exists_missing_link (S : Finset (C.Block L)) (hS : S.card < L + 2) (e : E) :
    ∃ i : Fin (L + 2), Link.atPosition e i ∉ C.activeLinks S := by
  classical
  have hcard : (C.activeLinks S).card <
      (Finset.univ.image (Link.atPosition (L := L) e)).card := by
    rw [Finset.card_image_of_injective _ (Link.atPosition_injective e)]
    simpa using lt_of_le_of_lt (C.card_activeLinks_le S) hS
  obtain ⟨l, hl, hn⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hl
  exact ⟨i, hn⟩

/-- A small block collection always leaves an unused link in every private wire. -/
noncomputable def cutsFor (S : Finset (C.Block L)) (hS : S.card < L + 2) : Cuts (E := E) (L := L) :=
  fun e => Classical.choose (C.exists_missing_link S hS e)

theorem cutsFor_missing (S : Finset (C.Block L)) (hS : S.card < L + 2) (e : E) :
    Link.atPosition e (C.cutsFor S hS e) ∉ C.activeLinks S :=
  Classical.choose_spec (C.exists_missing_link S hS e)

theorem active_not_cut (S : Finset (C.Block L)) (hS : S.card < L + 2)
    (l : Link E L) (hl : l ∈ C.activeLinks S) :
    l.position ≠ C.cutsFor S hS l.comparison := by
  intro heq
  apply C.cutsFor_missing S hS l.comparison
  rw [← heq, Link.atPosition_position]
  exact hl

/-- The type-support graph of the actual active links. -/
def typeGraph (S : Finset (C.Block L)) : SimpleGraph (Node T E L) :=
  SimpleGraph.fromRel (fun u v => ∃ l ∈ C.activeLinks S,
    u = C.leftNode L l ∧ v = C.rightNode L l)

theorem roots_equal_of_type_adj (S : Finset (C.Block L)) (hS : S.card < L + 2)
    {u v : Node T E L} (h : (C.typeGraph S).Adj u v) :
    C.root (C.cutsFor S hS) u = C.root (C.cutsFor S hS) v := by
  rcases h.2 with ⟨l, hl, rfl, rfl⟩ | ⟨l, hl, rfl, rfl⟩
  · exact C.root_eq_of_uncut _ l (C.active_not_cut S hS l hl)
  · exact (C.root_eq_of_uncut _ l (C.active_not_cut S hS l hl)).symm

theorem roots_equal_of_type_walk (S : Finset (C.Block L)) (hS : S.card < L + 2)
    {u v : Node T E L} (p : (C.typeGraph S).Walk u v) :
    C.root (C.cutsFor S hS) u = C.root (C.cutsFor S hS) v := by
  induction p with
  | nil => rfl
  | cons h p ih => exact (C.roots_equal_of_type_adj S hS h).trans ih

/-- A small active type component contains at most one real type. -/
theorem real_eq_of_type_reachable (S : Finset (C.Block L)) (hS : S.card < L + 2)
    {t u : T} (h : (C.typeGraph S).Reachable (Sum.inl t) (Sum.inl u)) : t = u := by
  obtain ⟨p⟩ := h
  exact C.roots_equal_of_type_walk S hS p

end GroupWL.SourceLayout.ComparisonData
