import GroupWL.RefinementGame

/-! # Retained histories of pure frame queries

Histories record actual announced bijections, selected pure queries, and
removals. Their endpoints remain winning and preserve the anchors anchors.
-/

set_option linter.unusedSectionVars false

namespace GroupWL.FrameHistory

open PebbleGame
variable {G H α : Type*} [Group G] [Group H] {m : ℕ}

/-- Winning strategies remain winning after any partial deletion of marks. -/
theorem winning_restricts {p q : Position m G H} (hp : Winning p) (hqp : Restricts q p) :
    Winning q := by
  refine ⟨fun r => ∃ s, Winning s ∧ Restricts r s, ⟨p,hp,hqp⟩,?_⟩
  rintro r ⟨s,hs,hrs⟩ i
  obtain ⟨ha,f,hf⟩ := winning_step hs i
  refine ⟨ha.restricts ?_,f,fun g => ⟨place s i g (f g),hf g,?_⟩⟩
  · intro j g h hj
    by_cases hji : j = i
    · subst j; simp at hj
    · rw [erase_ne _ _ _ hji] at hj ⊢
      exact hrs j g h hj
  · intro j g' h' hj
    by_cases hji : j = i
    · subst j; simpa using hj
    · rw [place_ne _ _ _ _ _ hji] at hj ⊢
      exact hrs j g' h' hj

/-- A finite continuation using pure queries and removals outside the anchor
slots. Each announcement witnesses a legal winning continuation for all picks. -/
inductive History (anchors : Finset (Fin m)) (query : α → G)
    (initial : Position m G H) : Position m G H → Prop
  | start (hp : Winning initial) : History anchors query initial initial
  | remove {p} (h : History anchors query initial p) (i : Fin m)
      (hi : i ∉ anchors) : History anchors query initial (erase p i)
  | select {p} (h : History anchors query initial p) (i : Fin m)
      (hi : i ∉ anchors) (f : G ≃ H)
      (hf : ∀ g, Winning (place p i g (f g))) (a : α) :
      History anchors query initial (place p i (query a) (f (query a)))

namespace History

variable {anchors : Finset (Fin m)} {query : α → G} {initial p : Position m G H}

theorem winning (h : History anchors query initial p) : Winning p := by
  induction h with
  | start hp => exact hp
  | remove h i hi ih => exact winning_restricts ih (erase_restricts _ _)
  | select h i hi f hf a ih => exact hf _

theorem anchors_preserved (h : History anchors query initial p) :
    ∀ i ∈ anchors, p i = initial i := by
  induction h with
  | start hp => intros; rfl
  | remove h j hj ih =>
      intro i hi
      rw [erase_ne _ _ _ (by intro hij; exact hj (hij ▸ hi))]
      exact ih i hi
  | select h j hj f hf a ih =>
      intro i hi
      rw [place_ne _ _ _ _ _ (by intro hij; exact hj (hij ▸ hi))]
      exact ih i hi

/-- Every pure query can be selected in an unanchors slot. -/
theorem query_exists (h : History anchors query initial p) (i : Fin m)
    (hi : i ∉ anchors) (a : α) :
    ∃ b : H, History anchors query initial (place p i (query a) b) := by
  obtain ⟨_,f,hf⟩ := winning_step h.winning i
  exact ⟨f (query a), h.select i hi f hf a⟩

/-- Sequentially query a whole frame in distinct slots, preserving every
mark outside those slots. No linearity of any announcement is used. -/
theorem query_frame (h : History anchors query initial p)
    (n : ℕ) (slot : Fin n ↪ Fin m) (hslot : ∀ i, slot i ∉ anchors)
    (a : Fin n → α) :
    ∃ (p' : Position m G H) (b : Fin n → H),
      History anchors query initial p' ∧
      (∀ i, p' (slot i) = some (query (a i), b i)) ∧
      (∀ j, (∀ i, slot i ≠ j) → p' j = p j) := by
  classical
  induction n generalizing p with
  | zero =>
      exact ⟨p, (fun i => Fin.elim0 i), h, (fun i => Fin.elim0 i), fun _ _ => rfl⟩
  | succ n ih =>
      obtain ⟨b0,h0⟩ := h.query_exists (slot 0) (hslot 0) (a 0)
      let tailSlot : Fin n ↪ Fin m :=
        ⟨fun i => slot i.succ, fun i j hij => Fin.succ_injective n (slot.injective hij)⟩
      obtain ⟨p',b',hh,hb,houtside⟩ := ih h0 tailSlot (fun i => hslot i.succ) (Fin.tail a)
      refine ⟨p',Fin.cons b0 b',hh,?_,?_⟩
      · intro i
        refine Fin.cases ?_ (fun i => ?_) i
        · rw [houtside (slot 0) (by
            intro i hi
            exact Fin.succ_ne_zero i (slot.injective hi))]
          simp
        · exact hb i
      · intro j hj
        rw [houtside j (fun i => hj i.succ)]
        exact place_ne _ _ _ _ _ (hj 0).symm

/-- The same acquisition theorem for an arbitrary finite family of queries. -/
theorem query_finite (h : History anchors query initial p)
    {η : Type*} [Fintype η] (slot : η ↪ Fin m) (hslot : ∀ i, slot i ∉ anchors)
    (a : η → α) :
    ∃ (p' : Position m G H) (b : η → H), History anchors query initial p' ∧
      (∀ i, p' (slot i) = some (query (a i),b i)) ∧
      (∀ j, (∀ i, slot i ≠ j) → p' j = p j) := by
  classical
  let e := Fintype.equivFin η
  obtain ⟨p',b,hh,hb,ho⟩ := h.query_frame (Fintype.card η)
    (e.symm.toEmbedding.trans slot) (fun i => hslot (e.symm i)) (fun i => a (e.symm i))
  refine ⟨p',fun i => b (e i),hh,?_,?_⟩
  · intro i
    simpa using hb (e i)
  · intro j hj
    exact ho j (fun i => hj (e.symm i))

end History

/-- Retain precisely a chosen set of slots. -/
def keep (p : Position m G H) (s : Finset (Fin m)) : Position m G H :=
  fun i => if i ∈ s then p i else none

@[simp] theorem keep_univ (p : Position m G H) : keep p Finset.univ = p := by
  funext i
  simp [keep]

@[simp] theorem keep_mem (p : Position m G H) {s : Finset (Fin m)} {i : Fin m}
    (hi : i ∈ s) : keep p s i = p i := by simp [keep,hi]

@[simp] theorem keep_not_mem (p : Position m G H) {s : Finset (Fin m)} {i : Fin m}
    (hi : i ∉ s) : keep p s i = none := by simp [keep,hi]

theorem keep_restricts (p : Position m G H) (s : Finset (Fin m)) : Restricts (keep p s) p := by
  intro i g h hi
  by_cases hs : i ∈ s
  · simpa [keep,hs] using hi
  · simp [keep,hs] at hi

/-- Removing a finite set is literally a finite sequence of allowed removals. -/
theorem History.remove_set {anchors : Finset (Fin m)} {query : α → G}
    {initial p : Position m G H} (h : History anchors query initial p)
    (s : Finset (Fin m)) (hs : Disjoint s anchors) :
    History anchors query initial (keep p (Finset.univ \ s)) := by
  classical
  induction s using Finset.induction_on generalizing p with
  | empty => simpa [keep] using h
  | @insert i s his ih =>
      have hi : i ∉ anchors := fun hp => Finset.disjoint_left.mp hs (by simp) hp
      have hs' : Disjoint s anchors := Finset.disjoint_left.mpr
        (fun j hj hp => Finset.disjoint_left.mp hs (by simp [hj]) hp)
      have hh := ih (h.remove i hi) hs'
      have heq : keep (erase p i) (Finset.univ \ s) = keep p (Finset.univ \ insert i s) := by
        funext j
        by_cases hji : j = i
        · subst j; simp [keep]
        · simp [keep,erase,hji]
      rwa [heq] at hh

/-- Any restriction preserving the anchors is an actual pure-query history. -/
theorem History.keep {anchors : Finset (Fin m)} {query : α → G}
    {initial p : Position m G H} (h : History anchors query initial p)
    (s : Finset (Fin m)) (hs : anchors ⊆ s) :
    History anchors query initial (keep p s) := by
  have hh := h.remove_set (Finset.univ \ s) (by
    apply Finset.disjoint_left.mpr
    intro i hi hp
    exact (Finset.mem_sdiff.mp hi).2 (hs hp))
  simpa using hh

/-- Finite slot support of one frame. -/
def frameSlots {n : ℕ} (slot : Fin n → Fin m) : Finset (Fin m) :=
  Finset.univ.image slot

@[simp] theorem mem_frameSlots {n : ℕ} (slot : Fin n → Fin m) (j : Fin m) :
    j ∈ frameSlots slot ↔ ∃ i, slot i = j := by simp [frameSlots]

/-- Place the replacement before removing the old frame. The intermediate
history contains both endpoint frames, permitting the actual commutation test. -/
theorem History.replace_frame {anchors : Finset (Fin m)} {query : α → G}
    {initial p : Position m G H} (h : History anchors query initial p)
    {n : ℕ} (old : Fin n → Fin m) (fresh : Fin n ↪ Fin m)
    (hold : ∀ i, old i ∉ anchors) (hfresh : ∀ i, fresh i ∉ anchors)
    (hdis : ∀ i j, fresh i ≠ old j) (a : Fin n → α) :
    ∃ (t p' : Position m G H) (b : Fin n → H),
      History anchors query initial t ∧ History anchors query initial p' ∧
      (∀ i, t (fresh i) = some (query (a i), b i)) ∧
      (∀ i, t (old i) = p (old i)) ∧
      (∀ i, p' (fresh i) = some (query (a i), b i)) ∧
      (∀ i, p' (old i) = none) ∧
      (∀ j, (∀ i, fresh i ≠ j) → (∀ i, old i ≠ j) → p' j = p j) := by
  classical
  obtain ⟨t,b,ht,hb,houtside⟩ := h.query_frame n fresh hfresh a
  let p' := FrameHistory.keep t (Finset.univ \ frameSlots old)
  have hp' : History anchors query initial p' := ht.remove_set (frameSlots old) (by
    apply Finset.disjoint_left.mpr
    rintro j hj hja
    obtain ⟨i,rfl⟩ := (mem_frameSlots old j).mp hj
    exact hold i hja)
  refine ⟨t,p',b,ht,hp',hb,?_,?_,?_,?_⟩
  · intro i
    exact houtside (old i) (fun j => hdis j i)
  · intro i
    dsimp only [p']
    rw [keep_mem t (by
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, mem_frameSlots]
      rintro ⟨j,hj⟩
      exact hdis i j hj.symm)]
    exact hb i
  · intro i
    simp [p',frameSlots]
  · intro j hjfresh hjold
    dsimp only [p']
    rw [keep_mem t (by
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, mem_frameSlots]
      exact not_exists.mpr hjold)]
    exact houtside j hjfresh

/-- Histories concatenate without losing the fixed anchor identities. -/
theorem History.trans {anchors : Finset (Fin m)} {query : α → G}
    {initial p t : Position m G H} (h : History anchors query initial p)
    (ht : History anchors query p t) : History anchors query initial t := by
  induction ht with
  | start _ => exact h
  | remove ht i hi ih => exact ih.remove i hi
  | select ht i hi f hf a ih => exact ih.select i hi f hf a

end GroupWL.FrameHistory
