import GroupWL.FrameHistory

/-! # Replacing an entire ring with one additional frame

The extra row of slots is reused: each new frame is queried before its old
frame is removed, then the released old slots become the next spare row.
-/
set_option linter.unusedSectionVars false

namespace GroupWL.FrameExchange

open PebbleGame FrameHistory
variable {G H α : Type*} [Group G] [Group H] {m n q : ℕ}

abbrev Packing (n q m : ℕ) := (Option (Fin n) × Fin q) ↪ Fin m

/-- The manuscript's frame budget provides an actual packing outside all anchors. -/
theorem packing_exists (anchors : Finset (Fin m)) (hm : q*(n+1) + anchors.card ≤ m) :
    ∃ s : Packing n q m, ∀ k, s k ∉ anchors := by
  classical
  have hc : Fintype.card (Option (Fin n) × Fin q) ≤ (Finset.univ \ anchors).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp only [Fintype.card_prod, Fintype.card_option, Fintype.card_fin, Finset.card_univ]
    rw [Nat.mul_comm (n+1) q]
    omega
  obtain ⟨s,hs⟩ := Function.Embedding.exists_of_card_le_finset hc
  exact ⟨s,fun k => (Finset.mem_sdiff.mp (hs ⟨k,rfl⟩)).2⟩

def Packing.row (s : Packing n q m) (i : Option (Fin n)) : Fin q ↪ Fin m :=
  ⟨fun a => s (i,a), fun _ _ h => (Prod.mk.inj (s.injective h)).2⟩

def Packing.swap (s : Packing n q m) (i : Fin n) : Packing n q m :=
  ((Equiv.prodCongr (Equiv.swap none (some i)) (Equiv.refl (Fin q))).toEmbedding).trans s

@[simp] theorem Packing.swap_none (s : Packing n q m) (i : Fin n) (a : Fin q) :
    s.swap i (none,a) = s (some i,a) := by simp [Packing.swap]

@[simp] theorem Packing.swap_same (s : Packing n q m) (i : Fin n) (a : Fin q) :
    s.swap i (some i,a) = s (none,a) := by simp [Packing.swap]

@[simp] theorem Packing.swap_other (s : Packing n q m) (i j : Fin n) (hji : j ≠ i)
    (a : Fin q) : s.swap i (some j,a) = s (some j,a) := by
  simp [Packing.swap,Equiv.swap_apply_def,hji]

def Tracks (query : α → G) (p : Position m G H) (s : Packing n q m)
    (labels : Fin n → Fin q → α) (answers : Fin n → Fin q → H) : Prop :=
  ∀ i a, p (s (some i,a)) = some (query (labels i a), answers i a)

/-- One replacement preserves every other retained frame and makes the old
slots the new spare row. -/
theorem replace_one {anchors : Finset (Fin m)} {query : α → G}
    {initial p : Position m G H} (hp : History anchors query initial p)
    (s : Packing n q m) (hs : ∀ k, s k ∉ anchors)
    (labels : Fin n → Fin q → α) (answers : Fin n → Fin q → H)
    (ht : Tracks query p s labels answers) (i : Fin n) (new : Fin q → α) :
    ∃ (t p' : Position m G H) (b : Fin q → H),
      History anchors query initial t ∧ History anchors query initial p' ∧
      (∀ a, t (s (some i,a)) = some (query (labels i a), answers i a)) ∧
      (∀ a, t (s (none,a)) = some (query (new a),b a)) ∧
      Tracks query p' (s.swap i) (Function.update labels i new) (Function.update answers i b) := by
  classical
  obtain ⟨t,p',b,htt,hpp,hnew,hold,hnew',hclear,houtside⟩ :=
    hp.replace_frame (fun a => s (some i,a)) (s.row none)
      (fun a => hs (some i,a)) (fun a => hs (none,a))
      (fun a b hab => by
        have he : (none : Option (Fin n)) = some i := congrArg Prod.fst (s.injective hab)
        cases he) new
  refine ⟨t,p',b,htt,hpp,?_,hnew,?_⟩
  · intro a
    rw [hold a]
    exact ht i a
  · intro j a
    by_cases hji : j = i
    · subst j
      simpa using hnew' a
    · simp only [Packing.swap_other s i j hji, Function.update_of_ne hji]
      rw [houtside (s (some j,a)) ?_ ?_]
      · exact ht j a
      · intro b hab
        have he : (none : Option (Fin n)) = some j := congrArg Prod.fst (s.injective hab)
        cases he
      · intro b hab
        exact hji (Option.some.inj (Prod.mk.inj (s.injective hab)).1).symm

/-- The physical relation observed during each coexistence is preserved in a
complete ring replacement. This is a finite sequence of genuine winning
histories using only the packed rows, with exactly one extra frame. -/
theorem exchange_all {anchors : Finset (Fin m)} {query : α → G}
    {initial p : Position m G H} (hp : History anchors query initial p)
    (s : Packing n q m) (hs : ∀ k, s k ∉ anchors)
    (src dst : Fin n → Fin q → α) (answers : Fin n → Fin q → H)
    (ht : Tracks query p s src answers)
    (R : Fin n → (Fin q → H) → (Fin q → H) → Prop)
    (test : ∀ (i : Fin n) (t : Position m G H), History anchors query initial t →
      ∀ (old fresh : Fin q → Fin m) (a b : Fin q → H),
        (∀ k, t (old k) = some (query (src i k),a k)) →
        (∀ k, t (fresh k) = some (query (dst i k),b k)) → R i a b) :
    ∃ (p' : Position m G H) (s' : Packing n q m) (b : Fin n → Fin q → H),
      History anchors query initial p' ∧ (∀ k, s' k ∉ anchors) ∧
      Tracks query p' s' dst b ∧ ∀ i, R i (answers i) (b i) := by
  classical
  have aux : ∀ d : Finset (Fin n),
      ∃ (p' : Position m G H) (s' : Packing n q m) (b : Fin n → Fin q → H),
        History anchors query initial p' ∧ (∀ k, s' k ∉ anchors) ∧
        Tracks query p' s' (fun i => if i ∈ d then dst i else src i) b ∧
        (∀ i ∈ d, R i (answers i) (b i)) ∧ (∀ i ∉ d, b i = answers i) := by
    intro d
    induction d using Finset.induction_on with
    | empty =>
        exact ⟨p,s,answers,hp,hs,by simpa using ht,by simp,by simp⟩
    | @insert i d hid ih =>
        obtain ⟨p',s',b,hp',hs',ht',hr,hb⟩ := ih
        obtain ⟨t,p'',bi,htt,hpp,hold,hnew,htracks⟩ :=
          replace_one hp' s' hs' (fun j => if j ∈ d then dst j else src j) b ht' i (dst i)
        have hrel : R i (answers i) bi := by
          apply test i t htt (fun a => s' (some i,a)) (fun a => s' (none,a)) (answers i) bi
          · intro a
            simpa [hid,hb i hid] using hold a
          · exact hnew
        refine ⟨p'',s'.swap i,Function.update b i bi,hpp,?_,?_,?_,?_⟩
        · intro k
          exact hs' ((Equiv.prodCongr (Equiv.swap none (some i)) (Equiv.refl (Fin q))) k)
        · convert htracks using 1
          funext j
          by_cases hji : j = i
          · subst j; simp
          · simp [hji]
        · intro j hj
          by_cases hji : j = i
          · subst j; simpa using hrel
          · rw [Function.update_of_ne hji]
            exact hr j ((Finset.mem_insert.mp hj).resolve_left hji)
        · intro j hj
          have hji : j ≠ i := fun heq => hj (by simp [heq])
          rw [Function.update_of_ne hji]
          exact hb j (fun hjd => hj (Finset.mem_insert_of_mem hjd))
  obtain ⟨p',s',b,hp',hs',ht',hr,hb⟩ := aux Finset.univ
  exact ⟨p',s',b,hp',hs',by simpa using ht',fun i => hr i (Finset.mem_univ i)⟩

end GroupWL.FrameExchange
