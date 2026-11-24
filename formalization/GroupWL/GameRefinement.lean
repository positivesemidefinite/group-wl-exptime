import GroupWL.PebbleGame
import GroupWL.Refinement
import GroupWL.CountingLogic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Equiv.Prod

/-!
# A winning group game preserves Weisfeiler--Leman colors

The same announced bijection transports the entire replacement-color vector.
To inspect replacement coordinate `i`, its old pebble slot becomes the spare
slot and the newly placed spare becomes coordinate `i`.
-/

namespace GroupWL.GameRefinement

open PebbleGame Refinement

universe u v w
variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- A tuple's distinct pebble slots, together with a slot outside the tuple. -/
structure Slots (k m : ℕ) where
  tuple : Fin k ↪ Fin m
  spare : Fin m
  outside : ∀ i, tuple i ≠ spare

variable {k m : ℕ}

def Slots.standard (k : ℕ) : Slots k (k + 1) where
  tuple := ⟨Fin.castSucc, Fin.castSucc_injective k⟩
  spare := Fin.last k
  outside := Fin.castSucc_ne_last

/-- Exchange one tuple slot with the spare slot. -/
def Slots.replace (s : Slots k m) (i : Fin k) : Slots k m where
  tuple :=
    { toFun := Function.update s.tuple i s.spare
      inj' := by
        intro j l h
        by_cases hj : j = i
        · subst j
          by_cases hl : l = i
          · exact hl.symm
          · have hbad : s.spare = s.tuple l := by simpa [Function.update, hl] using h
            exact False.elim (s.outside l hbad.symm)
        · by_cases hl : l = i
          · subst l
            have hbad : s.tuple j = s.spare := by simpa [Function.update, hj] using h
            exact False.elim (s.outside j hbad)
          · apply s.tuple.injective
            simpa [Function.update, hj, hl] using h }
  spare := s.tuple i
  outside j := by
    change Function.update s.tuple i s.spare j ≠ s.tuple i
    by_cases hj : j = i
    · subst j
      simpa using (s.outside i).symm
    · simp only [Function.update_of_ne hj]
      intro h
      exact hj (s.tuple.injective h)

def Tracks (s : Slots k m) (p : Position m G H) (a : Fin k → G) (b : Fin k → H) : Prop :=
  ∀ i, p (s.tuple i) = some (a i,b i)

omit [Group G] [Group H] in
theorem Tracks.erase_spare {s : Slots k m} {p : Position m G H}
    {a : Fin k → G} {b : Fin k → H} (h : Tracks s p a b) :
    Tracks s (erase p s.spare) a b := by
  intro i
  rw [erase_ne _ _ _ (s.outside i)]
  exact h i

omit [Group G] [Group H] in
theorem Tracks.replace {s : Slots k m} {p : Position m G H}
    {a : Fin k → G} {b : Fin k → H} (h : Tracks s p a b)
    (i : Fin k) (g : G) (h' : H) :
    Tracks (s.replace i) (place p s.spare g h')
      (Function.update a i g) (Function.update b i h') := by
  intro j
  by_cases hji : j = i
  · subst j
    simp [Slots.replace]
  · simp only [Slots.replace, Function.Embedding.coeFn_mk, Function.update_of_ne hji]
    rw [place_ne _ _ _ _ _ (s.outside j)]
    exact h j

private theorem map_univ_congr {A : Type u} {B : Type v} {C : Type w}
    [Fintype A] [Fintype B] (e : A ≃ B) (f : A → C) (g : B → C)
    (h : ∀ a, f a = g (e a)) :
    Finset.univ.val.map f = Finset.univ.val.map g := by
  calc
    _ = Finset.univ.val.map (g ∘ e) := by congr 1; funext a; exact h a
    _ = (Finset.univ.val.map e).map g := by rw [Multiset.map_map]
    _ = _ := by rw [Multiset.map_univ_val_equiv]

/-- A winning position with a spare pair preserves every recursive shared
Version-II color, with the manuscript's joint replacement-vector convention. -/
theorem color_eq_of_winning [Fintype G] [Fintype H]
    (r : ℕ) {s : Slots k m} {p : Position m G H}
    {a : Fin k → G} {b : Fin k → H} (hp : Winning p) (ht : Tracks s p a b) :
    color (initialII (G := G) k) r a = color (initialII (G := H) k) r b := by
  classical
  induction r generalizing s p a b with
  | zero =>
      funext word
      change decide (word.eval a = 1) = decide (word.eval b = 1)
      have hword := CountingLogic.atomic_preserves_words
        (winning_step hp s.spare).1 a b s.tuple ht.erase_spare word
      simp only [hword]
  | succ r ih =>
      apply Prod.ext
      · exact ih hp ht
      · obtain ⟨_, f, hf⟩ := winning_step hp s.spare
        apply map_univ_congr f
        intro g
        funext i
        exact ih (hf g) (ht.replace i g (f g))

/-- Sequentially filling distinct slots gives a triangular bijection on all
tuples. Earlier choices may affect the bijection announced for later slots. -/
theorem complete_tuples {m : ℕ} (n : ℕ) (slot : Fin n ↪ Fin m)
    {p : Position m G H} (hp : Winning p) :
    ∃ e : (Fin n → G) ≃ (Fin n → H), ∀ a, ∃ q : Position m G H,
      Winning q ∧ (∀ i, q (slot i) = some (a i, e a i)) ∧
        ∀ j, (∀ i, slot i ≠ j) → q j = p j := by
  classical
  induction n generalizing p with
  | zero =>
      let e : (Fin 0 → G) ≃ (Fin 0 → H) :=
        { toFun := fun _ i => Fin.elim0 i
          invFun := fun _ i => Fin.elim0 i
          left_inv := fun _ => by funext i; exact Fin.elim0 i
          right_inv := fun _ => by funext i; exact Fin.elim0 i }
      exact ⟨e, fun _ => ⟨p, hp, fun i => Fin.elim0 i, fun _ _ => rfl⟩⟩
  | succ n ih =>
      obtain ⟨_, f, hf⟩ := winning_step hp (slot 0)
      let tailSlot : Fin n ↪ Fin m :=
        ⟨fun i => slot i.succ, fun i j h => Fin.succ_injective n (slot.injective h)⟩
      have htail : ∀ g : G, ∃ e : (Fin n → G) ≃ (Fin n → H), ∀ a,
          ∃ q : Position m G H, Winning q ∧
            (∀ i, q (tailSlot i) = some (a i,e a i)) ∧
              ∀ j, (∀ i, tailSlot i ≠ j) → q j = place p (slot 0) g (f g) j :=
        fun g => ih tailSlot (hf g)
      choose es hes using htail
      let e : (Fin (n+1) → G) ≃ (Fin (n+1) → H) :=
        (Fin.consEquiv (fun _ : Fin (n+1) => G)).symm.trans
          ((Equiv.prodCongrRight es).trans
            ((Equiv.prodCongr f (Equiv.refl (Fin n → H))).trans
              (Fin.consEquiv (fun _ : Fin (n+1) => H))))
      have e_zero (a : Fin (n+1) → G) : e a 0 = f (a 0) := rfl
      have e_succ (a : Fin (n+1) → G) (i : Fin n) :
          e a i.succ = es (a 0) (Fin.tail a) i := rfl
      refine ⟨e, fun a => ?_⟩
      obtain ⟨q, hq, hmarks, hpreserve⟩ := hes (a 0) (Fin.tail a)
      refine ⟨q, hq, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun i => ?_) i
        · rw [hpreserve (slot 0) ?_, place_self, e_zero]
          intro i hi
          exact Fin.succ_ne_zero i (slot.injective hi)
        · exact hmarks i
      · intro j hj
        rw [hpreserve j (fun i => hj i.succ)]
        exact place_ne p (slot 0) j (a 0) (f (a 0)) (hj 0).symm

/-- A winning `(k+1)`-pebble game from the empty position implies stable
Version-II equivalence of the actual color histograms. -/
theorem equivalentII_of_winning_empty [Fintype G] [Fintype H] (k : ℕ)
    (hp : Winning (empty : Position (k+1) G H)) : EquivalentII k G H := by
  classical
  obtain ⟨e, he⟩ := complete_tuples k (Slots.standard k).tuple hp
  intro r
  apply map_univ_congr e
  intro a
  obtain ⟨q, hq, htracks, _⟩ := he a
  exact color_eq_of_winning r hq htracks

end GroupWL.GameRefinement
