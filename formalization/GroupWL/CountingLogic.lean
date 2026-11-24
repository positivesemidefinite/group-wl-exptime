import GroupWL.PebbleGame
import GroupWL.Refinement

/-! # Counting logic preserved by the after-pickup game

Formula atoms are arbitrary group words, so word length does not consume
additional variables. An `m`-variable formula is preserved by a winning
position with `m + 1` pairs. The last pair is the reserve needed to test
atomic relations after pickup.
-/

namespace GroupWL.CountingLogic

open Refinement PebbleGame

inductive Formula (m : ℕ) where
  | atom : GroupWord m → Formula m
  | neg : Formula m → Formula m
  | and : Formula m → Formula m → Formula m
  | count : ℕ → Fin m → Formula m → Formula m

/-- Semantics on finite groups; `count n i φ` means at least `n` values of
variable `i` satisfy `φ`. Rebinding does not introduce a new variable name. -/
def Formula.Realize {m : ℕ} {G : Type*} [Group G] (a : Fin m → G) : Formula m → Prop
  | .atom w => w.eval a = 1
  | .neg φ => ¬ φ.Realize a
  | .and φ ψ => φ.Realize a ∧ ψ.Realize a
  | .count n i φ => n ≤ Nat.card {g : G // φ.Realize (Function.update a i g)}

def wordVariables {m : ℕ} : GroupWord m → Finset (Fin m)
  | .one => ∅
  | .gen i => {i}
  | .mul u v => wordVariables u ∪ wordVariables v
  | .inv u => wordVariables u

def Formula.freeVariables {m : ℕ} : Formula m → Finset (Fin m)
  | .atom w => wordVariables w
  | .neg φ => φ.freeVariables
  | .and φ ψ => φ.freeVariables ∪ ψ.freeVariables
  | .count _ i φ => φ.freeVariables.erase i

theorem word_eval_congr {m : ℕ} {G : Type*} [Group G]
    (w : GroupWord m) {a b : Fin m → G}
    (h : ∀ i ∈ wordVariables w, a i = b i) : w.eval a = w.eval b := by
  induction w with
  | one => rfl
  | gen i => exact h i (Finset.mem_singleton_self i)
  | mul u v ihu ihv =>
      simp only [GroupWord.eval]
      rw [ihu (fun i hi => h i (Finset.mem_union_left _ hi)),
        ihv (fun i hi => h i (Finset.mem_union_right _ hi))]
  | inv u ih => exact congrArg Inv.inv (ih h)

theorem realize_congr {m : ℕ} {G : Type*} [Group G] (φ : Formula m)
    {a b : Fin m → G} (h : ∀ i ∈ φ.freeVariables, a i = b i) :
    φ.Realize a ↔ φ.Realize b := by
  induction φ generalizing a b with
  | atom w => exact congrArg (fun z => z = 1) (word_eval_congr w h) |>.to_iff
  | neg φ ih => exact not_congr (ih h)
  | and φ ψ ihφ ihψ =>
      exact and_congr (ihφ (fun i hi => h i (Finset.mem_union_left _ hi)))
        (ihψ (fun i hi => h i (Finset.mem_union_right _ hi)))
  | count n i φ ih =>
      have hφ : ∀ g, φ.Realize (Function.update a i g) ↔
          φ.Realize (Function.update b i g) := by
        intro g
        apply ih
        intro j hj
        by_cases hji : j = i
        · subst j; simp
        · simpa [Function.update, hji] using h j (Finset.mem_erase.mpr ⟨hji, hj⟩)
      have hc : Nat.card {g : G // φ.Realize (Function.update a i g)} =
          Nat.card {g : G // φ.Realize (Function.update b i g)} :=
        Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl G) hφ)
      change n ≤ _ ↔ n ≤ _
      rw [hc]

/-- All variable names are assigned to the first `m` pebble pairs. The last
pair may be occupied; it is available for the after-pickup atomic test. -/
def Tracks {m : ℕ} {G H : Type*} (p : Position (m + 1) G H)
    (a : Fin m → G) (b : Fin m → H) : Prop :=
  ∀ i, p i.castSucc = some (a i, b i)

def TracksOn {m : ℕ} {G H : Type*} (S : Finset (Fin m)) (p : Position (m + 1) G H)
    (a : Fin m → G) (b : Fin m → H) : Prop :=
  ∀ i ∈ S, p i.castSucc = some (a i, b i)

theorem Tracks.erase_spare {m : ℕ} {G H : Type*} {p : Position (m + 1) G H}
    {a : Fin m → G} {b : Fin m → H} (h : Tracks p a b) :
    Tracks (erase p (Fin.last m)) a b := by
  intro i
  rw [erase_ne _ _ _ (Fin.castSucc_ne_last i)]
  exact h i

theorem Tracks.place {m : ℕ} {G H : Type*} {p : Position (m + 1) G H}
    {a : Fin m → G} {b : Fin m → H} (hp : Tracks p a b)
    (i : Fin m) (g : G) (h : H) :
    Tracks (place p i.castSucc g h) (Function.update a i g) (Function.update b i h) := by
  intro j
  by_cases hji : j = i
  · subst j
    simp
  · have hcast : j.castSucc ≠ i.castSucc := by simpa using hji
    rw [place_ne _ _ _ _ _ hcast]
    simpa [Function.update, hji] using hp j

theorem atomic_preserves_words {m l : ℕ} {G H : Type*} [Group G] [Group H]
    {p : Position l G H} (hp : Atomic p) (a : Fin m → G) (b : Fin m → H)
    (slot : Fin m → Fin l) (hmarks : ∀ i, p (slot i) = some (a i, b i))
    (w : GroupWord m) : w.eval a = 1 ↔ w.eval b = 1 := by
  obtain ⟨S, T, e, he⟩ := hp
  have hS : ∀ i, a i ∈ S := fun i => (he (slot i) (a i) (b i) (hmarks i)).choose
  have hT : ∀ i, b i ∈ T := fun i => (he (slot i) (a i) (b i) (hmarks i)).choose_spec.choose
  let aS : Fin m → S := fun i => ⟨a i, hS i⟩
  let bT : Fin m → T := fun i => ⟨b i, hT i⟩
  have hevalS : w.eval a = (↑(w.eval aS) : G) :=
    GroupWord.eval_hom S.subtype aS w
  have hevalT : w.eval b = (↑(w.eval bT) : H) :=
    GroupWord.eval_hom T.subtype bT w
  have hab : e.toMonoidHom ∘ aS = bT := by
    funext i
    exact (he (slot i) (a i) (b i) (hmarks i)).choose_spec.choose_spec
  have heword : w.eval bT = e (w.eval aS) := by
    rw [← hab]
    exact GroupWord.eval_hom e.toMonoidHom aS w
  rw [hevalS, hevalT, heword]
  simp

/-- Bounded-variable counting-logic transfer for a genuine infinite winning
strategy in the Version-II after-pickup game. -/
theorem realize_iff_of_winning {m : ℕ} {G H : Type*} [Group G] [Group H]
    [Finite G] [Finite H] (φ : Formula m)
    {p : Position (m + 1) G H} {a : Fin m → G} {b : Fin m → H}
    (hp : Winning p) (htracks : Tracks p a b) :
    φ.Realize a ↔ φ.Realize b := by
  induction φ generalizing p a b with
  | atom w =>
      apply atomic_preserves_words (winning_step hp (Fin.last m)).1 a b Fin.castSucc
      exact htracks.erase_spare
  | neg φ ih => exact not_congr (ih hp htracks)
  | and φ ψ ihφ ihψ => exact and_congr (ihφ hp htracks) (ihψ hp htracks)
  | count n i φ ih =>
      obtain ⟨_, f, hf⟩ := winning_step hp i.castSucc
      have hφ : ∀ g, φ.Realize (Function.update a i g) ↔
          φ.Realize (Function.update b i (f g)) := by
        intro g
        exact ih (hf g) (htracks.place i g (f g))
      have hc : Nat.card {g : G // φ.Realize (Function.update a i g)} =
          Nat.card {h : H // φ.Realize (Function.update b i h)} :=
        Nat.card_congr (Equiv.subtypeEquiv f hφ)
      change n ≤ _ ↔ n ≤ _
      rw [hc]

theorem winning_complete_variables {m : ℕ} {G H : Type*} [Group G] [Group H]
    {S : Finset (Fin m)} {p : Position (m + 1) G H}
    {a : Fin m → G} {b : Fin m → H} (hp : Winning p) (hS : TracksOn S p a b) :
    ∃ q b', Winning q ∧ Tracks q a b' ∧ ∀ i ∈ S, b' i = b i := by
  have extend : ∀ T : Finset (Fin m),
      ∃ q b', Winning q ∧ TracksOn (S ∪ T) q a b' ∧ ∀ i ∈ S, b' i = b i := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact ⟨p, b, hp, by simpa [TracksOn] using hS, fun _ _ => rfl⟩
    | @insert i T hi ih =>
        obtain ⟨q, b', hq, htracks, hagree⟩ := ih
        by_cases hiS : i ∈ S
        · refine ⟨q, b', hq, ?_, hagree⟩
          intro j hj
          apply htracks j
          simpa [Finset.mem_union, Finset.mem_insert, hiS, or_assoc] using hj
        · obtain ⟨_, f, hf⟩ := winning_step hq i.castSucc
          refine ⟨place q i.castSucc (a i) (f (a i)), Function.update b' i (f (a i)),
            hf (a i), ?_, ?_⟩
          · intro j hj
            by_cases hji : j = i
            · subst j; simp
            · have hcast : j.castSucc ≠ i.castSucc := by simpa using hji
              rw [place_ne _ _ _ _ _ hcast]
              have hj' : j ∈ S ∪ T := by simpa [Finset.mem_union, Finset.mem_insert, hji] using hj
              simpa [Function.update, hji] using htracks j hj'
          · intro j hj
            have hji : j ≠ i := by intro hji; subst j; exact hiS hj
            simpa [Function.update, hji] using hagree j hj
  obtain ⟨q, b', hq, ht, ha⟩ := extend Finset.univ
  exact ⟨q, b', hq, fun i => ht i (Finset.mem_union_right _ (Finset.mem_univ i)), ha⟩

/-- Only free query and anchor variables need be retained. Bound-variable
slots can be filled during a hypothetical continuation of the winning game. -/
theorem realize_iff_of_winning_free {m : ℕ} {G H : Type*} [Group G] [Group H]
    [Finite G] [Finite H] (φ : Formula m)
    {p : Position (m + 1) G H} {a : Fin m → G} {b : Fin m → H}
    (hp : Winning p) (htracks : TracksOn φ.freeVariables p a b) :
    φ.Realize a ↔ φ.Realize b := by
  obtain ⟨q, b', hq, ht, ha⟩ := winning_complete_variables hp htracks
  exact (realize_iff_of_winning φ hq ht).trans (realize_congr φ ha)

/-- A closed sentence is invariant already from the initial empty position. -/
theorem sentence_iff_of_winning_empty {m : ℕ} {G H : Type*} [Group G] [Group H]
    [Finite G] [Finite H] (φ : Formula m) (hclosed : φ.freeVariables = ∅)
    (hp : Winning (empty : Position (m + 1) G H)) (a : Fin m → G) (b : Fin m → H) :
    φ.Realize a ↔ φ.Realize b := by
  apply realize_iff_of_winning_free φ hp
  intro i hi
  simp [hclosed] at hi

end GroupWL.CountingLogic
