import GroupWL.GameRefinement
import GroupWL.Identification
import GroupWL.WordAtomic
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Stable WL colors give a winning after-pickup pebble strategy -/

namespace GroupWL.RefinementGame

open Refinement PebbleGame GameRefinement

universe u v w
variable {G : Type u} {H : Type v} [Group G] [Group H] [Fintype G] [Fintype H]
variable {k : ℕ}

/-- Equal stable tuple colors, without choosing a numerical stable-color coding. -/
def Same (a : Fin k → G) (b : Fin k → H) : Prop :=
  ∀ r, color (initialII (G := G) k) r a = color (initialII (G := H) k) r b

theorem color_eq_lower {a : Fin k → G} {b : Fin k → H} {r s : ℕ}
    (hrs : r ≤ s) (h : color (initialII (G := G) k) s a = color (initialII (G := H) k) s b) :
    color (initialII (G := G) k) r a = color (initialII (G := H) k) r b := by
  induction s generalizing r with
  | zero => have hr : r = 0 := by omega
            subst r
            exact h
  | succ s ih =>
      by_cases hrs' : r ≤ s
      · exact ih hrs' (congrArg Prod.fst h)
      · have hr : r = s+1 := by omega
        subst r
        exact h

private theorem equiv_of_map_univ_eq {A : Type u} {B : Type v} {C : Type w}
    [Fintype A] [Fintype B] (f : A → C) (g : B → C)
    (h : Finset.univ.val.map f = Finset.univ.val.map g) :
    ∃ e : A ≃ B, ∀ a, f a = g (e a) := by
  classical
  have hc (c : C) : Fintype.card {a : A // f a = c} = Fintype.card {b : B // g b = c} := by
    have he := congrArg (Multiset.count c) h
    simp only [Multiset.count_map, ← Finset.filter_val, eq_comm (a := c)] at he
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact he
  let es (c : C) : {a : A // f a = c} ≃ {b : B // g b = c} :=
    Fintype.equivOfCardEq (hc c)
  exact ⟨Equiv.ofFiberEquiv es, fun a => (Equiv.ofFiberEquiv_map es a).symm⟩

/-- Equal successor colors give one bijection matching all coordinate
replacement colors simultaneously. -/
theorem matching_bijection {a : Fin k → G} {b : Fin k → H} (r : ℕ)
    (h : color (initialII (G := G) k) (r+1) a = color (initialII (G := H) k) (r+1) b) :
    ∃ f : G ≃ H, ∀ x i,
      color (initialII (G := G) k) r (Function.update a i x) =
      color (initialII (G := H) k) r (Function.update b i (f x)) := by
  obtain ⟨f, hf⟩ := equiv_of_map_univ_eq _ _ (congrArg Prod.snd h)
  exact ⟨f, fun x i => congrFun (hf x) i⟩

/-- Finitely many bijections suffice to select a single bijection matching
all stable replacement colors. -/
theorem stable_matching_bijection {a : Fin k → G} {b : Fin k → H} (h : Same a b) :
    ∃ f : G ≃ H, ∀ x i, Same (Function.update a i x) (Function.update b i (f x)) := by
  classical
  by_contra hn
  have hbad : ∀ f : G ≃ H, ∃ r : ℕ, ¬ ∀ x i,
      color (initialII (G := G) k) r (Function.update a i x) =
      color (initialII (G := H) k) r (Function.update b i (f x)) := by
    intro f
    by_contra hgood
    push Not at hgood
    exact hn ⟨f, fun x i r => hgood r x i⟩
  choose r hr using hbad
  let R : ℕ := Finset.univ.sup r
  obtain ⟨f, hf⟩ := matching_bijection R (h (R+1))
  apply hr f
  intro x i
  exact color_eq_lower (Finset.le_sup (Finset.mem_univ f)) (hf x i)

/-- Renaming the variable symbols of a group word. -/
def renameWord (e : Fin k → Fin k) : GroupWord k → GroupWord k
  | .one => .one
  | .gen i => .gen (e i)
  | .mul s t => .mul (renameWord e s) (renameWord e t)
  | .inv s => .inv (renameWord e s)

@[simp] theorem eval_renameWord (e : Fin k → Fin k) (a : Fin k → G) (s : GroupWord k) :
    (renameWord e s).eval a = s.eval (a ∘ e) := by
  induction s with
  | one => rfl
  | gen i => rfl
  | mul s t hs ht => simp [renameWord, GroupWord.eval, hs, ht]
  | inv s hs => simp [renameWord, GroupWord.eval, hs]

/-- Permuting coordinates acts explicitly on recursively defined colors. -/
def permuteColor (e : Fin k ≃ Fin k) : (r : ℕ) →
    Color (GroupWord k → Bool) k r → Color (GroupWord k → Bool) k r
  | 0, c => fun word => c (renameWord e word)
  | r+1, c => (permuteColor e r c.1,
      c.2.map fun v i => permuteColor e r (v (e i)))

private theorem update_comp (e : Fin k ≃ Fin k) (a : Fin k → G) (i : Fin k) (x : G) :
    Function.update (a ∘ e) i x = (Function.update a (e i) x) ∘ e := by
  classical
  funext j
  by_cases hji : j = i
  · subst j; simp
  · have hei : e j ≠ e i := fun h => hji (e.injective h)
    simp [Function.update, hji, hei]

theorem color_permute (e : Fin k ≃ Fin k) (r : ℕ) (a : Fin k → G) :
    color (initialII (G := G) k) r (a ∘ e) =
      permuteColor e r (color (initialII (G := G) k) r a) := by
  classical
  induction r generalizing a with
  | zero => funext word; simp [color, initialII, permuteColor]
  | succ r ih =>
      apply Prod.ext
      · exact ih a
      · change Finset.univ.val.map (fun x i => color (initialII (G := G) k) r
            (Function.update (a ∘ e) i x)) =
          (Finset.univ.val.map (fun x i => color (initialII (G := G) k) r
            (Function.update a i x))).map (fun v i => permuteColor e r (v (e i)))
        rw [Multiset.map_map]
        congr 1
        funext x i
        rw [update_comp, ih]
        rfl

theorem Same.permute {a : Fin k → G} {b : Fin k → H} (h : Same a b) (e : Fin k ≃ Fin k) :
    Same (a ∘ e) (b ∘ e) := by
  intro r
  rw [color_permute, color_permute, h r]

/-- Slots with the prescribed pair reserved for pickup. -/
def slotsAt (i : Fin (k+1)) : Slots k (k+1) where
  tuple := i.succAboveEmb
  spare := i
  outside := Fin.succAbove_ne i

/-- A full tuple of `k+1` slots is a bijective enumeration of all slots other
than its spare. -/
noncomputable def complementEquiv (s : Slots k (k+1)) :
    Fin k ≃ {j : Fin (k+1) // j ≠ s.spare} := by
  classical
  let f : Fin k → {j : Fin (k+1) // j ≠ s.spare} := fun i => ⟨s.tuple i, s.outside i⟩
  apply Equiv.ofBijective f
  apply (Fintype.bijective_iff_injective_and_card f).mpr
  exact ⟨fun i j h => s.tuple.injective (congrArg Subtype.val h),
    Fintype.card_congr (finSuccAboveEquiv s.spare)⟩

@[simp] theorem complementEquiv_val (s : Slots k (k+1)) (i : Fin k) :
    (complementEquiv s i).val = s.tuple i := rfl

theorem slots_cover (s : Slots k (k+1)) (j : Fin (k+1)) (hj : j ≠ s.spare) :
    ∃ i, s.tuple i = j := by
  obtain ⟨i, hi⟩ := (complementEquiv s).surjective ⟨j,hj⟩
  exact ⟨i, congrArg Subtype.val hi⟩

/-- Enumerations omitting the same spare differ only by a tuple permutation. -/
theorem slots_permutation (s t : Slots k (k+1)) (hsp : s.spare = t.spare) :
    ∃ e : Fin k ≃ Fin k, ∀ i, s.tuple (e i) = t.tuple i := by
  classical
  let f : Fin k → Fin k := fun i =>
    (complementEquiv s).symm ⟨t.tuple i, by simpa [hsp] using t.outside i⟩
  have hf (i : Fin k) : s.tuple (f i) = t.tuple i :=
    congrArg Subtype.val ((complementEquiv s).apply_symm_apply _)
  have hinj : Function.Injective f := by
    intro i j hij
    apply t.tuple.injective
    rw [← hf i, ← hf j, hij]
  exact ⟨Equiv.ofBijective f ⟨hinj,Finite.surjective_of_injective hinj⟩,hf⟩

private theorem replacement_coordinates (s : Slots k (k+1)) (a : Fin (k+1) → G)
    (i : Fin k) (x : G) :
    (Function.update a s.spare x) ∘ (s.replace i).tuple = Function.update (a ∘ s.tuple) i x := by
  classical
  funext j
  by_cases hji : j = i
  · subst j
    simp [Function.comp_def, Slots.replace, Function.update]
  · simp [Function.comp_def, Slots.replace, Function.update, hji, s.outside j]

/-- Every deletion of one pair has equal stable tuple colors. Keeping all
orders of the retained slots makes coordinate permutations explicit. -/
def FullGood (a : Fin (k+1) → G) (b : Fin (k+1) → H) : Prop :=
  ∀ s : Slots k (k+1), Same (a ∘ s.tuple) (b ∘ s.tuple)

/-- After any pickup there is a bijection maintaining the deletion invariant
for every possible subsequent choice. -/
theorem fullGood_step {a : Fin (k+1) → G} {b : Fin (k+1) → H}
    (hgood : FullGood a b) (i : Fin (k+1)) :
    ∃ f : G ≃ H, ∀ x, FullGood (Function.update a i x) (Function.update b i (f x)) := by
  classical
  let s := slotsAt i
  obtain ⟨f,hf⟩ := stable_matching_bijection (hgood s)
  refine ⟨f,fun x t => ?_⟩
  by_cases hti : t.spare = i
  · have hGa : (Function.update a i x) ∘ t.tuple = a ∘ t.tuple := by
      funext j
      exact Function.update_of_ne (by simpa [← hti] using t.outside j) _ _
    have hHb : (Function.update b i (f x)) ∘ t.tuple = b ∘ t.tuple := by
      funext j
      exact Function.update_of_ne (by simpa [← hti] using t.outside j) _ _
    rw [hGa,hHb]
    exact hgood t
  · obtain ⟨j,hj⟩ := slots_cover s t.spare hti
    obtain ⟨e,he⟩ := slots_permutation (s.replace j) t hj
    have hframe : Same ((Function.update a i x) ∘ (s.replace j).tuple)
        ((Function.update b i (f x)) ∘ (s.replace j).tuple) := by
      change Same ((Function.update a s.spare x) ∘ (s.replace j).tuple)
        ((Function.update b s.spare (f x)) ∘ (s.replace j).tuple)
      rw [replacement_coordinates,replacement_coordinates]
      exact hf x j
    have hperm := hframe.permute e
    convert hperm using 1
    · funext l
      exact congrArg (Function.update a i x) (he l).symm
    · funext l
      exact congrArg (Function.update b i (f x)) (he l).symm

def fullPosition (a : Fin (k+1) → G) (b : Fin (k+1) → H) : Position (k+1) G H :=
  fun i => some (a i,b i)

/-- The after-pickup atomic test follows from the complete word-type component
of the stable tuple color. -/
theorem fullGood_atomic {a : Fin (k+1) → G} {b : Fin (k+1) → H}
    (hgood : FullGood a b) (i : Fin (k+1)) : Atomic (erase (fullPosition a b) i) := by
  apply WordAtomic.atomic_of_initialII_eq (hgood (slotsAt i) 0)
  intro j g h hmark
  have hji : j ≠ i := by intro hj; subst j; simp at hmark
  obtain ⟨l,hl⟩ := slots_cover (slotsAt i) j hji
  have hpairs : a j = g ∧ b j = h := by
    simpa [erase_ne _ _ _ hji,fullPosition] using hmark
  exact ⟨l,by simpa [Function.comp_def,hl] using hpairs.1,
    by simpa [Function.comp_def,hl] using hpairs.2⟩

/-- The deletion-color invariant is a genuine infinite winning strategy. -/
theorem winning_fullPosition {a : Fin (k+1) → G} {b : Fin (k+1) → H}
    (hgood : FullGood a b) : Winning (fullPosition a b) := by
  let I : Position (k+1) G H → Prop := fun p => ∃ a b, p = fullPosition a b ∧ FullGood a b
  refine ⟨I,⟨a,b,rfl,hgood⟩,?_⟩
  rintro p ⟨a,b,rfl,hgood⟩ i
  refine ⟨fullGood_atomic hgood i,?_⟩
  obtain ⟨f,hf⟩ := fullGood_step hgood i
  refine ⟨f,fun x => ⟨Function.update a i x,Function.update b i (f x),?_,hf x⟩⟩
  funext j
  by_cases hji : j = i <;> simp [fullPosition,place,Function.update,hji]

/-- Forgetting marks cannot destroy a winning strategy. The strategy may keep
virtual marks in the witness position while playing the smaller position. -/
theorem winning_of_restricts {m : ℕ} {p q : Position m G H}
    (hp : Winning p) (hqp : Restricts q p) : Winning q := by
  let I : Position m G H → Prop := fun q => ∃ p, Winning p ∧ Restricts q p
  refine ⟨I,⟨p,hp,hqp⟩,?_⟩
  rintro q ⟨p,hp,hqp⟩ i
  obtain ⟨ha,f,hf⟩ := winning_step hp i
  constructor
  · apply ha.restricts
    intro j g h hmark
    by_cases hji : j = i
    · subst j; simp at hmark
    · rw [erase_ne _ _ _ hji] at hmark ⊢
      exact hqp j g h hmark
  · refine ⟨f,fun x => ⟨place p i x (f x),hf x,?_⟩⟩
    intro j g h hmark
    by_cases hji : j = i
    · subst j
      simpa using hmark
    · rw [place_ne _ _ _ _ _ hji] at hmark ⊢
      exact hqp j g h hmark

/-- Histogram equivalence matches the all-identity tuple to itself, since its
initial word type forces every coordinate of a matching tuple to be identity. -/
theorem same_identity_tuple (h : EquivalentII k G H) :
    Same (fun _ : Fin k => (1:G)) (fun _ : Fin k => (1:H)) := by
  intro r
  have hm : color (initialII (G := G) k) r (fun _ => 1) ∈ histogram (initialII (G := G) k) r :=
    Multiset.mem_map.mpr ⟨(fun _ => 1),Finset.mem_univ _,rfl⟩
  rw [h r] at hm
  obtain ⟨b,_,hb⟩ := Multiset.mem_map.mp hm
  have hzero := color_eq_lower (Nat.zero_le r) hb.symm
  have hb1 : b = fun _ => 1 := by
    funext i
    exact (relations_iff_of_initialII_eq hzero (.gen i)).mp rfl
  rw [← hb1]
  exact hb.symm

/-- Stable Version-II equivalence supplies the actual `(k+1)`-pair game
strategy. No game/refinement correspondence is assumed. -/
theorem winning_empty_of_equivalentII (h : EquivalentII k G H) :
    Winning (empty : Position (k+1) G H) := by
  have hgood : FullGood (fun _ : Fin (k+1) => (1:G)) (fun _ : Fin (k+1) => (1:H)) :=
    fun _ => same_identity_tuple h
  apply winning_of_restricts (winning_fullPosition hgood)
  intro i g h hmark
  simp [empty] at hmark

/-- The full correspondence, with the manuscript's after-pickup convention. -/
theorem equivalentII_iff_winning_empty : EquivalentII k G H ↔
    Winning (empty : Position (k+1) G H) :=
  ⟨winning_empty_of_equivalentII,GameRefinement.equivalentII_of_winning_empty k⟩

end GroupWL.RefinementGame
