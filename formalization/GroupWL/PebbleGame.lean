import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# The Version-II bijective pebble game

The atomic relation below is the marked-subgroup isomorphism condition.  The
round recursion tests this condition after pickup, as in the manuscript.  A
bijection is announced before the next element is selected.  Selection from
the right-hand group is included because every announced map is an equivalence.
-/

namespace GroupWL
namespace PebbleGame

universe u v

abbrev Position (m : ℕ) (G : Type u) (H : Type v) := Fin m → Option (G × H)

variable {m : ℕ} {G : Type u} {H : Type v}

def empty : Position m G H := fun _ => none

def erase (p : Position m G H) (i : Fin m) : Position m G H :=
  Function.update p i none

def place (p : Position m G H) (i : Fin m) (g : G) (h : H) : Position m G H :=
  Function.update p i (some (g, h))

@[simp] theorem erase_self (p : Position m G H) (i : Fin m) : erase p i i = none := by
  simp [erase]

@[simp] theorem place_self (p : Position m G H) (i : Fin m) (g : G) (h : H) :
    place p i g h i = some (g, h) := by
  simp [place]

@[simp] theorem erase_ne (p : Position m G H) (i j : Fin m) (h : j ≠ i) :
    erase p i j = p j := by
  simp [erase, h]

@[simp] theorem place_ne (p : Position m G H) (i j : Fin m) (g : G) (h : H)
    (hne : j ≠ i) : place p i g h j = p j := by
  simp [place, hne]

/-- `q` is obtained by forgetting some of the marks of `p`. -/
def Restricts (q p : Position m G H) : Prop :=
  ∀ i g h, q i = some (g, h) → p i = some (g, h)

theorem erase_restricts (p : Position m G H) (i : Fin m) : Restricts (erase p i) p := by
  intro j g h heq
  by_cases hji : j = i
  · subst j
    simp at heq
  · simpa [erase_ne p i j hji] using heq

section Support
variable {X : Type*} [DecidableEq X]

/-- Input coordinates of the currently occupied left-hand pebbles. -/
def support (c : G → X) (p : Position m G H) : Finset X :=
  Finset.univ.biUnion fun i => match p i with
    | none => ∅
    | some gh => {c gh.1}

@[simp] theorem mem_support {c : G → X} {p : Position m G H} {x : X} :
    x ∈ support c p ↔ ∃ i g h, p i = some (g,h) ∧ c g = x := by
  simp only [support, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    cases heq : p i with
    | none => simp [heq] at hi
    | some gh =>
        refine ⟨i, gh.1, gh.2, heq, ?_⟩
        simpa [heq, eq_comm] using hi
  · rintro ⟨i, g, h, hmark, rfl⟩
    exact ⟨i, by simp [hmark]⟩

@[simp] theorem support_empty (c : G → X) : support c (empty : Position m G H) = ∅ := by
  ext x
  simp [mem_support, empty]

theorem support_mono (c : G → X) {p q : Position m G H} (hqp : Restricts q p) :
    support c q ⊆ support c p := by
  intro x hx
  obtain ⟨i, g, h, hmark, heq⟩ := mem_support.mp hx
  exact mem_support.mpr ⟨i, g, h, hqp i g h hmark, heq⟩

theorem support_place (c : G → X) (p : Position m G H) (i : Fin m) (g : G) (h : H) :
    support c (place p i g h) = insert (c g) (support c (erase p i)) := by
  ext x
  rw [Finset.mem_insert, mem_support]
  constructor
  · rintro ⟨j, g', h', hmark, heq⟩
    by_cases hji : j = i
    · subst j
      simp only [place_self, Option.some.injEq, Prod.mk.injEq] at hmark
      exact Or.inl (hmark.1 ▸ heq.symm)
    · right
      apply mem_support.mpr
      exact ⟨j, g', h', by simpa [place_ne p i j g h hji, erase_ne p i j hji] using hmark, heq⟩
  · rintro (rfl | hx)
    · exact ⟨i, g, h, place_self p i g h, rfl⟩
    · obtain ⟨j, g', h', hmark, heq⟩ := mem_support.mp hx
      have hji : j ≠ i := by intro hi; subst j; simp at hmark
      exact ⟨j, g', h', by simpa [place_ne p i j g h hji, erase_ne p i j hji] using hmark, heq⟩

theorem card_support_le (c : G → X) (p : Position m G H) : (support c p).card ≤ m := by
  calc
    _ ≤ ∑ i : Fin m, (match p i with | none => ∅ | some gh => ({c gh.1} : Finset X)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin m, 1 := by
      apply Finset.sum_le_sum
      intro i hi
      cases p i <;> simp
    _ = m := by simp

theorem card_support_erase_lt (c : G → X) (p : Position m G H) (i : Fin m) :
    (support c (erase p i)).card < m := by
  have heq : support c (erase p i) =
      (Finset.univ.erase i).biUnion (fun j => match p j with
        | none => ∅ | some gh => ({c gh.1} : Finset X)) := by
    ext x
    rw [mem_support]
    simp only [Finset.mem_biUnion, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨j, g, h, hmark, rfl⟩
      have hji : j ≠ i := by intro hi; subst j; simp at hmark
      have horig : p j = some (g, h) := by simpa [erase_ne p i j hji] using hmark
      exact ⟨j, hji, by simp [horig]⟩
    · rintro ⟨j, hji, hx⟩
      cases hj : p j with
      | none => simp [hj] at hx
      | some gh =>
        refine ⟨j, gh.1, gh.2, ?_, ?_⟩
        · simpa [erase_ne p i j hji] using hj
        · simpa [hj, eq_comm] using hx
  rw [heq]
  calc
    _ ≤ ∑ j ∈ Finset.univ.erase i,
        (match p j with | none => ∅ | some gh => ({c gh.1} : Finset X)).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ Finset.univ.erase i, 1 := by
      apply Finset.sum_le_sum
      intro j hj
      cases p j <;> simp
    _ = m - 1 := by simp
    _ < m := Nat.sub_lt (Nat.zero_lt_of_lt i.isLt) (by omega)

end Support

section Groups
variable [Group G] [Group H]

/-- The two marked tuples extend to an isomorphism of subgroups.
`atomic_iff_generated` below identifies this with the usual test on the
subgroups generated by the marks. -/
def Atomic (p : Position m G H) : Prop :=
  ∃ (S : Subgroup G) (T : Subgroup H) (e : S ≃* T),
    ∀ i g h, p i = some (g, h) →
      ∃ (hg : g ∈ S) (hh : h ∈ T), e ⟨g, hg⟩ = ⟨h, hh⟩

def leftMarks (p : Position m G H) : Set G :=
  {g | ∃ i h, p i = some (g, h)}

def rightMarks (p : Position m G H) : Set H :=
  {h | ∃ i g, p i = some (g, h)}

def leftGenerated (p : Position m G H) : Subgroup G := Subgroup.closure (leftMarks p)
def rightGenerated (p : Position m G H) : Subgroup H := Subgroup.closure (rightMarks p)

omit [Group H] in
theorem mem_leftGenerated {p : Position m G H} {i : Fin m} {g : G} {h : H}
    (hp : p i = some (g, h)) : g ∈ leftGenerated p :=
  Subgroup.subset_closure ⟨i, h, hp⟩

omit [Group G] in
theorem mem_rightGenerated {p : Position m G H} {i : Fin m} {g : G} {h : H}
    (hp : p i = some (g, h)) : h ∈ rightGenerated p :=
  Subgroup.subset_closure ⟨i, g, hp⟩

/-- The literal marked-generated-subgroup atomic condition. -/
def GeneratedAtomic (p : Position m G H) : Prop :=
  ∃ e : leftGenerated p ≃* rightGenerated p,
    ∀ i g h (hp : p i = some (g, h)),
      e ⟨g, mem_leftGenerated hp⟩ = ⟨h, mem_rightGenerated hp⟩

theorem atomic_of_generated {p : Position m G H} (hp : GeneratedAtomic p) : Atomic p := by
  obtain ⟨e, he⟩ := hp
  exact ⟨leftGenerated p, rightGenerated p, e,
    fun i g h hmark => ⟨mem_leftGenerated hmark, mem_rightGenerated hmark,
      he i g h hmark⟩⟩

private theorem closure_image_mem {S : Subgroup G} {T : Subgroup H}
    (e : S ≃* T) (s : Set G) (t : Set H)
    (hs : s ⊆ S)
    (hst : ∀ g ∈ s, ∀ hg : g ∈ S, (e ⟨g, hg⟩ : H) ∈ Subgroup.closure t)
    {g : G} (hg : g ∈ Subgroup.closure s) :
    ∀ hgS : g ∈ S, (e ⟨g, hgS⟩ : H) ∈ Subgroup.closure t := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hst x hx
  | one =>
      intro h
      change (e (1 : S) : H) ∈ Subgroup.closure t
      rw [map_one]
      exact (Subgroup.closure t).one_mem
  | mul x y hx hy ihx ihy =>
      intro hxy
      have hxS := (Subgroup.closure_le S).2 hs hx
      have hyS := (Subgroup.closure_le S).2 hs hy
      change (e (⟨x, hxS⟩ * ⟨y, hyS⟩) : H) ∈ Subgroup.closure t
      rw [map_mul]
      exact (Subgroup.closure t).mul_mem (ihx hxS) (ihy hyS)
  | inv x hx ih =>
      intro hxinv
      have hxS := (Subgroup.closure_le S).2 hs hx
      change (e (⟨x, hxS⟩ : S)⁻¹ : H) ∈ Subgroup.closure t
      rw [map_inv]
      exact (Subgroup.closure t).inv_mem (ih hxS)

theorem generated_of_atomic {p : Position m G H} (hp : Atomic p) : GeneratedAtomic p := by
  obtain ⟨S, T, e, he⟩ := hp
  have hS : leftMarks p ⊆ S := by
    rintro g ⟨i, h, hmark⟩
    exact (he i g h hmark).choose
  have hT : rightMarks p ⊆ T := by
    rintro h ⟨i, g, hmark⟩
    exact (he i g h hmark).choose_spec.choose
  have hGS : leftGenerated p ≤ S := (Subgroup.closure_le S).2 hS
  have hGT : rightGenerated p ≤ T := (Subgroup.closure_le T).2 hT
  have hf : ∀ g : leftGenerated p, (e ⟨g, hGS g.property⟩ : H) ∈ rightGenerated p := by
    intro g
    apply closure_image_mem e (leftMarks p) (rightMarks p) hS _ g.property
    rintro x ⟨i, y, hmark⟩ hx
    obtain ⟨hx', hy, heq⟩ := he i x y hmark
    simpa [heq] using mem_rightGenerated hmark
  have hb : ∀ h : rightGenerated p, (e.symm ⟨h, hGT h.property⟩ : G) ∈ leftGenerated p := by
    intro h
    apply closure_image_mem e.symm (rightMarks p) (leftMarks p) hT _ h.property
    rintro y ⟨i, x, hmark⟩ hy
    obtain ⟨hx, hy', heq⟩ := he i x y hmark
    have heq' : e.symm ⟨y, hy⟩ = ⟨x, hx⟩ := by
      rw [← heq, e.symm_apply_apply]
    rw [heq']
    exact mem_leftGenerated hmark
  let e' : leftGenerated p ≃* rightGenerated p :=
    { toFun := fun g => ⟨e ⟨g, hGS g.property⟩, hf g⟩
      invFun := fun h => ⟨e.symm ⟨h, hGT h.property⟩, hb h⟩
      left_inv := fun g => by
        apply Subtype.ext
        exact congrArg (fun s : S => (s : G)) (e.symm_apply_apply ⟨g, hGS g.property⟩)
      right_inv := fun h => by
        apply Subtype.ext
        exact congrArg (fun t : T => (t : H)) (e.apply_symm_apply ⟨h, hGT h.property⟩)
      map_mul' := fun g g' => by
        apply Subtype.ext
        exact congrArg (fun t : T => (t : H))
          (e.map_mul ⟨g, hGS g.property⟩ ⟨g', hGS g'.property⟩) }
  refine ⟨e', ?_⟩
  intro i g h hmark
  obtain ⟨hg, hh, heq⟩ := he i g h hmark
  apply Subtype.ext
  exact congrArg (fun t : T => (t : H)) heq

theorem atomic_iff_generated (p : Position m G H) : Atomic p ↔ GeneratedAtomic p :=
  ⟨generated_of_atomic, atomic_of_generated⟩

theorem Atomic.restricts {p q : Position m G H} (hp : Atomic p) (hqp : Restricts q p) :
    Atomic q := by
  obtain ⟨S, T, e, he⟩ := hp
  exact ⟨S, T, e, fun i g h hmark => he i g h (hqp i g h hmark)⟩

theorem Atomic.erase {p : Position m G H} (hp : Atomic p) (i : Fin m) : Atomic (erase p i) :=
  hp.restricts (erase_restricts p i)

/-- `Wins n p` means that Duplicator survives `n` further rounds.
Each round first removes the chosen pair and tests the retained marked
subgroups, then announces a bijection, then allows any element to be selected. -/
def Wins : ℕ → Position m G H → Prop
  | 0, _ => True
  | n + 1, p => ∀ i : Fin m, Atomic (erase p i) ∧
      ∃ f : G ≃ H, ∀ g : G, Wins n (place p i g (f g))

/-- Survival for every finite number of rounds. -/
def AllRounds (p : Position m G H) : Prop := ∀ n, Wins n p

/-- A local strategy invariant yields survival for every finite number of rounds. -/
theorem wins_of_invariant (I : Position m G H → Prop)
    (atomic : ∀ p, I p → Atomic p)
    (step : ∀ p, I p → ∀ i, ∃ f : G ≃ H, ∀ g, I (place p i g (f g)))
    {p : Position m G H} (hp : I p) : AllRounds p := by
  intro n
  induction n generalizing p with
  | zero => trivial
  | succ n ih =>
      intro i
      obtain ⟨f, hf⟩ := step p hp i
      exact ⟨(atomic p hp).erase i, f, fun g => ih (hf g)⟩

/-- The inverse of the announced bijection implements choices made in `H`. -/
theorem right_selection {n : ℕ} {p : Position m G H} {i : Fin m}
    {f : G ≃ H} (hf : ∀ g : G, Wins n (place p i g (f g))) (h : H) :
    Wins n (place p i (f.symm h) h) := by
  simpa using hf (f.symm h)

/-- Surviving more rounds implies surviving fewer rounds. -/
theorem wins_mono {p : Position m G H} {n k : ℕ} (hnk : n ≤ k) (hk : Wins k p) : Wins n p := by
  have down : ∀ j (q : Position m G H), Wins (j + 1) q → Wins j q := by
    intro j
    induction j with
    | zero => intro q hq; trivial
    | succ j ih =>
        intro q hq i
        obtain ⟨ha, f, hf⟩ := hq i
        exact ⟨ha, f, fun g => ih _ (hf g)⟩
  induction k generalizing n with
  | zero =>
      have hn : n = 0 := by omega
      subst n
      exact hk
  | succ k ih =>
      by_cases h : n ≤ k
      · exact ih h (down k p hk)
      · have hn : n = k + 1 := by omega
        subst n
        exact hk

/-- An infinite safety strategy is expressed by a post-fixed set of positions.
This definition uses the actual after-pickup atomic test. -/
def Winning (p : Position m G H) : Prop :=
  ∃ I : Position m G H → Prop, I p ∧
    ∀ q, I q → ∀ i : Fin m, Atomic (erase q i) ∧
      ∃ f : G ≃ H, ∀ g : G, I (place q i g (f g))

/-- Unfold a winning strategy for one selected pickup. -/
theorem winning_step {p : Position m G H} (hp : Winning p) (i : Fin m) :
    Atomic (erase p i) ∧ ∃ f : G ≃ H, ∀ g, Winning (place p i g (f g)) := by
  obtain ⟨I, hp, hI⟩ := hp
  obtain ⟨ha, f, hf⟩ := hI p hp i
  exact ⟨ha, f, fun g => ⟨I, hf g, hI⟩⟩

/-- A strategy invariant gives an infinite safety strategy directly. -/
theorem winning_of_invariant (I : Position m G H → Prop)
    (atomic : ∀ p, I p → Atomic p)
    (step : ∀ p, I p → ∀ i, ∃ f : G ≃ H, ∀ g, I (place p i g (f g)))
    {p : Position m G H} (hp : I p) : Winning p :=
  ⟨I, hp, fun q hq i => ⟨(atomic q hq).erase i, step q hq i⟩⟩

theorem allRounds_of_winning {p : Position m G H} (hp : Winning p) : AllRounds p := by
  obtain ⟨I, hp, hI⟩ := hp
  intro n
  induction n generalizing p with
  | zero => trivial
  | succ n ih =>
      intro i
      obtain ⟨ha, f, hf⟩ := hI p hp i
      exact ⟨ha, f, fun g => ih (hf g)⟩

/-- In a finite game, survival at every finite horizon supplies one common
choice of the announced bijection whose successors also survive every horizon. -/
theorem allRounds_step [Finite G] [Finite H] {p : Position m G H}
    (hp : AllRounds p) (i : Fin m) :
    Atomic (erase p i) ∧ ∃ f : G ≃ H, ∀ g : G, AllRounds (place p i g (f g)) := by
  classical
  letI := Fintype.ofFinite G
  letI := Fintype.ofFinite H
  refine ⟨(hp 1 i).1, ?_⟩
  by_contra hn
  have hbad : ∀ f : G ≃ H, ∃ n : ℕ, ¬ ∀ g, Wins n (place p i g (f g)) := by
    intro f
    by_contra hgood
    push Not at hgood
    apply hn
    exact ⟨f, fun g n => hgood n g⟩
  choose n hn using hbad
  let N : ℕ := Finset.univ.sup n
  obtain ⟨f, hf⟩ := (hp (N + 1) i).2
  apply hn f
  intro g
  exact wins_mono (Finset.le_sup (Finset.mem_univ f)) (hf g)

/-- The finite-horizon and infinite-strategy semantics agree for finite groups. -/
theorem winning_iff_allRounds [Finite G] [Finite H] (p : Position m G H) :
    Winning p ↔ AllRounds p := by
  constructor
  · exact allRounds_of_winning
  · intro hp
    exact ⟨AllRounds, hp, fun _ hq i => allRounds_step hq i⟩

end Groups

section Fiberwise
variable {X Y Z : Type*} [AddGroup Y]

/-- The single bijection announced in the shear strategy. Its displacement
may depend arbitrarily on `x`, and need not be linear on the whole space. -/
def fiberwiseShear (a : X → Y) : (X × Y × Z) ≃ (X × Y × Z) where
  toFun g := (g.1, g.2.1 + a g.1, g.2.2)
  invFun g := (g.1, g.2.1 - a g.1, g.2.2)
  left_inv g := by rcases g with ⟨x, y, z⟩; simp
  right_inv g := by rcases g with ⟨x, y, z⟩; simp

@[simp] theorem fiberwiseShear_apply (a : X → Y) (x : X) (y : Y) (z : Z) :
    fiberwiseShear a (x, y, z) = (x, y + a x, z) := rfl

@[simp] theorem fiberwiseShear_symm_apply (a : X → Y) (x : X) (y : Y) (z : Z) :
    (fiberwiseShear a).symm (x, y, z) = (x, y - a x, z) := rfl

end Fiberwise
end PebbleGame
end GroupWL
