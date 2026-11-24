import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Tactic

/-!
# Shared-color Weisfeiler--Leman refinement on groups

The recursive colors use one multiset of whole replacement vectors. In
particular, the replacement coordinates are not refined independently.
Version II initial colors record all group-word relations. Identification
below quantifies over every finite group, not only tensor groups.
-/
namespace GroupWL
namespace Refinement

universe u v w

inductive GroupWord (k : ℕ) where
  | one : GroupWord k
  | gen : Fin k → GroupWord k
  | mul : GroupWord k → GroupWord k → GroupWord k
  | inv : GroupWord k → GroupWord k
  deriving DecidableEq

def GroupWord.eval {k : ℕ} {G : Type u} [Group G] (a : Fin k → G) :
    GroupWord k → G
  | .one => 1
  | .gen i => a i
  | .mul s t => s.eval a * t.eval a
  | .inv s => (s.eval a)⁻¹

@[simp] theorem GroupWord.eval_hom {k : ℕ} {G : Type u} {H : Type v}
    [Group G] [Group H] (f : G →* H) (a : Fin k → G) (s : GroupWord k) :
    s.eval (f ∘ a) = f (s.eval a) := by
  induction s with
  | one => simp [GroupWord.eval]
  | gen i => rfl
  | mul s t hs ht => simp [GroupWord.eval, hs, ht]
  | inv s hs => simp [GroupWord.eval, hs]

/-- The type of an initial Version-I tuple, including equality and multiplication. -/
abbrev InitialI (k : ℕ) :=
  (Fin k → Fin k → Bool) × (Fin k → Fin k → Fin k → Bool)

noncomputable def initialI {G : Type u} [Group G] (k : ℕ) (a : Fin k → G) :
    InitialI k := by
  classical
  exact (fun i j => decide (a i = a j), fun i j l => decide (a i * a j = a l))

/-- Complete word type: equality of these colors is marked-subgroup equivalence. -/
noncomputable def initialII {G : Type u} [Group G] (k : ℕ) (a : Fin k → G) :
    GroupWord k → Bool := by
  classical
  exact fun s => decide (s.eval a = 1)

def Color (C : Type w) (k : ℕ) : ℕ → Type w
  | 0 => C
  | r + 1 => Color C k r × Multiset (Fin k → Color C k r)

noncomputable def color {A : Type u} [Fintype A] {C : Type w} {k : ℕ}
    (initial : (Fin k → A) → C) : (r : ℕ) → (Fin k → A) → Color C k r
  | 0, a => initial a
  | r + 1, a => (color initial r a,
      Finset.univ.val.map (fun x => fun i => color initial r (Function.update a i x)))

noncomputable def histogram {A : Type u} [Fintype A] {C : Type w} {k : ℕ}
    (initial : (Fin k → A) → C) (r : ℕ) : Multiset (Color C k r) :=
  Finset.univ.val.map (color initial r)

/-- Stable equivalence expressed without arbitrarily choosing color numbers. -/
def Equivalent {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    {C : Type w} {k : ℕ} (initialA : (Fin k → A) → C)
    (initialB : (Fin k → B) → C) : Prop :=
  ∀ r, histogram initialA r = histogram initialB r

private theorem map_univ_congr {A : Type u} {B : Type v} {C : Type w}
    [Fintype A] [Fintype B] (e : A ≃ B) (f : A → C) (g : B → C)
    (h : ∀ a, f a = g (e a)) :
    Finset.univ.val.map f = Finset.univ.val.map g := by
  calc
    _ = Finset.univ.val.map (g ∘ e) := by congr 1; funext a; exact h a
    _ = (Finset.univ.val.map e).map g := by rw [Multiset.map_map]
    _ = _ := by rw [Multiset.map_univ_val_equiv]

theorem color_equiv {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    {C : Type w} {k : ℕ} (e : A ≃ B)
    (initialA : (Fin k → A) → C) (initialB : (Fin k → B) → C)
    (h : ∀ a, initialA a = initialB (e ∘ a)) (r : ℕ) (a : Fin k → A) :
    color initialA r a = color initialB r (e ∘ a) := by
  induction r generalizing a with
  | zero => exact h a
  | succ r ih =>
    apply Prod.ext
    · exact ih a
    · apply map_univ_congr e
      intro x
      funext i
      rw [ih]
      congr 1
      funext j
      by_cases hj : j = i <;> simp [Function.update, hj]

theorem equivalent_of_initial_equiv {A : Type u} {B : Type v}
    [Fintype A] [Fintype B] {C : Type w} {k : ℕ} (e : A ≃ B)
    (initialA : (Fin k → A) → C) (initialB : (Fin k → B) → C)
    (h : ∀ a, initialA a = initialB (e ∘ a)) :
    Equivalent initialA initialB := by
  intro r
  apply map_univ_congr (Equiv.arrowCongr (Equiv.refl (Fin k)) e)
  intro a
  exact color_equiv e initialA initialB h r a

def EquivalentI (k : ℕ) (G : Type u) (H : Type v)
    [Group G] [Group H] [Fintype G] [Fintype H] : Prop :=
  Equivalent (initialI (G := G) k) (initialI (G := H) k)

def EquivalentII (k : ℕ) (G : Type u) (H : Type v)
    [Group G] [Group H] [Fintype G] [Fintype H] : Prop :=
  Equivalent (initialII (G := G) k) (initialII (G := H) k)

theorem initialI_equiv {G : Type u} {H : Type v} [Group G] [Group H]
    (e : G ≃* H) (k : ℕ) (a : Fin k → G) :
    initialI k a = initialI k (e ∘ a) := by
  classical
  apply Prod.ext
  · funext i j
    simp [initialI]
  · funext i j l
    simp [initialI, ← map_mul]

theorem initialII_equiv {G : Type u} {H : Type v} [Group G] [Group H]
    (e : G ≃* H) (k : ℕ) (a : Fin k → G) :
    initialII k a = initialII k (e ∘ a) := by
  classical
  funext s
  change decide (s.eval a = 1) = decide (s.eval (e.toMonoidHom ∘ a) = 1)
  rw [GroupWord.eval_hom]
  simp

theorem equivalentI_of_isomorphic {G : Type u} {H : Type v}
    [Group G] [Group H] [Fintype G] [Fintype H] (e : G ≃* H) (k : ℕ) :
    EquivalentI k G H :=
  equivalent_of_initial_equiv e.toEquiv _ _ (initialI_equiv e k)

theorem equivalentII_of_isomorphic {G : Type u} {H : Type v}
    [Group G] [Group H] [Fintype G] [Fintype H] (e : G ≃* H) (k : ℕ) :
    EquivalentII k G H :=
  equivalent_of_initial_equiv e.toEquiv _ _ (initialII_equiv e k)

/-- A first-order finite group represented on its full finite carrier. -/
structure FiniteGroup where
  Carrier : Type
  group : Group Carrier
  finite : Fintype Carrier

instance (G : FiniteGroup) : Group G.Carrier := G.group
instance (G : FiniteGroup) : Fintype G.Carrier := G.finite

/-- All comparison finite groups are included, without restricting their presentations. -/
def IdentifiesII (k : ℕ) (G : Type u) [Group G] [Fintype G] : Prop :=
  ∀ H : FiniteGroup, EquivalentII k G H.Carrier → Nonempty (G ≃* H.Carrier)

def IdentifiesI (k : ℕ) (G : Type u) [Group G] [Fintype G] : Prop :=
  ∀ H : FiniteGroup, EquivalentI k G H.Carrier → Nonempty (G ≃* H.Carrier)

/-- Equality of a color histogram already determines the size of the tuple space. -/
theorem card_eq_of_equivalent {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    {C : Type w} {k : ℕ} (hk : k ≠ 0)
    {initialA : (Fin k → A) → C} {initialB : (Fin k → B) → C}
    (h : Equivalent initialA initialB) : Fintype.card A = Fintype.card B := by
  have hc := congrArg Multiset.card (h 0)
  simp only [histogram, Multiset.card_map] at hc
  change Fintype.card (Fin k → A) = Fintype.card (Fin k → B) at hc
  simp only [Fintype.card_fun, Fintype.card_fin] at hc
  exact Nat.pow_left_injective hk hc

/-- Multiplication gadget vertices: one group node, and four fresh nodes per ordered pair. -/
abbrev GadgetVertex (G : Type u) := G ⊕ (G × G × Fin 4)

private def attachment {G : Type u} [Group G] (v g h : G) (j : Fin 4) : Prop :=
  (j = 0 ∧ v = g) ∨ (j = 1 ∧ v = h) ∨ (j = 3 ∧ v = g * h)

def gadgetAdj {G : Type u} [Group G] : GadgetVertex G → GadgetVertex G → Prop
  | .inl _, .inl _ => False
  | .inl v, .inr (g, h, j) => attachment v g h j
  | .inr (g, h, j), .inl v => attachment v g h j
  | .inr (g, h, i), .inr (g', h', j) =>
    g = g' ∧ h = h' ∧ (i.val + 1 = j.val ∨ j.val + 1 = i.val)

theorem gadgetAdj_symm {G : Type u} [Group G] (a b : GadgetVertex G) :
    gadgetAdj a b ↔ gadgetAdj b a := by
  cases a with
  | inl a => cases b <;> rfl
  | inr a =>
    cases b with
    | inl b => rfl
    | inr b => simp only [gadgetAdj]; aesop

theorem gadgetAdj_irrefl {G : Type u} [Group G] (a : GadgetVertex G) :
    ¬ gadgetAdj a a := by
  cases a with
  | inl a => simp [gadgetAdj]
  | inr a => simp [gadgetAdj]

noncomputable def graphInitial {A : Type u} (adj : A → A → Prop)
    (k : ℕ) (a : Fin k → A) : (Fin k → Fin k → Bool) × (Fin k → Fin k → Bool) := by
  classical
  exact (fun i j => decide (a i = a j), fun i j => decide (adj (a i) (a j)))

def NeighborColor : ℕ → Type
  | 0 => Unit
  | r + 1 => NeighborColor r × Multiset (NeighborColor r)

noncomputable def neighborColor {A : Type u} [Fintype A]
    (adj : A → A → Prop) : (r : ℕ) → A → NeighborColor r
  | 0, _ => ()
  | r + 1, a => by
    classical
    exact (neighborColor adj r a,
      (Finset.univ.filter (adj a)).val.map (neighborColor adj r))

/-- Version III restricts final histograms to group elements, while refinement
runs on the entire multiplication graph. -/
noncomputable def graphGroupHistogram {G : Type u} [Group G] [Fintype G]
    (k r : ℕ) :=
  Finset.univ.val.map (fun a : Fin k → G =>
    color (graphInitial (gadgetAdj (G := G)) k) r (Sum.inl ∘ a))

noncomputable def neighborGroupHistogram {G : Type u} [Group G] [Fintype G]
    (r : ℕ) : Multiset (NeighborColor r) :=
  Finset.univ.val.map (fun a : G => neighborColor gadgetAdj r (Sum.inl a))

def EquivalentIII (k : ℕ) (G : Type u) (H : Type v)
    [Group G] [Group H] [Fintype G] [Fintype H] : Prop :=
  if k = 1 then ∀ r, neighborGroupHistogram (G := G) r = neighborGroupHistogram (G := H) r
  else ∀ r, graphGroupHistogram (G := G) k r = graphGroupHistogram (G := H) k r

inductive Version where
  | one | two | three
  deriving DecidableEq, Fintype

def GroupEquivalent (version : Version) (k : ℕ) (G : Type u) (H : Type v)
    [Group G] [Group H] [Fintype G] [Fintype H] : Prop :=
  match version with
  | .one => EquivalentI k G H
  | .two => EquivalentII k G H
  | .three => EquivalentIII k G H

/-- No restriction to the output of the reduction is placed on the comparison group. -/
def Identifies (version : Version) (k : ℕ) (G : Type u) [Group G] [Fintype G] : Prop :=
  ∀ H : FiniteGroup, GroupEquivalent version k G H.Carrier →
    Nonempty (G ≃* H.Carrier)

end Refinement
end GroupWL
