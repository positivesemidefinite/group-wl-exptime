import GroupWL.PebbleGame
import GroupWL.TensorGroup
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Exact local shear families give a bijective-game strategy

This is the game-theoretic part of the manuscript's forward theorem. The
existence of an exact family is a named premise; constructing it from the
affine source and the relative obstruction duality is a separate obligation.
No affine or linear form is required of Duplicator's announced bijection.
-/

namespace GroupWL
namespace ShearGame

open PebbleGame

universe u v w
variable {F : Type u} {X : Type v} {Z : Type w}
variable [Field F] [AddCommGroup X] [Module F X] [AddCommGroup Z] [Module F Z]
variable (Y : Submodule F (X →ₗ[F] Z)) (ε : AlternatingBilinearMap F X Z)

abbrev Source := TensorGroup (evaluationTwist Y AlternatingBilinearMap.zero)
abbrev Target := TensorGroup (evaluationTwist Y ε)

/-- Fiberwise translation, with an arbitrary displacement function. -/
def announcedShear (a : X → Y) : Source Y ≃ Target Y ε where
  toFun g := ⟨(g.fst.1, g.fst.2 + a g.fst.1), g.snd⟩
  invFun g := ⟨(g.fst.1, g.fst.2 - a g.fst.1), g.snd⟩
  left_inv g := by ext <;> simp
  right_inv g := by ext <;> simp

/-- Finite input sets index global linear representatives of the local shears.
Only their restriction to the span of the index set matters. -/
structure ExactFamily (m : ℕ) [DecidableEq X] where
  maps : Finset X → Set (X →ₗ[F] Y)
  empty_nonempty : (maps ∅).Nonempty
  local_law : ∀ (s : Finset X), s.card ≤ m → ∀ α ∈ maps s,
    ∀ x ∈ Submodule.span F (s : Set X), ∀ x' ∈ Submodule.span F (s : Set X),
      shearCoboundary Y α x x' = ε x x'
  restrict : ∀ (s t : Finset X), s ⊆ t → t.card ≤ m → ∀ α ∈ maps t,
    ∃ β ∈ maps s, ∀ x ∈ s, β x = α x
  extend : ∀ (s : Finset X), s.card < m → ∀ α ∈ maps s, ∀ x : X,
    ∃ β ∈ maps (insert x s), ∀ z ∈ s, β z = α z

variable {Y ε} {m : ℕ} [DecidableEq X]

/-- The pebbled response to each element is its image under one local shear. -/
def Matches (α : X →ₗ[F] Y) (p : Position m (Source Y) (Target Y ε)) : Prop :=
  ∀ i g h, p i = some (g,h) → h = evaluationShear Y α ε g

/-- The invariant retains one exact-family witness on all occupied inputs. -/
def Invariant (P : ExactFamily Y ε m) (p : Position m (Source Y) (Target Y ε)) : Prop :=
  ∃ α ∈ P.maps (support (fun g : Source Y => g.fst.1) p), Matches α p

private theorem matches_restrict {p q : Position m (Source Y) (Target Y ε)}
    {α β : X →ₗ[F] Y} (hqp : Restricts q p) (hα : Matches α p)
    (hβ : ∀ x ∈ support (fun g : Source Y => g.fst.1) q, β x = α x) : Matches β q := by
  intro i g h hmark
  rw [hα i g h (hqp i g h hmark)]
  have heq := hβ g.fst.1 (mem_support.mpr ⟨i, g, h, hmark, rfl⟩)
  change (⟨(g.fst.1, g.fst.2 + α g.fst.1), g.snd⟩ : Target Y ε) =
    ⟨(g.fst.1, g.fst.2 + β g.fst.1), g.snd⟩
  rw [heq]

theorem invariant_erase (P : ExactFamily Y ε m)
    {p : Position m (Source Y) (Target Y ε)} (hp : Invariant P p) (i : Fin m) :
    Invariant P (erase p i) := by
  obtain ⟨α, hα, hmatch⟩ := hp
  obtain ⟨β, hβ, hagree⟩ := P.restrict _ _
    (support_mono _ (erase_restricts p i)) (card_support_le _ p) α hα
  exact ⟨β, hβ, matches_restrict (erase_restricts p i) hmatch hagree⟩

/-- The crucial order of quantifiers: a single announced bijection works for
all subsequent choices, although each input coordinate has its own extension. -/
theorem invariant_step (P : ExactFamily Y ε m)
    {p : Position m (Source Y) (Target Y ε)} (hp : Invariant P p) (i : Fin m) :
    ∃ f : Source Y ≃ Target Y ε, ∀ g : Source Y, Invariant P (place p i g (f g)) := by
  classical
  obtain ⟨α, hα, hmatch⟩ := invariant_erase P hp i
  let s := support (fun g : Source Y => g.fst.1) (erase p i)
  have hs : s.card < m := card_support_erase_lt _ p i
  have hext : ∀ x : X, ∃ β ∈ P.maps (insert x s), ∀ z ∈ s, β z = α z :=
    fun x => P.extend s hs α hα x
  choose β hβ hagree using hext
  let f := announcedShear Y ε (fun x => β x x)
  refine ⟨f, fun g => ?_⟩
  refine ⟨β g.fst.1, ?_, ?_⟩
  · rw [support_place]
    exact hβ g.fst.1
  · intro j g' h' hmark
    by_cases hji : j = i
    · subst j
      simp only [place_self, Option.some.injEq, Prod.mk.injEq] at hmark
      rcases hmark with ⟨rfl, rfl⟩
      rfl
    · have hold : erase p i j = some (g',h') := by
        simpa [place_ne p i j g (f g) hji, erase_ne p i j hji] using hmark
      have hg's : g'.fst.1 ∈ s := mem_support.mpr ⟨j, g', h', hold, rfl⟩
      rw [hmatch j g' h' hold]
      change (⟨(g'.fst.1, g'.fst.2 + α g'.fst.1), g'.snd⟩ : Target Y ε) =
        ⟨(g'.fst.1, g'.fst.2 + β g.fst.1 g'.fst.1), g'.snd⟩
      rw [hagree g.fst.1 g'.fst.1 hg's]

/-- Exact-family witnesses preserve the full marked-subgroup atomic type. -/
theorem invariant_atomic (P : ExactFamily Y ε m)
    {p : Position m (Source Y) (Target Y ε)} (hp : Invariant P p) : Atomic p := by
  obtain ⟨α, hα, hmatch⟩ := hp
  let s := support (fun g : Source Y => g.fst.1) p
  let E := Submodule.span F (s : Set X)
  let e := localShearMulEquiv Y α ε E (P.local_law s (card_support_le _ p) α hα)
  refine ⟨inputSubgroup Y AlternatingBilinearMap.zero E, inputSubgroup Y ε E, e, ?_⟩
  intro i g h hmark
  have hg : g.fst.1 ∈ E := Submodule.subset_span (mem_support.mpr ⟨i,g,h,hmark,rfl⟩)
  have hh : h.fst.1 ∈ E := by rw [hmatch i g h hmark]; exact hg
  refine ⟨hg, hh, ?_⟩
  apply Subtype.ext
  exact (hmatch i g h hmark).symm

/-- The exact local shear families supply a strategy for every finite number
of rounds of the actual marked-subgroup bijective game. -/
theorem allRounds_of_exactFamily (P : ExactFamily Y ε m) :
    AllRounds (empty : Position m (Source Y) (Target Y ε)) := by
  apply wins_of_invariant (Invariant P)
    (fun _ hp => invariant_atomic P hp)
    (fun _ hp i => invariant_step P hp i)
  obtain ⟨α, hα⟩ := P.empty_nonempty
  refine ⟨α, ?_, ?_⟩
  · simpa using hα
  · intro i g h hmark
    simp [empty] at hmark

/-- The same invariant is an infinite strategy, with the after-pickup convention. -/
theorem winning_of_exactFamily (P : ExactFamily Y ε m) :
    Winning (empty : Position m (Source Y) (Target Y ε)) := by
  apply winning_of_invariant (Invariant P)
    (fun _ hp => invariant_atomic P hp)
    (fun _ hp i => invariant_step P hp i)
  obtain ⟨α, hα⟩ := P.empty_nonempty
  refine ⟨α, ?_, ?_⟩
  · simpa using hα
  · intro i g h hmark
    simp [empty] at hmark

/-- The subspace-indexed form used by the coherent-residual construction.
Global linear maps represent local maps; exactness compares their restrictions. -/
structure ExactSubspaceFamily (m : ℕ) where
  maps : Submodule F X → Set (X →ₗ[F] Y)
  bot_nonempty : (maps ⊥).Nonempty
  local_law : ∀ E : Submodule F X, Module.finrank F E ≤ m → ∀ α ∈ maps E,
    ∀ x ∈ E, ∀ x' ∈ E, shearCoboundary Y α x x' = ε x x'
  restrict : ∀ E D : Submodule F X, E ≤ D → Module.finrank F D ≤ m → ∀ α ∈ maps D,
    ∃ β ∈ maps E, ∀ x ∈ E, β x = α x
  extend : ∀ E D : Submodule F X, E ≤ D → Module.finrank F D ≤ m → ∀ α ∈ maps E,
    ∃ β ∈ maps D, ∀ x ∈ E, β x = α x

/-- Spanning the finitely many retained directions converts the manuscript's
subspace families into the finite-support family used by the strategy proof. -/
def ExactSubspaceFamily.toExactFamily (P : ExactSubspaceFamily (Y := Y) (ε := ε) m) :
    ExactFamily Y ε m where
  maps s := P.maps (Submodule.span F (s : Set X))
  empty_nonempty := by simpa using P.bot_nonempty
  local_law s hs α hα := P.local_law _
    ((finrank_span_finset_le_card s).trans hs) α hα
  restrict s t hst ht α hα := by
    obtain ⟨β, hβ, hagree⟩ := P.restrict _ _
      (Submodule.span_mono (Finset.coe_subset.mpr hst))
      ((finrank_span_finset_le_card t).trans ht) α hα
    exact ⟨β, hβ, fun x hx => hagree x (Submodule.subset_span hx)⟩
  extend s hs α hα x := by
    have hdim : Module.finrank F (Submodule.span F ((insert x s : Finset X) : Set X)) ≤ m := by
      apply (finrank_span_finset_le_card (insert x s)).trans
      exact (Finset.card_insert_le x s).trans (by omega)
    obtain ⟨β, hβ, hagree⟩ := P.extend _ _
      (Submodule.span_mono (by intro z hz; exact Finset.mem_insert_of_mem hz)) hdim α hα
    exact ⟨β, hβ, fun z hz => hagree z (Submodule.subset_span hz)⟩

/-- The subspace-family formulation of the manuscript's bijective strategy. -/
theorem winning_of_exactSubspaceFamily
    (P : ExactSubspaceFamily (Y := Y) (ε := ε) m) :
    Winning (empty : Position m (Source Y) (Target Y ε)) :=
  winning_of_exactFamily P.toExactFamily

end ShearGame
end GroupWL
