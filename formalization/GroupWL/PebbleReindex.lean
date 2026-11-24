import GroupWL.RefinementGame
import GroupWL.RefinementMap

/-! # Forgetting pebble pairs and monotonicity of Version II -/
namespace GroupWL.PebbleReindex

open PebbleGame Refinement

universe u v
variable {G : Type u} {H : Type v} [Group G] [Group H] {m n : ℕ}

/-- Reindexing along an embedding keeps only the selected pair slots. -/
def restrictSlots (slot : Fin m ↪ Fin n) (p : Position n G H) : Position m G H :=
  p ∘ slot

theorem atomic_restrictSlots (slot : Fin m ↪ Fin n) {p : Position n G H} (hp : Atomic p) :
    Atomic (restrictSlots slot p) := by
  obtain ⟨S,T,e,he⟩ := hp
  exact ⟨S,T,e,fun i g h hmark => he (slot i) g h hmark⟩

@[simp] theorem restrictSlots_erase (slot : Fin m ↪ Fin n) (p : Position n G H) (i : Fin m) :
    restrictSlots slot (erase p (slot i)) = erase (restrictSlots slot p) i := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [restrictSlots]
  · have hs : slot j ≠ slot i := fun h => hji (slot.injective h)
    simp [restrictSlots,erase,Function.update,hji,hs]

@[simp] theorem restrictSlots_place (slot : Fin m ↪ Fin n) (p : Position n G H)
    (i : Fin m) (g : G) (h : H) :
    restrictSlots slot (place p (slot i) g h) = place (restrictSlots slot p) i g h := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [restrictSlots]
  · have hs : slot j ≠ slot i := fun h => hji (slot.injective h)
    simp [restrictSlots,place,Function.update,hji,hs]

/-- A winning strategy with more pairs induces one on any selected subset. -/
theorem winning_restrictSlots (slot : Fin m ↪ Fin n) {p : Position n G H} (hp : Winning p) :
    Winning (restrictSlots slot p) := by
  let I : Position m G H → Prop := fun q => ∃ p, Winning p ∧ q = restrictSlots slot p
  refine ⟨I,⟨p,hp,rfl⟩,?_⟩
  rintro q ⟨p,hp,rfl⟩ i
  obtain ⟨ha,f,hf⟩ := winning_step hp (slot i)
  refine ⟨?_,f,fun x => ⟨place p (slot i) x (f x),hf x,?_⟩⟩
  · simpa using atomic_restrictSlots slot ha
  · exact (restrictSlots_place slot p i x (f x)).symm

/-- Dimension monotonicity for the concrete shared-color Version-II relation. -/
theorem equivalentII_mono [Fintype G] [Fintype H] {k l : ℕ} (hkl : k ≤ l)
    (h : EquivalentII l G H) : EquivalentII k G H := by
  have hw := RefinementGame.winning_empty_of_equivalentII h
  let slot : Fin (k+1) ↪ Fin (l+1) :=
    ⟨Fin.castLE (by omega),Fin.castLE_injective _⟩
  apply GameRefinement.equivalentII_of_winning_empty k
  exact winning_restrictSlots slot hw

theorem equivalentI_of_equivalentII_of_le [Fintype G] [Fintype H] {k l : ℕ} (hkl : k ≤ l)
    (h : EquivalentII l G H) : EquivalentI k G H :=
  Refinement.equivalentI_of_equivalentII (equivalentII_mono hkl h)

theorem identifiesII_mono [Fintype G] {k l : ℕ} (hkl : k ≤ l) (h : IdentifiesII k G) :
    IdentifiesII l G := by
  intro H hH
  exact h H (equivalentII_mono hkl hH)

end GroupWL.PebbleReindex
