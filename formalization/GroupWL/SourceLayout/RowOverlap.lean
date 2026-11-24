import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace GroupWL.SourceLayout.RowOverlap

variable {B : Type*} [DecidableEq B] {r : ℕ}

/-- In a union of at most `r+1` blocks, a set of `r` blocks omits at most one
block of any other subset of that union. -/
theorem lost_card_le_one (R₁ R₂ T : Finset B)
    (h₁ : R₁ ⊆ T) (h₂ : R₂ ⊆ T) (hR₂ : R₂.card = r) (hT : T.card ≤ r + 1) :
    (R₁ \ R₂).card ≤ 1 := by
  have hu : (R₁ ∪ R₂).card ≤ T.card :=
    Finset.card_le_card (Finset.union_subset h₁ h₂)
  have hs := Finset.card_sdiff_add_card R₁ R₂
  omega

/-- Among any two distinct rows represented by the first ring, at least one
is represented by a block shared with the second ring. -/
theorem common_block_covers_pair (R₁ R₂ T : Finset B)
    (h₁ : R₁ ⊆ T) (h₂ : R₂ ⊆ T) (hR₂ : R₂.card = r) (hT : T.card ≤ r + 1)
    (row : B → Fin r) (hrows : ∀ i, ∃ b ∈ R₁, row b = i)
    (i j : Fin r) (hij : i ≠ j) :
    ∃ b ∈ R₁ ∩ R₂, row b = i ∨ row b = j := by
  obtain ⟨a, ha, hai⟩ := hrows i
  obtain ⟨b, hb, hbj⟩ := hrows j
  by_cases ha₂ : a ∈ R₂
  · exact ⟨a, Finset.mem_inter.mpr ⟨ha, ha₂⟩, Or.inl hai⟩
  by_cases hb₂ : b ∈ R₂
  · exact ⟨b, Finset.mem_inter.mpr ⟨hb, hb₂⟩, Or.inr hbj⟩
  have hab := (Finset.card_le_one.mp (lost_card_le_one R₁ R₂ T h₁ h₂ hR₂ hT))
    a (Finset.mem_sdiff.mpr ⟨ha, ha₂⟩) b (Finset.mem_sdiff.mpr ⟨hb, hb₂⟩)
  exact False.elim (hij (hai.symm.trans ((congrArg row hab).trans hbj)))

/-- An injective row assignment on exactly `r` blocks represents all rows. -/
theorem rows_surjective_of_card (R : Finset B) (hR : R.card = r)
    (row : B → Fin r) (hinj : Set.InjOn row R) :
    ∀ i, ∃ b ∈ R, row b = i := by
  have hc : (R.image row).card = r := by rw [Finset.card_image_iff.mpr hinj, hR]
  have he : R.image row = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simpa using hc.ge)
  intro i
  exact Finset.mem_image.mp (he ▸ Finset.mem_univ i)

theorem common_block_covers_pair_of_injective (R₁ R₂ T : Finset B)
    (h₁ : R₁ ⊆ T) (h₂ : R₂ ⊆ T) (hR₁ : R₁.card = r) (hR₂ : R₂.card = r)
    (hT : T.card ≤ r + 1) (row : B → Fin r) (hinj : Set.InjOn row R₁)
    (i j : Fin r) (hij : i ≠ j) :
    ∃ b ∈ R₁ ∩ R₂, row b = i ∨ row b = j :=
  common_block_covers_pair R₁ R₂ T h₁ h₂ hR₂ hT row
    (rows_surjective_of_card R₁ hR₁ row hinj) i j hij

end GroupWL.SourceLayout.RowOverlap
