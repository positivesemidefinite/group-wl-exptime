import GroupWL.SourceLayout.MinimalWrapping
import GroupWL.SourceLayout.RowOverlap

namespace GroupWL.SourceLayout.ComparisonData

variable {F T E : Type*} [Field F] {n L : ℕ}
variable (C : ComparisonData F T E (n + 3))
variable [Fintype T] [Fintype E]

theorem blockTags_of_compatible (cut : Cuts (E := E) (L := L))
    (S : Finset (C.Block L)) (t : T) (a : Fin (n + 3) → Bool)
    (ha : C.CompatibleAddress cut S t a) (B : C.Block L) (hB : B ∈ S) :
    C.blockTags cut B = ((t, a (C.blockRow B)),
      (t, a (finRotate (n + 3) (C.blockRow B)))) := by
  classical
  cases B with
  | inl h =>
    exact Prod.ext (ha (.inl h) (C.scope_subset_used hB (by simp [scope]))).1
      (ha (.inl h) (C.scope_subset_used hB (by simp [scope]))).2
  | inr s =>
    exact Prod.ext
      (ha (.inl (C.squareLeft L s)) (C.scope_subset_used hB (by simp [scope]))).1
      (ha (.inl (C.squareLeft L s)) (C.scope_subset_used hB (by simp [scope]))).2

/-- Two minimum wrapping sets inside `r+1` blocks determine the same aligned
root and address. Each coordinate is witnessed by a common adjacent row. -/
theorem compatible_addresses_eq_of_overlap (cut : Cuts (E := E) (L := L))
    (R₁ R₂ S : Finset (C.Block L)) (h₁ : R₁ ⊆ S) (h₂ : R₂ ⊆ S)
    (hwrap₁ : (C.wrappingLayout R₁).Wraps) (hcard₁ : R₁.card = n + 3)
    (hcard₂ : R₂.card = n + 3) (hS : S.card ≤ n + 4)
    (t₁ t₂ : T) (a₁ a₂ : Fin (n + 3) → Bool)
    (ha₁ : C.CompatibleAddress cut R₁ t₁ a₁)
    (ha₂ : C.CompatibleAddress cut R₂ t₂ a₂) : t₁ = t₂ ∧ a₁ = a₂ := by
  classical
  have hrows (i : Fin (n + 3)) : ∃ B ∈ R₁, C.blockRow B = i := by
    obtain ⟨B, hB, _⟩ := C.wrapping_unique_block_per_row R₁ hwrap₁ hcard₁ i
    exact ⟨B.val, B.property, hB⟩
  have hcoord (i : Fin (n + 3)) : (t₁, a₁ i) = (t₂, a₂ i) := by
    let j := (finRotate (n + 3)).symm i
    have hij : i ≠ j := by
      intro heq
      have hrot : finRotate (n + 3) i = i := by
        calc
          finRotate (n + 3) i = finRotate (n + 3) j := congrArg _ heq
          _ = i := Equiv.apply_symm_apply _ i
      exact CyclicLifting.finRotate_no_fixed n i hrot
    obtain ⟨B, hB, hr⟩ := RowOverlap.common_block_covers_pair R₁ R₂ S h₁ h₂ hcard₂ hS
      C.blockRow hrows i j hij
    have hb₁ := C.blockTags_of_compatible cut R₁ t₁ a₁ ha₁ B (Finset.mem_inter.mp hB).1
    have hb₂ := C.blockTags_of_compatible cut R₂ t₂ a₂ ha₂ B (Finset.mem_inter.mp hB).2
    have heq := hb₁.symm.trans hb₂
    rcases hr with hr | hr
    · simpa only [hr] using congrArg Prod.fst heq
    · have hn : finRotate (n + 3) (C.blockRow B) = i := by
        rw [hr]
        exact Equiv.apply_symm_apply _ i
      simpa only [hn] using congrArg Prod.snd heq
  exact ⟨congrArg Prod.fst (hcoord 0), funext (fun i => congrArg Prod.snd (hcoord i))⟩

end GroupWL.SourceLayout.ComparisonData
