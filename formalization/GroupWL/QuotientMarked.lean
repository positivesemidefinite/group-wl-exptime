import GroupWL.QuotientNaming
import GroupWL.PebbleTransport

/-! Exact quotient names at arbitrary pebble slots. Copying a marked element
into the formula's query slot is an actual announced-bijection move. -/
namespace GroupWL.CoordinateNames.QuotientNamingContext
open Refinement CountingLogic PebbleGame

variable {F X Z H : Type*} [Field F] [NeZero (2 : F)]
  [AddCommGroup X] [Module F X] [AddCommGroup Z] [Module F Z]
  [Group H] [Finite H]
  {Y : Submodule F (X →ₗ[F] Z)} {ε : AlternatingBilinearMap F X Z}
  [Finite (TensorGroup (evaluationTwist Y ε))] {n : ℕ}
  (C : QuotientNamingContext Y ε H n)

theorem quotient_query_four
    {pos : Position (n + 1) (TensorGroup (evaluationTwist Y ε)) H} (hp : Winning pos)
    (ha : ∀ i ∈ ({0, 1, 2} : Finset (Fin 9)),
      pos (C.slot i).castSucc = some (C.reference (C.slot i), C.opponent (C.slot i)))
    {g : TensorGroup (evaluationTwist Y ε)} {h : H}
    (hm : pos (C.slot 4).castSucc = some (g, h)) : C.quotient h = g.fst.1 := by
  have ht := C.quotient_word hp
    (Function.update C.reference (C.slot 4) g) (Function.update C.opponent (C.slot 4) h)
    (C.update_anchor C.reference 4 (by decide) g)
    (C.update_anchor C.opponent 4 (by decide) h)
    (.gen 4) (by decide) (by
      intro i hi
      simp only [wordVariables, Finset.mem_union, Finset.mem_singleton] at hi
      rcases hi with hi | rfl
      · rw [C.update_anchor C.reference 4 (by decide) g i hi,
          C.update_anchor C.opponent 4 (by decide) h i hi]
        exact ha i hi
      · simpa only [Function.update_self] using hm)
  simpa only [GroupWord.eval, Function.comp_apply, Function.update_self] using ht

/-- The anchor names determine the input quotient at every occupied slot,
including the after-pickup reserve and the anchor slots themselves. -/
theorem quotient_of_marked
    {pos : Position (n + 1) (TensorGroup (evaluationTwist Y ε)) H} (hp : Winning pos)
    (ha : ∀ j ∈ ({0, 1, 2} : Finset (Fin 9)),
      pos (C.slot j).castSucc = some (C.reference (C.slot j), C.opponent (C.slot j)))
    {i : Fin (n + 1)} {g : TensorGroup (evaluationTwist Y ε)} {h : H}
    (hm : pos i = some (g, h)) : C.quotient h = g.fst.1 := by
  by_cases hi4 : i = (C.slot 4).castSucc
  · exact C.quotient_query_four hp ha (hi4 ▸ hm)
  obtain ⟨f, hf⟩ := (winning_step hp (C.slot 4).castSucc).2
  obtain ⟨s, his, h4s⟩ : ∃ s : Fin (n + 1), i ≠ s ∧ (C.slot 4).castSucc ≠ s := by
    by_cases hi0 : i = (C.slot 0).castSucc
    · exact ⟨(C.slot 1).castSucc, hi0 ▸ C.slot_cast_ne (by decide), C.slot_cast_ne (by decide)⟩
    · exact ⟨(C.slot 0).castSucc, hi0, C.slot_cast_ne (by decide)⟩
  have he : h = f g := (hf g).marked_equal
    (by simpa only [place_ne _ _ _ _ _ hi4] using hm)
    (place_self _ _ _ _) s his h4s
  have hw : Winning (place pos (C.slot 4).castSucc g h) := by rw [he]; exact hf g
  apply C.quotient_query_four hw
  · intro j hj
    have hj4 : j ≠ 4 := by
      intro heq
      subst j
      exact (by decide : (4 : Fin 9) ∉ ({0, 1, 2} : Finset (Fin 9))) hj
    rw [place_ne _ _ _ _ _ (C.slot_cast_ne hj4)]
    exact ha j hj
  · exact place_self _ _ _ _

end GroupWL.CoordinateNames.QuotientNamingContext
