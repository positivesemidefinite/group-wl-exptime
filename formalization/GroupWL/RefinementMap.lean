import GroupWL.Refinement

/-! Functoriality of shared colors, and the actual Version-II-to-I comparison. -/
namespace GroupWL.Refinement

universe u v w w'

noncomputable def mapColor {C : Type w} {D : Type w'} {k : ℕ} (f : C → D) :
    (r : ℕ) → Color C k r → Color D k r
  | 0, c => f c
  | r + 1, c => (mapColor f r c.1,
      c.2.map (fun v i => mapColor f r (v i)))

theorem mapColor_color {A : Type u} [Fintype A] {C : Type w} {D : Type w'}
    {k : ℕ} (f : C → D) (initial : (Fin k → A) → C) (r : ℕ) (a : Fin k → A) :
    mapColor f r (color initial r a) = color (f ∘ initial) r a := by
  induction r generalizing a with
  | zero => rfl
  | succ r ih =>
    simp only [color, mapColor, ih, Multiset.map_map, Function.comp_def]

theorem mapColor_histogram {A : Type u} [Fintype A] {C : Type w} {D : Type w'}
    {k : ℕ} (f : C → D) (initial : (Fin k → A) → C) (r : ℕ) :
    (histogram initial r).map (mapColor f r) = histogram (f ∘ initial) r := by
  simp only [histogram, Multiset.map_map, Function.comp_def, mapColor_color]

theorem Equivalent.map_initial {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    {C : Type w} {D : Type w'} {k : ℕ}
    {initialA : (Fin k → A) → C} {initialB : (Fin k → B) → C}
    (h : Equivalent initialA initialB) (f : C → D) :
    Equivalent (f ∘ initialA) (f ∘ initialB) := by
  intro r
  rw [← mapColor_histogram f initialA, ← mapColor_histogram f initialB, h r]

def wordTypeToInitialI {k : ℕ} (c : GroupWord k → Bool) : InitialI k :=
  (fun i j => c (.mul (.gen i) (.inv (.gen j))),
   fun i j l => c (.mul (.mul (.gen i) (.gen j)) (.inv (.gen l))))

theorem wordTypeToInitialI_initialII {G : Type u} [Group G]
    (k : ℕ) (a : Fin k → G) : wordTypeToInitialI (initialII k a) = initialI k a := by
  classical
  simp only [wordTypeToInitialI, initialII, initialI, GroupWord.eval, mul_inv_eq_one]

/-- The same-dimension Version-I comparison is proved for the concrete color definitions. -/
theorem equivalentI_of_equivalentII {G : Type u} {H : Type v}
    [Group G] [Group H] [Fintype G] [Fintype H] {k : ℕ}
    (h : EquivalentII k G H) : EquivalentI k G H := by
  have hm := Equivalent.map_initial h (@wordTypeToInitialI k)
  have hG : wordTypeToInitialI ∘ initialII (G := G) k = initialI (G := G) k := by
    funext a
    exact wordTypeToInitialI_initialII k a
  have hH : wordTypeToInitialI ∘ initialII (G := H) k = initialI (G := H) k := by
    funext a
    exact wordTypeToInitialI_initialII k a
  rw [hG, hH] at hm
  exact hm

end GroupWL.Refinement
