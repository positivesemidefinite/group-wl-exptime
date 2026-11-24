import GroupWL.SourceLayout.Images

/-! # The actual comparison shift is a sum of adjacent-address rows -/
namespace GroupWL.SourceLayout.ComparisonData

open scoped BigOperators
variable {F T E : Type*} [Field F] {r L : ℕ} (C : ComparisonData F T E r)

/-- Extend each comparison's accumulated wire-row shift by zero outside the
active two-label domain. Its values are computed from the actual square charges. -/
noncomputable def comparisonRows (beta : C.Block L → F) (e : E) (i : Fin r) (u v : Bool) : F :=
  if hu : u ∈ C.domain e i then
    if hv : v ∈ C.domain e (finRotate r i) then
      beta (.inr ⟨.first e,i,⟨u,hu⟩,⟨v,hv⟩⟩) +
        (∑ k : Fin L, beta (.inr ⟨.middle e k,i,⟨u,hu⟩,⟨v,hv⟩⟩)) +
        beta (.inr ⟨.last e,i,⟨u,hu⟩,⟨v,hv⟩⟩)
    else 0
  else 0

@[simp] theorem comparisonRows_address (beta : C.Block L → F) (e : E)
    (a : C.DomainAddress e) (i : Fin r) :
    C.comparisonRows beta e i (a i).val (a (finRotate r i)).val =
      beta (.inr (C.squareAt (.first e) a i)) +
        (∑ k : Fin L, beta (.inr (C.squareAt (.middle e k) a i))) +
        beta (.inr (C.squareAt (.last e) a i)) := by
  simp only [comparisonRows, dif_pos (a i).property,
    dif_pos (a (finRotate r i)).property, squareAt]
  rfl

/-- The genuine whole-wire comparison shift has the row decomposition needed
by acceptance, without any independent row-representation hypothesis. -/
theorem comparisonDelta_eq_sum_rows (beta : C.Block L → F) (e : E) (a : C.DomainAddress e) :
    C.comparisonDelta beta e a =
      ∑ i, C.comparisonRows beta e i (a i).val (a (finRotate r i)).val := by
  simp_rw [comparisonRows_address]
  simp only [Finset.sum_add_distrib,comparisonDelta,linkDelta]
  congr 2
  rw [Finset.sum_comm]

end GroupWL.SourceLayout.ComparisonData
