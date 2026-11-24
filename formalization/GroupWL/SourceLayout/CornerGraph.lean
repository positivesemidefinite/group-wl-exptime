import GroupWL.SourceLayout.System
import GroupWL.SourceLayout.ActiveLinks

namespace GroupWL.SourceLayout.ComparisonData

variable {F T E : Type*} [Field F] {n L : ℕ}
variable (C : ComparisonData F T E (n + 3))
variable [Fintype T] [Fintype E]

def cornerRow (v : C.Corner L) : Fin (n + 3) := v.2.1

def blockRow : C.Block L → Fin (n + 3)
  | .inl h => h.2.1
  | .inr s => s.2.1

noncomputable def usedReadouts (S : Finset (C.Block L)) : Finset (C.Readout L) :=
  (C.affineSystem (L := L)).readouts S

def cornerGraph (S : Finset (C.Block L)) : SimpleGraph (C.Corner L) :=
  SimpleGraph.fromRel (fun u v => ∃ q ∈ C.usedReadouts S,
    u = C.readoutStart L q ∧ v = C.readoutEnd L q)

def edgeMarker (u v : C.Corner L) : F :=
  if C.cornerRow v = finRotate (n + 3) (C.cornerRow u) then
    Wrapping.seamMarker (n + 2) 1 (C.cornerRow u)
  else if C.cornerRow u = finRotate (n + 3) (C.cornerRow v) then
    -Wrapping.seamMarker (n + 2) 1 (C.cornerRow v)
  else 0

theorem marker_same_row {u v : C.Corner L} (h : C.cornerRow u = C.cornerRow v) :
    C.edgeMarker u v = 0 := by
  simp [edgeMarker, h, (CyclicLifting.finRotate_no_fixed n (C.cornerRow v)).symm]

theorem marker_forward {u v : C.Corner L}
    (h : C.cornerRow v = finRotate (n + 3) (C.cornerRow u)) :
    C.edgeMarker u v = Wrapping.seamMarker (n + 2) 1 (C.cornerRow u) := by
  simp [edgeMarker, h]

theorem marker_backward {u v : C.Corner L}
    (h : C.cornerRow u = finRotate (n + 3) (C.cornerRow v)) :
    C.edgeMarker u v = -Wrapping.seamMarker (n + 2) 1 (C.cornerRow v) := by
  have hn : C.cornerRow v ≠ finRotate (n + 3) (C.cornerRow u) := by
    intro hv
    rw [h] at hv
    exact CyclicLifting.finRotate_no_two_cycle n (C.cornerRow v) hv.symm
  unfold edgeMarker
  rw [if_neg hn, if_pos h]

theorem horizontal_row_eq_of_mem_scope (h : C.Horizontal L) (B : C.Block L)
    (hh : Sum.inl h ∈ C.scope L B) : h.2.1 = C.blockRow B := by
  classical
  cases B with
  | inl q =>
    have heq : h = q := by simpa [scope] using hh
    subst q
    rfl
  | inr s =>
    have heq : h = C.squareLeft L s ∨ h = C.squareRight L s := by
      simpa [scope] using hh
    rcases heq with rfl | rfl <;> rfl

theorem horizontal_owner (S : Finset (C.Block L)) (h : C.Horizontal L)
    (hh : Sum.inl h ∈ C.usedReadouts S) : ∃ B ∈ S, C.blockRow B = h.2.1 := by
  obtain ⟨B, hB, hhB⟩ := Finset.mem_biUnion.mp hh
  exact ⟨B, hB, (C.horizontal_row_eq_of_mem_scope h B hhB).symm⟩

/-- The actual corner graph has exactly the row-marker edge types needed by
the general wrapping theorem. -/
def wrappingLayout (S : Finset (C.Block L)) : Wrapping.Layout (K := F) (n + 2) (C.cornerGraph S) where
  row := C.cornerRow
  marker := C.edgeMarker
  seam := 1
  edge_kind := by
    intro u v huv
    rcases huv.2 with ⟨q, hq, rfl, rfl⟩ | ⟨q, hq, rfl, rfl⟩
    · cases q with
      | inl h => exact Or.inr (Or.inl ⟨rfl, C.marker_forward rfl⟩)
      | inr w => exact Or.inl ⟨rfl, C.marker_same_row rfl⟩
    · cases q with
      | inl h => exact Or.inr (Or.inr ⟨rfl, C.marker_backward rfl⟩)
      | inr w => exact Or.inl ⟨rfl, C.marker_same_row rfl⟩

theorem horizontal_crossing_has_owner (S : Finset (C.Block L))
    (u v : C.Corner L) (huv : (C.cornerGraph S).Adj u v)
    (hrow : C.cornerRow v = finRotate (n + 3) (C.cornerRow u)) :
    ∃ B ∈ S, C.blockRow B = C.cornerRow u := by
  rcases huv.2 with ⟨q, hq, rfl, rfl⟩ | ⟨q, hq, rfl, rfl⟩
  · cases q with
    | inl h => exact C.horizontal_owner S h hq
    | inr w =>
      exact False.elim ((CyclicLifting.finRotate_no_fixed n w.2.1) hrow.symm)
  · cases q with
    | inl h =>
      exact False.elim ((CyclicLifting.finRotate_no_two_cycle n h.2.1) hrow.symm)
    | inr w =>
      exact False.elim ((CyclicLifting.finRotate_no_fixed n w.2.1) hrow.symm)

/-- The manuscript's wrapping lower bound, instantiated for the actual
site-and-square readout graph. -/
theorem wrapping_card_bound (S : Finset (C.Block L))
    (hwrap : (C.wrappingLayout S).Wraps) : n + 3 ≤ S.card :=
  (C.wrappingLayout S).card_rows_le_card_blocks S C.blockRow
    (C.horizontal_crossing_has_owner S) hwrap

theorem wrapping_unique_block_per_row (S : Finset (C.Block L))
    (hwrap : (C.wrappingLayout S).Wraps) (hS : S.card = n + 3) (i : Fin (n + 3)) :
    ∃! B : {B // B ∈ S}, C.blockRow B.1 = i :=
  (C.wrappingLayout S).unique_block_per_row S C.blockRow
    (C.horizontal_crossing_has_owner S) hwrap hS i

end GroupWL.SourceLayout.ComparisonData
