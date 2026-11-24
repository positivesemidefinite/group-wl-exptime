import GroupWL.GraphPotentials
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Wrapping requires every row

This module isolates the row-counting part of the site-and-square argument.
It proves that a corner component with nonzero marker on a closed walk must
cross every cyclic row boundary. If every horizontal edge comes from a block
in its row, wrapping needs at least as many blocks as rows. At equality there
is exactly one block per row.

The separate statements about type supports being trees and agreement of
aligned address labels are not asserted here.
-/

namespace GroupWL
namespace Wrapping

variable {V K : Type*} [AddCommGroup K]

def seamMarker (n : ℕ) (a : K) (i : Fin (n + 1)) : K :=
  if i = Fin.last n then a else 0

/-- Cutting boundary `b` makes the seam marker an exact potential difference. -/
def cutPotential (n : ℕ) (a : K) (b i : Fin (n + 1)) : K :=
  if b.val < i.val then -a else 0

theorem cutPotential_step (n : ℕ) (a : K) (b i : Fin (n + 1)) (hi : i ≠ b) :
    cutPotential n a b (finRotate (n + 1) i) - cutPotential n a b i =
      seamMarker n a i := by
  by_cases hlast : i = Fin.last n
  · subst i
    have hb : b.val < n := by
      have hbne : b.val ≠ n := by
        intro h
        apply hi
        apply Fin.ext
        simpa using h.symm
      have := b.isLt
      omega
    simp [cutPotential, seamMarker, hb]
  · have hval : i.val ≠ b.val := fun h => hi (Fin.ext h)
    have heq : b.val < i.val + 1 ↔ b.val < i.val := by omega
    simp only [cutPotential, coe_finRotate_of_ne_last hlast, heq,
      seamMarker, if_neg hlast, sub_self]

/-- The three allowed oriented edge kinds of a cyclic corner graph. -/
structure Layout (n : ℕ) (G : SimpleGraph V) where
  row : V → Fin (n + 1)
  marker : V → V → K
  seam : K
  edge_kind : ∀ u v, G.Adj u v →
    (row v = row u ∧ marker u v = 0) ∨
    (row v = finRotate (n + 1) (row u) ∧ marker u v = seamMarker n seam (row u)) ∨
    (row u = finRotate (n + 1) (row v) ∧ marker u v = -seamMarker n seam (row v))

namespace Layout

variable {n : ℕ} {G : SimpleGraph V} (L : Layout (K := K) n G)

def Wraps : Prop := ∃ v, ∃ p : G.Walk v v, GraphPotentials.integral L.marker p ≠ 0

/-- If one row boundary is absent, the marker is globally exact. -/
theorem exact_of_missing_boundary (b : Fin (n + 1))
    (hmissing : ∀ u v, G.Adj u v → L.row u = b →
      L.row v ≠ finRotate (n + 1) b) :
    ∃ s : V → K, ∀ u v, G.Adj u v → L.marker u v = s v - s u := by
  refine ⟨fun v => cutPotential n L.seam b (L.row v), ?_⟩
  intro u v huv
  change L.marker u v = cutPotential n L.seam b (L.row v) - cutPotential n L.seam b (L.row u)
  rcases L.edge_kind u v huv with ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩
  · simp only [hr, hm, sub_self]
  · have hu : L.row u ≠ b := by
      intro h
      exact hmissing u v huv h (by simpa [h] using hr)
    rw [hm, hr]
    exact (cutPotential_step n L.seam b (L.row u) hu).symm
  · have hv : L.row v ≠ b := by
      intro h
      exact hmissing v u huv.symm h (by simpa [h] using hr)
    rw [hm, hr]
    have h := cutPotential_step n L.seam b (L.row v) hv
    rw [← h]
    abel

/-- Every row boundary is represented on any graph containing a wrapping walk. -/
theorem crosses_every_boundary (hwrap : L.Wraps) (b : Fin (n + 1)) :
    ∃ u v, G.Adj u v ∧ L.row u = b ∧ L.row v = finRotate (n + 1) b := by
  classical
  by_contra hcross
  have hmissing : ∀ u v, G.Adj u v → L.row u = b →
      L.row v ≠ finRotate (n + 1) b := by
    intro u v huv hu hv
    exact hcross ⟨u, v, huv, hu, hv⟩
  obtain ⟨s, hs⟩ := L.exact_of_missing_boundary b hmissing
  have hi {u v : V} (p : G.Walk u v) :
      GraphPotentials.integral L.marker p = s v - s u := by
    induction p with
    | nil => simp [GraphPotentials.integral]
    | cons h p ih => simp only [GraphPotentials.integral_cons, hs _ _ h, ih]; abel
  obtain ⟨v, p, hp⟩ := hwrap
  exact hp (by simpa using hi p)

variable {B : Type*}

/-- Assigning every horizontal readout to a block in its row forces a wrapping
block set to cover every row. A square can own two horizontal readouts, but
both belong to the same row. -/
theorem every_row_has_block (S : Finset B) (blockRow : B → Fin (n + 1))
    (hcover : ∀ u v, G.Adj u v → L.row v = finRotate (n + 1) (L.row u) →
      ∃ b ∈ S, blockRow b = L.row u)
    (hwrap : L.Wraps) (i : Fin (n + 1)) : ∃ b ∈ S, blockRow b = i := by
  obtain ⟨u, v, huv, hu, hv⟩ := L.crosses_every_boundary hwrap i
  obtain ⟨b, hb, hr⟩ := hcover u v huv (by simpa [hu] using hv)
  exact ⟨b, hb, hr.trans hu⟩

theorem blockRow_image_eq_univ (S : Finset B) (blockRow : B → Fin (n + 1))
    (hcover : ∀ u v, G.Adj u v → L.row v = finRotate (n + 1) (L.row u) →
      ∃ b ∈ S, blockRow b = L.row u)
    (hwrap : L.Wraps) : S.image blockRow = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro i
  obtain ⟨b, hb, hr⟩ := L.every_row_has_block S blockRow hcover hwrap i
  exact Finset.mem_image.mpr ⟨b, hb, hr⟩

/-- Wrapping requires at least one block in each of the `n+1` rows. -/
theorem card_rows_le_card_blocks (S : Finset B) (blockRow : B → Fin (n + 1))
    (hcover : ∀ u v, G.Adj u v → L.row v = finRotate (n + 1) (L.row u) →
      ∃ b ∈ S, blockRow b = L.row u)
    (hwrap : L.Wraps) : n + 1 ≤ S.card := by
  have h := Finset.card_image_le (s := S) (f := blockRow)
  rw [L.blockRow_image_eq_univ S blockRow hcover hwrap] at h
  simpa using h

/-- At the minimum block count there is exactly one block per row. -/
theorem unique_block_per_row (S : Finset B) (blockRow : B → Fin (n + 1))
    (hcover : ∀ u v, G.Adj u v → L.row v = finRotate (n + 1) (L.row u) →
      ∃ b ∈ S, blockRow b = L.row u)
    (hwrap : L.Wraps) (hcard : S.card = n + 1) (i : Fin (n + 1)) :
    ∃! b : {b // b ∈ S}, blockRow b.1 = i := by
  have hinj : Set.InjOn blockRow (↑S : Set B) :=
    Finset.injOn_of_card_image_eq (by
      rw [L.blockRow_image_eq_univ S blockRow hcover hwrap, hcard]
      simp)
  obtain ⟨b, hb, hr⟩ := L.every_row_has_block S blockRow hcover hwrap i
  refine ⟨⟨b, hb⟩, hr, ?_⟩
  intro c hc
  apply Subtype.ext
  exact hinj c.2 hb (hc.trans hr.symm)

end Layout
end Wrapping
end GroupWL
