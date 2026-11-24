import GroupWL.Wrapping
import GroupWL.CyclicLifting

namespace GroupWL.SourceLayout

variable {K A V : Type*} [AddCommGroup K]

theorem cutPotential_step_all (n : ℕ) (a : K) (b i : Fin (n + 1)) :
    Wrapping.cutPotential n a b (finRotate (n + 1) i) - Wrapping.cutPotential n a b i =
      Wrapping.seamMarker n a i - if i = b then a else 0 := by
  by_cases hi : i = b
  · subst i
    by_cases hb : b = Fin.last n
    · subst b
      simp [Wrapping.cutPotential, Wrapping.seamMarker]
    · simp [Wrapping.cutPotential, Wrapping.seamMarker, hb, coe_finRotate_of_ne_last hb]
  · rw [if_neg hi, sub_zero]
    exact Wrapping.cutPotential_step n a b i hi

noncomputable def labelledCutPotential {n : ℕ} (a : K) (b : Fin (n + 3))
    (right : Fin (n + 3) → A) (i : Fin (n + 3)) (z : A) : K := by
  classical
  exact Wrapping.cutPotential (n + 2) a b i +
    if i = finRotate (n + 3) b ∧ z = right b then a else 0

/-- A mismatch between the incoming and outgoing label opens the cycle at
that boundary, so its marker has an explicit potential. -/
theorem labelledCutPotential_step {n : ℕ} (a : K) (b : Fin (n + 3))
    (left right : Fin (n + 3) → A) (hmismatch : right b ≠ left (finRotate (n + 3) b))
    (i : Fin (n + 3)) :
    labelledCutPotential a b right (finRotate (n + 3) i) (right i) -
      labelledCutPotential a b right i (left i) = Wrapping.seamMarker (n + 2) a i := by
  classical
  have hin : (finRotate (n + 3) i = finRotate (n + 3) b ∧ right i = right b) ↔ i = b := by
    constructor
    · intro h
      exact (finRotate (n + 3)).injective h.1
    · rintro rfl
      exact ⟨rfl, rfl⟩
  have hout : ¬ (i = finRotate (n + 3) b ∧ left i = right b) := by
    rintro ⟨rfl, h⟩
    exact hmismatch h.symm
  unfold labelledCutPotential
  simp only [hin, if_neg hout, add_zero]
  calc
    _ = (Wrapping.cutPotential (n + 2) a b (finRotate (n + 3) i) -
        Wrapping.cutPotential (n + 2) a b i) + (if i = b then a else 0) := by abel
    _ = Wrapping.seamMarker (n + 2) a i := by
      rw [cutPotential_step_all]
      abel

/-- If each row has one prescribed pair of horizontal labels and vertical
edges preserve labels, a wrapping walk forces the row labels to fit together. -/
theorem labels_match_of_wrapping {n : ℕ} {G : SimpleGraph V}
    (L : Wrapping.Layout (K := K) (n + 2) G) (label : V → A)
    (left right : Fin (n + 3) → A)
    (hvertical : ∀ u v, G.Adj u v → L.row u = L.row v → label u = label v)
    (hforward : ∀ u v, G.Adj u v → L.row v = finRotate (n + 3) (L.row u) →
      label u = left (L.row u) ∧ label v = right (L.row u))
    (hwrap : L.Wraps) (b : Fin (n + 3)) : right b = left (finRotate (n + 3) b) := by
  classical
  by_contra hmismatch
  let s : V → K := fun v => labelledCutPotential L.seam b right (L.row v) (label v)
  have hs (u v : V) (huv : G.Adj u v) : L.marker u v = s v - s u := by
    rcases L.edge_kind u v huv with ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩
    · have hl := hvertical u v huv hr.symm
      simp only [s, hr, hl, hm, sub_self]
    · obtain ⟨hlu, hlv⟩ := hforward u v huv hr
      dsimp only [s]
      rw [hr, hlu, hlv, hm]
      exact (labelledCutPotential_step L.seam b left right hmismatch (L.row u)).symm
    · obtain ⟨hlv, hlu⟩ := hforward v u huv.symm hr
      dsimp only [s]
      rw [hr, hlu, hlv, hm]
      have hh := labelledCutPotential_step L.seam b left right hmismatch (L.row v)
      rw [← hh]
      abel
  have hi {u v : V} (p : G.Walk u v) : GraphPotentials.integral L.marker p = s v - s u := by
    induction p with
    | nil => simp [GraphPotentials.integral]
    | cons h p ih => simp only [GraphPotentials.integral_cons, hs _ _ h, ih]; abel
  obtain ⟨u, p, hp⟩ := hwrap
  exact hp (by simpa using hi p)

end GroupWL.SourceLayout
