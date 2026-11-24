import GroupWL.GraphPotentials

namespace GroupWL.SourceLayout

attribute [local instance] Classical.propDecidable

variable {V K : Type*} [AddCommGroup K] (G : SimpleGraph V) (m : V → V → K)

def NonwrappingAt (u : V) : Prop := ∀ p : G.Walk u u, GraphPotentials.integral m p = 0

theorem nonwrappingAt_of_walk {u v : V} (p : G.Walk u v) (hu : NonwrappingAt G m u) :
    NonwrappingAt G m v := by
  intro q
  have h0 := hu (p.append p.reverse)
  have h1 := hu (p.append (q.append p.reverse))
  simp only [GraphPotentials.integral_append] at h0 h1
  calc
    GraphPotentials.integral m q =
      (GraphPotentials.integral m p +
        (GraphPotentials.integral m q + GraphPotentials.integral m p.reverse)) -
      (GraphPotentials.integral m p + GraphPotentials.integral m p.reverse) := by abel
    _ = 0 := by rw [h0, h1, sub_self]

theorem nonwrappingAt_iff_of_walk {u v : V} (p : G.Walk u v) :
    NonwrappingAt G m u ↔ NonwrappingAt G m v :=
  ⟨nonwrappingAt_of_walk G m p, nonwrappingAt_of_walk G m p.reverse⟩

/-- Remove marker contributions on wrapping components. -/
noncomputable def nonwrappingMarker (u v : V) : K :=
  if NonwrappingAt G m u then m u v else 0

theorem integral_nonwrappingMarker {u v : V} (p : G.Walk u v) :
    GraphPotentials.integral (nonwrappingMarker G m) p =
      if NonwrappingAt G m u then GraphPotentials.integral m p else 0 := by
  classical
  induction p with
  | nil => simp [GraphPotentials.integral]
  | @cons u v w h p ih =>
    have heq := nonwrappingAt_iff_of_walk G m h.toWalk
    simp only [GraphPotentials.integral_cons, nonwrappingMarker, ih]
    by_cases hu : NonwrappingAt G m u
    · simp [hu, heq.mp hu]
    · have hv : ¬ NonwrappingAt G m v := fun hv => hu (heq.mpr hv)
      simp [hu, hv]

/-- One global potential simultaneously gives the correct marker differences
on every nonwrapping component. Wrapping components have zero modified marker. -/
theorem exists_nonwrapping_potential : ∃ s : V → K, ∀ u v, G.Adj u v →
    (if NonwrappingAt G m u then m u v else 0) = s v - s u := by
  classical
  apply GraphPotentials.exists_potential_of_zero_closed_walks (nonwrappingMarker G m)
  intro u p
  rw [integral_nonwrappingMarker]
  by_cases hu : NonwrappingAt G m u
  · rw [if_pos hu, hu p]
  · rw [if_neg hu]

end GroupWL.SourceLayout
