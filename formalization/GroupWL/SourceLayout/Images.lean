import GroupWL.SourceLayout.RingEquations

namespace GroupWL.SourceLayout.ComparisonData

open scoped BigOperators

variable {F T E : Type*} [Field F] {r L : ℕ}
variable (C : ComparisonData F T E r)

abbrev RealAddress (_C : ComparisonData F T E r) := Fin r → Bool
abbrev ImageSets := ∀ t : T, C.RealAddress → Set (Fin (C.dim t) → F)

def sourceAddress {e : E} (a : C.DomainAddress e) : C.RealAddress := fun i => (a i).val
def targetAddress {e : E} (a : C.DomainAddress e) : C.RealAddress :=
  fun i => C.permutation e i (a i).val

def comparisonDelta (beta : C.Block L → F) (e : E) (a : C.DomainAddress e) : F :=
  C.linkDelta beta (.first e) a + (∑ i : Fin L, C.linkDelta beta (.middle e i) a) +
    C.linkDelta beta (.last e) a

/-- The exact scalar-image predicate extracted by the retained-ring argument. -/
structure ScalarImages (beta : C.Block L → F) (Q : C.ImageSets) : Prop where
  nonempty : ∀ t a, (Q t a).Nonempty
  comparison : ∀ e (a : C.DomainAddress e),
    C.sourceForm e '' Q (C.source e) (C.sourceAddress a) =
      (fun z => C.comparisonDelta beta e a + z) ''
        (C.targetForm e '' Q (C.target e) (C.targetAddress a))

/-- The corresponding predicate when the shift of each whole wire is constant. -/
structure ConstantScalarImages (b : E → F) (Q : C.ImageSets) : Prop where
  nonempty : ∀ t a, (Q t a).Nonempty
  comparison : ∀ e (a : C.DomainAddress e),
    C.sourceForm e '' Q (C.source e) (C.sourceAddress a) =
      (fun z => b e + z) '' (C.targetForm e '' Q (C.target e) (C.targetAddress a))

def realRing (z : C.Assignment L) (t : T) (a : C.RealAddress) : Fin (C.dim t) → F :=
  C.ringValue z (.inl t) (fun i => ⟨a i, Finset.mem_univ _⟩)

def internalRing (z : C.Assignment L) (e : E) (j : Fin (L + 1)) (a : C.DomainAddress e) : F :=
  C.ringValue z (.inr (e, j)) a

private theorem sum_neighbor_differences (f : Fin (L + 1) → F) :
    (∑ i : Fin L, (f i.castSucc - f i.succ)) = f 0 - f (Fin.last L) := by
  have h := (Fin.sum_univ_castSucc f).symm.trans (Fin.sum_univ_succ f)
  rw [Finset.sum_sub_distrib]
  exact sub_eq_sub_iff_add_eq_add.mpr h

variable [Fintype T] [Fintype E]

/-- Summing all squares around the rows and along a complete private wire
recovers exactly the original real-type comparison. -/
theorem comparison_equation_of_solution (z : C.Assignment L) (beta : C.Block L → F)
    (hz : (C.affineSystem (L := L)).linearMap z = beta) (e : E) (a : C.DomainAddress e) :
    C.sourceForm e (C.realRing z (C.source e) (C.sourceAddress a)) -
      C.targetForm e (C.realRing z (C.target e) (C.targetAddress a)) = C.comparisonDelta beta e a := by
  have hfirst := C.ring_equation_of_solution z beta hz (.first e) a
  change C.sourceForm e (C.realRing z (C.source e) (C.sourceAddress a)) -
    C.internalRing z e 0 a = C.linkDelta beta (.first e) a at hfirst
  have hmiddle (i : Fin L) := C.ring_equation_of_solution z beta hz (.middle e i) a
  change ∀ i : Fin L, C.internalRing z e i.castSucc a - C.internalRing z e i.succ a =
    C.linkDelta beta (.middle e i) a at hmiddle
  have hlast := C.ring_equation_of_solution z beta hz (.last e) a
  change C.internalRing z e (Fin.last L) a -
    C.targetForm e (C.realRing z (C.target e) (C.targetAddress a)) =
      C.linkDelta beta (.last e) a at hlast
  calc
    _ = (C.sourceForm e (C.realRing z (C.source e) (C.sourceAddress a)) - C.internalRing z e 0 a) +
      (∑ i : Fin L, (C.internalRing z e i.castSucc a - C.internalRing z e i.succ a)) +
      (C.internalRing z e (Fin.last L) a -
        C.targetForm e (C.realRing z (C.target e) (C.targetAddress a))) := by
      rw [sum_neighbor_differences (fun j : Fin (L + 1) => C.internalRing z e j a)]
      abel
    _ = C.comparisonDelta beta e a := by
      rw [hfirst, hlast]
      unfold comparisonDelta
      congr 2
      exact Finset.sum_congr rfl (fun i _ => hmiddle i)

end GroupWL.SourceLayout.ComparisonData
