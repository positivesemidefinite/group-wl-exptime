import GroupWL.SourceLayout.WrappedShiftExtension

namespace GroupWL.SourceLayout.ComparisonData

variable {F T E : Type*} [Field F] {n L : ℕ}
variable (C : ComparisonData F T E (n + 3)) [Fintype T] [Fintype E]

/-- Every admissible local assignment extends to a larger block set within
the `r+1` budget, preserving all old readouts exactly. -/
theorem sourceFamily_extend (b : E → F) (Q : C.ImageSets)
    (hQ : C.ConstantScalarImages b Q) (S U : Finset (C.Block L))
    (hSU : S ⊆ U) (hU : U.card ≤ n + 4) (hL : U.card < L + 2)
    (z : C.Assignment L) (hz : z ∈ C.sourceFamily b Q S) :
    ∃ w ∈ C.sourceFamily b Q U, ∀ q ∈ C.usedReadouts S, w q = z q := by
  classical
  by_cases heq : S = U
  · subst U
    exact ⟨z, hz, fun _ _ => rfl⟩
  have hScard : S.card ≤ n + 3 := by
    have hlt : S.card < U.card := Finset.card_lt_card (ssubset_iff_subset_ne.mpr ⟨hSU, heq⟩)
    omega
  obtain ⟨old, h, M, ho, hadm, hagree⟩ := hz
  let new := C.cutsFor U hL
  have hn : C.UncutOn new U := C.active_not_cut U hL
  have hnS := hn.mono C hSU
  have hold : C.ShiftEquations S b (C.completedShift old h b) :=
    fun l hl => C.completedShift_equation old h b l (ho l hl)
  have hex : ∃ h' : ∀ t, Fin (C.dim t) → F, C.RootAdmissible Q new U h' ∧
      ∀ v : C.Corner L, ¬ NonwrappingAt (C.cornerGraph S) C.edgeMarker v →
        C.completedShift new h' b v.1 = C.completedShift old h b v.1 := by
    by_cases hw : (C.wrappingLayout S).Wraps
    · have hcard : S.card = n + 3 := le_antisymm hScard (C.wrapping_card_bound S hw)
      obtain ⟨h', hadm', hkeep⟩ := C.extend_wrapped_shifts b Q hQ S U hSU hcard hU hw old new ho hn h hadm
      exact ⟨h', hadm', fun v hv => hkeep v (C.usedCorner_of_wrappingAt S v hv)⟩
    · obtain ⟨h', hadm'⟩ := C.exists_admissible_shifts Q hQ.nonempty new U hn hU
      refine ⟨h', hadm', ?_⟩
      intro v hv
      obtain ⟨p, hp⟩ := not_forall.mp hv
      exact False.elim (hw ⟨v, p, hp⟩)
  obtain ⟨h', hadm', hkeep⟩ := hex
  have hnew : C.ShiftEquations S b (C.completedShift new h' b) :=
    fun l hl => C.completedShift_equation new h' b l (hnS l hl)
  obtain ⟨M', hM⟩ := C.gauge_extension S b (C.completedShift old h b)
    (C.completedShift new h' b) M hold hnew hkeep
  refine ⟨C.potentialAssignment (C.completedShift new h' b) M',
    ⟨new, h', M', hn, hadm', fun _ _ => rfl⟩, ?_⟩
  intro q hq
  exact (hM q hq).trans (hagree q hq).symm

/-- The site-and-square construction has an exact local family whenever the
original real-type comparisons have nonempty scalar-image sets. This theorem
constructs the family and proves projection equality through its extension
and restriction fields; no local-family premise is assumed. -/
noncomputable def exactLocalFamily_of_constantScalarImages (b : E → F) (Q : C.ImageSets)
    (hQ : C.ConstantScalarImages b Q) (hL : n + 4 < L + 2) :
    AffineSystem.ExactLocalFamily (C.affineSystem (L := L)) (C.sourceShift b) (n + 4) where
  assignments := C.sourceFamily b Q
  nonempty S hS := C.sourceFamily_nonempty b Q hQ.nonempty S hS (lt_of_le_of_lt hS hL)
  sound S _ z hz := C.sourceFamily_sound b Q S z hz
  saturated S _ z w hzw := C.sourceFamily_saturated b Q S z w hzw
  restrict S U hSU _ := C.sourceFamily_restrict b Q hSU
  extend S U hSU hU z hz := C.sourceFamily_extend b Q hQ S U hSU hU (lt_of_le_of_lt hU hL) z hz

end GroupWL.SourceLayout.ComparisonData
