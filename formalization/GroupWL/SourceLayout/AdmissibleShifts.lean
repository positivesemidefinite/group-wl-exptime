import GroupWL.SourceLayout.WrappingOverlap
import GroupWL.SourceLayout.Images

namespace GroupWL.SourceLayout.ComparisonData

variable {F T E : Type*} [Field F] {n L : ℕ}
variable (C : ComparisonData F T E (n + 3)) [Fintype T] [Fintype E]

theorem activeLinks_mono {S U : Finset (C.Block L)} (h : S ⊆ U) :
    C.activeLinks S ⊆ C.activeLinks U := by
  classical
  intro l hl
  obtain ⟨B, hB, hlB⟩ := Finset.mem_biUnion.mp hl
  exact Finset.mem_biUnion.mpr ⟨B, h hB, hlB⟩

theorem UncutOn.mono {cut : Cuts (E := E) (L := L)} {S U : Finset (C.Block L)}
    (h : C.UncutOn cut U) (hSU : S ⊆ U) : C.UncutOn cut S :=
  fun l hl => h l (C.activeLinks_mono hSU hl)

/-- Image admissibility is imposed precisely on wrapping subcollections of
minimum size. At most `r+1` blocks can impose only one root/address condition. -/
def RootAdmissible (Q : C.ImageSets) (cut : Cuts (E := E) (L := L))
    (S : Finset (C.Block L)) (h : ∀ t, Fin (C.dim t) → F) : Prop :=
  ∀ R, R ⊆ S → R.card = n + 3 → (C.wrappingLayout R).Wraps →
    ∀ t a, C.CompatibleAddress cut R t a → h t ∈ Q t a

theorem RootAdmissible.mono {Q : C.ImageSets} {cut : Cuts (E := E) (L := L)}
    {S U : Finset (C.Block L)} {h : ∀ t, Fin (C.dim t) → F}
    (hh : C.RootAdmissible Q cut U h) (hSU : S ⊆ U) : C.RootAdmissible Q cut S h :=
  fun R hR hcard hwrap t a ha => hh R (hR.trans hSU) hcard hwrap t a ha

theorem rootAdmissible_of_one (Q : C.ImageSets) (cut : Cuts (E := E) (L := L))
    (S R : Finset (C.Block L)) (hR : R ⊆ S) (hcard : R.card = n + 3)
    (hwrap : (C.wrappingLayout R).Wraps) (hS : S.card ≤ n + 4)
    (t : T) (a : Fin (n + 3) → Bool) (ha : C.CompatibleAddress cut R t a)
    (h : ∀ t, Fin (C.dim t) → F) (hadm : h t ∈ Q t a) :
    C.RootAdmissible Q cut S h := by
  intro R' hR' hcard' hwrap' t' a' ha'
  obtain ⟨rfl, rfl⟩ := C.compatible_addresses_eq_of_overlap cut R R' S hR hR'
    hwrap hcard hcard' hS t t' a a' ha ha'
  exact hadm

theorem exists_admissible_shifts (Q : C.ImageSets) (hne : ∀ t a, (Q t a).Nonempty)
    (cut : Cuts (E := E) (L := L)) (S : Finset (C.Block L))
    (hcut : C.UncutOn cut S) (hS : S.card ≤ n + 4) :
    ∃ h : ∀ t, Fin (C.dim t) → F, C.RootAdmissible Q cut S h := by
  classical
  by_cases hex : ∃ R, R ⊆ S ∧ R.card = n + 3 ∧ (C.wrappingLayout R).Wraps
  · obtain ⟨R, hR, hcard, hwrap⟩ := hex
    obtain ⟨t, a, ha⟩ := C.exists_compatible_address cut R (hcut.mono C hR) hwrap hcard
    obtain ⟨z, hz⟩ := hne t a
    let h : ∀ t, Fin (C.dim t) → F := Function.update (fun _ _ => 0) t z
    exact ⟨h, C.rootAdmissible_of_one Q cut S R hR hcard hwrap hS t a ha h (by simpa [h] using hz)⟩
  · refine ⟨fun _ _ => 0, ?_⟩
    intro R hR hcard hwrap
    exact False.elim (hex ⟨R, hR, hcard, hwrap⟩)

/-- Total assignments represent local data by agreement on the readouts of
the chosen block set; this makes saturation part of the definition. -/
def sourceFamily (b : E → F) (Q : C.ImageSets) (S : Finset (C.Block L)) :
    Set (C.Assignment L) :=
  {z | ∃ (cut : Cuts (E := E) (L := L)) (h : ∀ t, Fin (C.dim t) → F)
      (M : C.CornerPotential (L := L)), C.UncutOn cut S ∧ C.RootAdmissible Q cut S h ∧
      ∀ q ∈ C.usedReadouts S, z q = C.potentialAssignment (C.completedShift cut h b) M q}

theorem sourceFamily_nonempty (b : E → F) (Q : C.ImageSets)
    (hne : ∀ t a, (Q t a).Nonempty) (S : Finset (C.Block L))
    (hS : S.card ≤ n + 4) (hL : S.card < L + 2) : (C.sourceFamily b Q S).Nonempty := by
  let cut := C.cutsFor S hL
  have hcut : C.UncutOn cut S := C.active_not_cut S hL
  obtain ⟨h, hh⟩ := C.exists_admissible_shifts Q hne cut S hcut hS
  exact ⟨C.potentialAssignment (C.completedShift cut h b) 0, cut, h, 0, hcut, hh, fun _ _ => rfl⟩

theorem sourceFamily_sound (b : E → F) (Q : C.ImageSets)
    (S : Finset (C.Block L)) (z : C.Assignment L) (hz : z ∈ C.sourceFamily b Q S) :
    (C.affineSystem (L := L)).SolvesOn (C.sourceShift b) S z := by
  obtain ⟨cut, h, M, hcut, _, hagree⟩ := hz
  apply ((C.affineSystem (L := L)).solvesOn_congr (C.sourceShift b) S hagree).mpr
  exact C.potentialAssignment_solvesOn S b (C.completedShift cut h b) M
    (fun l hl => C.completedShift_equation cut h b l (hcut l hl))

theorem sourceFamily_restrict (b : E → F) (Q : C.ImageSets)
    {S U : Finset (C.Block L)} (hSU : S ⊆ U) :
    C.sourceFamily b Q U ⊆ C.sourceFamily b Q S := by
  rintro z ⟨cut, h, M, hcut, hadm, hagree⟩
  exact ⟨cut, h, M, hcut.mono C hSU, hadm.mono C hSU,
    fun q hq => hagree q ((C.affineSystem (L := L)).readouts_mono hSU hq)⟩

theorem sourceFamily_saturated (b : E → F) (Q : C.ImageSets)
    (S : Finset (C.Block L)) (z w : C.Assignment L)
    (hzw : ∀ q ∈ C.usedReadouts S, z q = w q) :
    z ∈ C.sourceFamily b Q S ↔ w ∈ C.sourceFamily b Q S := by
  constructor
  · rintro ⟨cut, h, M, hcut, hadm, hagree⟩
    exact ⟨cut, h, M, hcut, hadm, fun q hq => (hzw q hq).symm.trans (hagree q hq)⟩
  · rintro ⟨cut, h, M, hcut, hadm, hagree⟩
    exact ⟨cut, h, M, hcut, hadm, fun q hq => (hzw q hq).trans (hagree q hq)⟩

end GroupWL.SourceLayout.ComparisonData
