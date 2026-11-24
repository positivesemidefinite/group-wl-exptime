import GroupWL.SourceLayout.AdmissibleShifts
import GroupWL.SourceLayout.InternalWrapping
import GroupWL.SourceLayout.ImageShiftTransport

namespace GroupWL.SourceLayout.ComparisonData

variable {F T E : Type*} [Field F] {n L : ℕ}
variable (C : ComparisonData F T E (n + 3)) [Fintype T] [Fintype E]

theorem exists_usedCorner_of_wrap (S : Finset (C.Block L))
    (hwrap : (C.wrappingLayout S).Wraps) : ∃ v, C.UsedCorner S v := by
  obtain ⟨v, p, hp⟩ := hwrap
  exact ⟨v, C.usedCorner_of_wrappingAt S v (fun hv => hp (hv p))⟩

/-- Extend the image-admissible shifts of a minimal wrapping collection to
any larger collection of at most `r+1` blocks. The shifts on its entire old
corner support are preserved. -/
theorem extend_wrapped_shifts (b : E → F) (Q : C.ImageSets)
    (hQ : C.ConstantScalarImages b Q) (S U : Finset (C.Block L))
    (hSU : S ⊆ U) (hS : S.card = n + 3) (hU : U.card ≤ n + 4)
    (hwrap : (C.wrappingLayout S).Wraps) (old new : Cuts (E := E) (L := L))
    (ho : C.UncutOn old S) (hn : C.UncutOn new U)
    (h : ∀ t, Fin (C.dim t) → F) (hadm : C.RootAdmissible Q old S h) :
    ∃ h' : ∀ t, Fin (C.dim t) → F, C.RootAdmissible Q new U h' ∧
      ∀ v, C.UsedCorner S v →
        C.completedShift new h' b v.1 = C.completedShift old h b v.1 := by
  classical
  have hnS := hn.mono C hSU
  obtain ⟨t₀, a₀, ha₀⟩ := C.exists_compatible_address old S ho hwrap hS
  obtain ⟨t₁, a₁, ha₁⟩ := C.exists_compatible_address new S hnS hwrap hS
  have h₀ : h t₀ ∈ Q t₀ a₀ := hadm S (Finset.Subset.refl S) hS hwrap t₀ a₀ ha₀
  have hold : C.ShiftEquations S b (C.completedShift old h b) :=
    fun l hl => C.completedShift_equation old h b l (ho l hl)
  have hnew (h' : ∀ t, Fin (C.dim t) → F) : C.ShiftEquations S b (C.completedShift new h' b) :=
    fun l hl => C.completedShift_equation new h' b l (hnS l hl)
  by_cases hex : ∃ (t : T) (i : Fin (n + 3)) (a : C.Label L (.inl t) i),
      C.UsedCorner S ⟨.inl t, i, a⟩
  · obtain ⟨t, i, a, hu⟩ := hex
    obtain ⟨ht, ha⟩ := C.compatible_addresses_eq_of_real_corner old new S ho hnS hS hwrap
      t₀ t₁ a₀ a₁ ha₀ ha₁ t i a hu
    have h₁ : h t₁ ∈ Q t₁ a₁ := (C.shiftMember_congr Q h ht ha).mp h₀
    refine ⟨h, C.rootAdmissible_of_one Q new U S hSU hS hwrap hU t₁ a₁ ha₁ h h₁, ?_⟩
    intro v hv
    obtain ⟨p⟩ := C.minimal_wrapping_used_connected S hS hwrap hu hv
    exact C.shift_eq_of_walk S b _ _ hold (hnew h) (fun _ _ _ _ => rfl) p rfl
  · have hnone : C.NoRealCorners S := fun t i a hu => hex ⟨t, i, a, hu⟩
    obtain ⟨⟨node, i, a⟩, hu⟩ := C.exists_usedCorner_of_wrap S hwrap
    cases node with
    | inl t => exact False.elim (hnone t i a hu)
    | inr q =>
      obtain ⟨e, j⟩ := q
      obtain ⟨d, hd⟩ := C.internal_wrapping_domain old S ho hnone hS hwrap t₀ a₀ ha₀ e j i a hu
      obtain ⟨hr₀, hr₁, hat⟩ := C.compatible_addresses_transport old new S ho hnS hS hwrap
        t₀ t₁ a₀ a₁ ha₀ ha₁ ⟨.inr (e, j), i, a⟩ hu
      have had₀ : C.alignedAddress old e j d = a₀ := funext hd
      have had₁ : C.alignedAddress new e j d = a₁ := by
        funext k
        calc
          C.alignedAddress new e j d k =
              C.cutTransport old new k (.inr (e, j)) (C.alignedAddress old e j d k) := by
            simpa only [alignedAddress, alignedPermutation_apply] using
              C.cutTransport_alignedLabel old new k (.inr (e, j)) (d k).val
          _ = a₁ k := by rw [had₀]; exact (hat k).symm
      have hdm : h (C.root old (.inr (e, j))) ∈
          Q (C.root old (.inr (e, j))) (C.alignedAddress old e j d) :=
        (C.shiftMember_congr Q h hr₀ had₀).mpr h₀
      obtain ⟨h', hm, he⟩ := C.transport_internal_shift b Q hQ old new h e j d hdm
      have h₁ : h' t₁ ∈ Q t₁ a₁ := (C.shiftMember_congr Q h' hr₁ had₁).mp hm
      refine ⟨h', C.rootAdmissible_of_one Q new U S hSU hS hwrap hU t₁ a₁ ha₁ h' h₁, ?_⟩
      intro v hv
      obtain ⟨p⟩ := C.minimal_wrapping_used_connected S hS hwrap hu hv
      exact C.shift_eq_of_walk S b _ _ hold (hnew h')
        (fun t k c hc => False.elim (hnone t k c hc)) p he

end GroupWL.SourceLayout.ComparisonData
