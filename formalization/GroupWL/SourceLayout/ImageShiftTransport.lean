import GroupWL.SourceLayout.Images
import GroupWL.SourceLayout.CutTransport

namespace GroupWL.SourceLayout.ComparisonData

variable {F T E : Type*} [Field F] {r L : ℕ}
variable (C : ComparisonData F T E r)

def alignedAddress (cut : Cuts (E := E) (L := L)) (e : E) (j : Fin (L + 1))
    (d : C.DomainAddress e) : C.RealAddress :=
  fun i => C.alignedPermutation cut i (.inr (e, j)) (d i).val

private def ShiftMember (Q : C.ImageSets) (h : ∀ t, Fin (C.dim t) → F)
    (t : T) (a : C.RealAddress) : Prop := h t ∈ Q t a

theorem shiftMember_congr (Q : C.ImageSets) (h : ∀ t, Fin (C.dim t) → F)
    {t t' : T} {a a' : C.RealAddress} (ht : t = t') (ha : a = a') :
    h t ∈ Q t a ↔ h t' ∈ Q t' a' := by subst t'; subst a'; rfl

private theorem rootMember_source (Q : C.ImageSets) (h : ∀ t, Fin (C.dim t) → F)
    (cut : Cuts (E := E) (L := L)) (e : E) (j : Fin (L + 1)) (d : C.DomainAddress e)
    (hs : j.val < (cut e).val) :
    (h (C.root cut (.inr (e, j))) ∈ Q (C.root cut (.inr (e, j))) (C.alignedAddress cut e j d)) ↔
      h (C.source e) ∈ Q (C.source e) (C.sourceAddress d) := by
  apply C.shiftMember_congr Q h (by simp [root, hs])
  funext i
  simp [alignedAddress, alignedPermutation, hs, sourceAddress]

private theorem rootMember_target (Q : C.ImageSets) (h : ∀ t, Fin (C.dim t) → F)
    (cut : Cuts (E := E) (L := L)) (e : E) (j : Fin (L + 1)) (d : C.DomainAddress e)
    (hs : ¬ j.val < (cut e).val) :
    (h (C.root cut (.inr (e, j))) ∈ Q (C.root cut (.inr (e, j))) (C.alignedAddress cut e j d)) ↔
      h (C.target e) ∈ Q (C.target e) (C.targetAddress d) := by
  apply C.shiftMember_congr Q h (by simp [root, hs])
  funext i
  simp [alignedAddress, alignedPermutation, hs, targetAddress]

/-- Scalar-image equality transports an admissible shift across a change of
the missing link, preserving the scalar at an internal anchor. -/
theorem transport_internal_shift (b : E → F) (Q : C.ImageSets)
    (hQ : C.ConstantScalarImages b Q) (old new : Cuts (E := E) (L := L))
    (h : ∀ t, Fin (C.dim t) → F) (e : E) (j : Fin (L + 1)) (d : C.DomainAddress e)
    (hadm : h (C.root old (.inr (e, j))) ∈
      Q (C.root old (.inr (e, j))) (C.alignedAddress old e j d)) :
    ∃ h' : ∀ t, Fin (C.dim t) → F,
      h' (C.root new (.inr (e, j))) ∈
        Q (C.root new (.inr (e, j))) (C.alignedAddress new e j d) ∧
      C.completedShift new h' b (.inr (e, j)) = C.completedShift old h b (.inr (e, j)) := by
  classical
  by_cases ho : j.val < (old e).val <;> by_cases hn : j.val < (new e).val
  · refine ⟨h, ?_, ?_⟩
    · exact (C.rootMember_source Q h new e j d hn).mpr ((C.rootMember_source Q h old e j d ho).mp hadm)
    · simp only [completedShift, if_pos ho, if_pos hn]
  · have hs : C.sourceForm e (h (C.source e)) ∈
        C.sourceForm e '' Q (C.source e) (C.sourceAddress d) := by
      refine ⟨h (C.source e), ?_, rfl⟩
      exact (C.rootMember_source Q h old e j d ho).mp hadm
    rw [hQ.comparison e d] at hs
    obtain ⟨v, ⟨z, hz, rfl⟩, hv⟩ := hs
    let h' := Function.update h (C.target e) z
    refine ⟨h', ?_, ?_⟩
    · apply (C.rootMember_target Q h' new e j d hn).mpr
      simpa only [h', Function.update_self] using hz
    · change (if j.val < (new e).val then C.sourceForm e (h' (C.source e))
          else C.targetForm e (h' (C.target e)) + b e) =
        (if j.val < (old e).val then C.sourceForm e (h (C.source e))
          else C.targetForm e (h (C.target e)) + b e)
      simp only [if_neg hn, if_pos ho, h', Function.update_self]
      simpa only [add_comm] using hv
  · have ht : C.targetForm e (h (C.target e)) ∈
        C.targetForm e '' Q (C.target e) (C.targetAddress d) := by
      refine ⟨h (C.target e), ?_, rfl⟩
      exact (C.rootMember_target Q h old e j d ho).mp hadm
    have hs : b e + C.targetForm e (h (C.target e)) ∈
        C.sourceForm e '' Q (C.source e) (C.sourceAddress d) := by
      rw [hQ.comparison e d]
      exact ⟨_, ht, rfl⟩
    obtain ⟨z, hz, hv⟩ := hs
    let h' := Function.update h (C.source e) z
    refine ⟨h', ?_, ?_⟩
    · apply (C.rootMember_source Q h' new e j d hn).mpr
      simpa only [h', Function.update_self] using hz
    · change (if j.val < (new e).val then C.sourceForm e (h' (C.source e))
          else C.targetForm e (h' (C.target e)) + b e) =
        (if j.val < (old e).val then C.sourceForm e (h (C.source e))
          else C.targetForm e (h (C.target e)) + b e)
      simp only [if_pos hn, if_neg ho, h', Function.update_self]
      simpa only [add_comm] using hv
  · refine ⟨h, ?_, ?_⟩
    · exact (C.rootMember_target Q h new e j d hn).mpr ((C.rootMember_target Q h old e j d ho).mp hadm)
    · simp only [completedShift, if_neg ho, if_neg hn]

end GroupWL.SourceLayout.ComparisonData
