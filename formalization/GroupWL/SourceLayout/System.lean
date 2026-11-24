import GroupWL.SourceLayout.Core

namespace GroupWL.SourceLayout.ComparisonData

open scoped BigOperators

variable {F T E : Type*} [Field F] {r L : ℕ}
variable (C : ComparisonData F T E r)

noncomputable instance readoutDecidableEq : DecidableEq (C.Readout L) := Classical.decEq _
noncomputable instance blockDecidableEq : DecidableEq (C.Block L) := Classical.decEq _

noncomputable instance readoutFintype [Fintype T] [Fintype E] : Fintype (C.Readout L) :=
  Fintype.ofFinite _

noncomputable instance blockFintype [Fintype T] [Fintype E] : Fintype (C.Block L) :=
  Fintype.ofFinite _

variable [Fintype T] [Fintype E]

/-- The coefficient of one readout in the actual block equation. -/
noncomputable def coefficient (B : C.Block L) (q : C.Readout L) : C.readoutSpace L q →ₗ[F] F :=
  (C.blockEquation L B).comp (LinearMap.single F (C.readoutSpace L) q)

theorem coefficient_outside (B : C.Block L) (q : C.Readout L) (hq : q ∉ C.scope L B) :
    C.coefficient B q = 0 := by
  classical
  ext v
  cases B with
  | inl h => simp [coefficient, blockEquation]
  | inr s =>
    have hl : q ≠ Sum.inl (C.squareLeft L s) := by
      intro heq
      apply hq
      simp [scope, heq]
    have hr : q ≠ Sum.inl (C.squareRight L s) := by
      intro heq
      apply hq
      simp [scope, heq]
    have ha : q ≠ Sum.inr (C.squareAfter L s) := by
      intro heq
      apply hq
      simp [scope, heq]
    have hb : q ≠ Sum.inr (C.squareBefore L s) := by
      intro heq
      apply hq
      simp [scope, heq]
    change C.leftForm L s.1 ((Pi.single q v) (.inl (C.squareLeft L s))) -
      C.rightForm L s.1 ((Pi.single q v) (.inl (C.squareRight L s))) +
      (Pi.single q v) (.inr (C.squareAfter L s)) -
      (Pi.single q v) (.inr (C.squareBefore L s)) = 0
    rw [Pi.single_eq_of_ne hl.symm, Pi.single_eq_of_ne hr.symm,
      Pi.single_eq_of_ne ha.symm, Pi.single_eq_of_ne hb.symm]
    change C.leftForm L s.1 (0 : C.nodeSpace L (C.leftNode L s.1)) -
      C.rightForm L s.1 (0 : C.nodeSpace L (C.rightNode L s.1)) + (0 : F) - 0 = 0
    rw [(C.leftForm L s.1).map_zero, (C.rightForm L s.1).map_zero]
    simp

/-- The finite affine system underlying the site-and-square source. -/
noncomputable def affineSystem : AffineSystem F (C.Block L) (C.Readout L) (C.readoutSpace L) where
  scope := C.scope L
  coefficient := C.coefficient
  coefficient_outside := C.coefficient_outside

@[simp] theorem affineSystem_scope (B : C.Block L) :
    (C.affineSystem (L := L)).scope B = C.scope L B := rfl

/-- Extracting coefficients and reassembling the finite sum recovers the
original signed block equation exactly. -/
theorem affineSystem_equation (B : C.Block L) (z : C.Assignment L) :
    (C.affineSystem (L := L)).equation B z = C.blockEquation L B z := by
  classical
  change (∑ q, C.blockEquation L B ((LinearMap.single F (C.readoutSpace L) q) (z q))) = _
  rw [← map_sum]
  simp only [LinearMap.single_apply, LinearMap.sum_single_apply]

theorem solves_iff (beta : C.Block L → F) (z : C.Assignment L) :
    (C.affineSystem (L := L)).linearMap z = beta ↔
      ∀ B, C.blockEquation L B z = beta B := by
  constructor
  · intro h B
    simpa [AffineSystem.linearMap, C.affineSystem_equation] using congrFun h B
  · intro h
    funext B
    exact (C.affineSystem_equation B z).trans (h B)

end GroupWL.SourceLayout.ComparisonData
