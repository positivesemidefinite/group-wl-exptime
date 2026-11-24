import Mathlib.Tactic

/-!
# Parameters and transfer between WL versions

This file checks the arithmetic in Section 6 and the abstract consequence
of the three version-comparison inequalities. It does not establish those
comparison inequalities or the hardness reduction itself.
-/

namespace GroupWL

namespace Parameters

def blockBudget (r : ℕ) : ℕ := r + 1
def frameWidth (r : ℕ) : ℕ := r + 100
def ringBudget (r : ℕ) : ℕ := frameWidth r * blockBudget r
def dimensionII (r : ℕ) : ℕ := ringBudget r + 40
def dimensionI (r : ℕ) : ℕ := dimensionII r + 6
def dimensionIII (r : ℕ) : ℕ := (dimensionII r + 1) / 2 + 2
def rejectionDimension (r : ℕ) : ℕ :=
  (frameWidth r - 1) * (blockBudget r + 1) - 2

theorem frameWidth_ge_four (r : ℕ) : 4 ≤ frameWidth r := by
  unfold frameWidth
  omega

theorem rejectionDimension_eq (r : ℕ) :
    rejectionDimension r = ringBudget r + 96 := by
  unfold rejectionDimension ringBudget frameWidth blockBudget
  have h : r + 100 - 1 = r + 99 := by omega
  rw [h]
  have hpoly : (r + 99) * (r + 1 + 1) = (r + 100) * (r + 1) + 98 := by
    ring
  rw [hpoly]
  omega

theorem main_game_fits (r : ℕ) :
    dimensionII r + 1 < (frameWidth r - 1) * (blockBudget r + 1) := by
  have h := rejectionDimension_eq r
  unfold rejectionDimension at h
  unfold dimensionII
  omega

theorem versionI_in_rejection_range (r : ℕ) :
    dimensionI r ≤ rejectionDimension r := by
  rw [rejectionDimension_eq]
  unfold dimensionI dimensionII
  omega

theorem versionIII_comparison_fits (r : ℕ) :
    2 * dimensionIII r + 1 ≤ dimensionI r := by
  unfold dimensionIII dimensionI
  omega

theorem three_frame_test_fits {r : ℕ} (hr : 32 ≤ r) :
    3 * frameWidth r + 40 ≤ ringBudget r + 40 := by
  unfold ringBudget blockBudget
  have : 3 ≤ r + 1 := by omega
  nlinarith [Nat.mul_le_mul_left (frameWidth r) this]

theorem transfer_retains_spare (r : ℕ) :
    ringBudget r + 4 + 1 ≤ dimensionII r + 1 := by
  unfold dimensionII
  omega

end Parameters

/-- Identification relative to an equivalence test and an intended isomorphism relation. -/
def Identifies {A : Type*} (iso : A → A → Prop) (equiv : ℕ → A → A → Prop)
    (k : ℕ) (G : A) : Prop := ∀ H, equiv k G H → iso G H

/-- The power comparisons needed by the reduction, expressed in the
equivalence direction. Their group-WL instances require separate proofs. -/
structure VersionComparisons (A : Type*) where
  versionI : ℕ → A → A → Prop
  versionII : ℕ → A → A → Prop
  versionIII : ℕ → A → A → Prop
  monoI : ∀ {k l G H}, k ≤ l → versionI l G H → versionI k G H
  monoII : ∀ {k l G H}, k ≤ l → versionII l G H → versionII k G H
  monoIII : ∀ {k l G H}, k ≤ l → versionIII l G H → versionIII k G H
  ii_implies_i : ∀ {k G H}, versionII k G H → versionI k G H
  iii_implies_ii : ∀ {k G H},
    versionIII ((k + 1) / 2 + 2) G H → versionII k G H
  i_implies_iii : ∀ {k G H}, versionI (2 * k + 1) G H → versionIII k G H

namespace VersionComparisons

variable {A : Type*} (v : VersionComparisons A)

theorem identifies_III_of_II {iso : A → A → Prop} {k : ℕ} {G : A}
    (h : Identifies iso v.versionII k G) :
    Identifies iso v.versionIII ((k + 1) / 2 + 2) G := by
  intro H heq
  exact h H (v.iii_implies_ii heq)

theorem identifies_I_of_II {iso : A → A → Prop} {k : ℕ} {G : A}
    (h : Identifies iso v.versionII k G) :
    Identifies iso v.versionI (k + 6) G := by
  intro H heq
  apply h H
  apply v.iii_implies_ii
  apply v.i_implies_iii
  apply v.monoI (show 2 * ((k + 1) / 2 + 2) + 1 ≤ k + 6 by omega)
  exact heq

theorem rejection_I {r : ℕ} {G H : A}
    (h : v.versionII (Parameters.rejectionDimension r) G H) :
    v.versionI (Parameters.dimensionI r) G H :=
  v.ii_implies_i (v.monoII (Parameters.versionI_in_rejection_range r) h)

theorem rejection_III {r : ℕ} {G H : A}
    (h : v.versionII (Parameters.rejectionDimension r) G H) :
    v.versionIII (Parameters.dimensionIII r) G H := by
  apply v.i_implies_iii
  exact v.monoI (Parameters.versionIII_comparison_fits r) (v.rejection_I h)

theorem common_identification_cap {iso : A → A → Prop} {D : ℕ} {G : A}
    (h : Identifies iso v.versionII D G) :
    Identifies iso v.versionI (D + 10) G ∧
      Identifies iso v.versionII (D + 10) G ∧
      Identifies iso v.versionIII (D + 10) G := by
  refine ⟨?_, ?_, ?_⟩
  · intro H heq
    exact v.identifies_I_of_II h H (v.monoI (by omega) heq)
  · intro H heq
    exact h H (v.monoII (by omega) heq)
  · intro H heq
    exact v.identifies_III_of_II h H (v.monoIII (by omega) heq)

end VersionComparisons
end GroupWL
