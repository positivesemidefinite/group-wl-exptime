import GroupWL.NamedChargeReduction
import GroupWL.SourceRingTransfer

/-! The actual group identification reduction from the affine source's
acceptance property. All group recognition, naming and ring-transfer inputs
are discharged here. -/
namespace GroupWL.SourceIdentification
open SourceLayout SourceLayout.ComparisonData SourceRingTransfer
open PebbleGame Refinement FrameResponses

variable {p : ℕ} [Fact p.Prime] [NeZero (2 : ZMod p)]
  {T E : Type} [Fintype T] [Fintype E] {r : ℕ}
  (C : ComparisonData (ZMod p) T E (r+3)) (L q : ℕ) (hq : 3 ≤ q)
  [Nonempty (C.Block L)]

/-- The precise affine acceptance conclusion required from the computation
source, rather than an assumed group identification theorem. -/
def ScalarImageSolvability : Prop :=
  ∀ (β : C.Block L → ZMod p) (Q : C.ImageSets),
    (∀ h : C.Horizontal L, β (.inl h) = 0) → C.ScalarImages β Q →
      β ∈ LinearMap.range (system C L).linearMap

theorem winning_implies_isomorphic (hsource : ScalarImageSolvability C L)
    (hodd : Odd p) {k : ℕ} (hk : 9 ≤ k) (hbudget : q*((r+3)+1)+4 ≤ k+1)
    {H : Type*} [Group H] [Finite H]
    {pos : PebbleGame.Position (k+1) (G₀ C L q (by omega)) H} (hp : Winning pos) :
    Nonempty (G₀ C L q (by omega) ≃* H) := by
  obtain ⟨β, e, anchors, initial, hanchors, hi, named⟩ :=
    NamedChargeReduction.exists_named_charge (system C L) q (by omega) hodd hk hp
  have hm : q*((r+3)+1)+anchors.card ≤ k+1 := by omega
  have hs := site_shift_zero C L q (by omega) β anchors initial named hi hm
  have hQ := scalarImages_of_winning C L q (by omega) β anchors initial named hi hm
  have hβ := hsource β _ hs hQ
  obtain ⟨f⟩ := (NamedChargeReduction.zero_charge_iso (system C L) q (by omega) hq β).mpr hβ
  exact ⟨f.trans e.symm⟩

/-- Identification is quantified over every finite group in the original
definition. No restriction to tensor-described comparison groups is imposed. -/
theorem identifiesII [Fintype (G₀ C L q (by omega))]
    (hsource : ScalarImageSolvability C L) (hodd : Odd p)
    {k : ℕ} (hk : 9 ≤ k) (hbudget : q*((r+3)+1)+4 ≤ k+1) :
    IdentifiesII k (G₀ C L q (le_trans (by decide : 2 ≤ 3) hq)) := by
  intro H heq
  exact winning_implies_isomorphic C L q hq hsource hodd hk hbudget
    (RefinementGame.winning_empty_of_equivalentII heq)

end GroupWL.SourceIdentification
