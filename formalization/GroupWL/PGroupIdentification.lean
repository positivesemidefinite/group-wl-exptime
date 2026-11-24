import GroupWL.PGroupCandidates
import GroupWL.NeighborIsomorphism

/-! # Complete finite search space for identification of prime-power groups -/
namespace GroupWL.Refinement

universe u v
variable {G : Type u} {H : Type v} [Group G] [Group H] [Fintype G] [Fintype H]

/-- Every positive-dimensional version already determines the group order
from the zeroth restricted histogram. -/
theorem GroupEquivalent.card_eq {version : Version} {k : ℕ} (hk : k ≠ 0)
    (h : GroupEquivalent version k G H) : Fintype.card G=Fintype.card H := by
  cases version with
  | one => exact card_eq_of_equivalent hk h
  | two => exact card_eq_of_equivalent hk h
  | three =>
      change EquivalentIII k G H at h
      by_cases h1 : k=1
      · simp only [EquivalentIII,if_pos h1] at h
        have he := congrArg Multiset.card (h 0)
        simpa only [neighborGroupHistogram,Multiset.card_map] using he
      · simp only [EquivalentIII,if_neg h1] at h
        have he := congrArg Multiset.card (h 0)
        simp only [graphGroupHistogram,Multiset.card_map] at he
        change Fintype.card (Fin k → G)=Fintype.card (Fin k → H) at he
        simp only [Fintype.card_fun,Fintype.card_fin] at he
        exact Nat.pow_left_injective hk he

end GroupWL.Refinement

namespace GroupWL.PGroupCandidates

open Refinement
universe u
variable {p D : ℕ} [Fact p.Prime]
variable {G : Type u} [Group G] [Fintype G]

/-- The finite decoded-candidate condition, before supplying executable WL
and isomorphism tests. Rejected codes impose no requirement. -/
def IdentifiesCandidates (version : Version) (k D : ℕ) (G : Type u)
    [Group G] [Fintype G] : Prop :=
  ∀ c : Code p D, match decode (p := p) D c with
  | none => True
  | some t => letI := t
      GroupEquivalent version k G (Carrier p D) → Nonempty (G ≃* Carrier p D)

/-- Identification among all finite groups is equivalent to checking the
bounded candidate space, because equivalence fixes order and the decoder is complete. -/
theorem identifies_iff_candidates (version : Version) {k : ℕ} (hk : k ≠ 0)
    (hc : Nat.card G=p^D) :
    Refinement.Identifies version k G ↔ IdentifiesCandidates (p := p) version k D G := by
  constructor
  · intro h c
    cases he : decode (p := p) D c with
    | none => trivial
    | some t =>
        letI := t
        exact h ⟨Carrier p D,t,carrierFintype p D⟩
  · intro h H he
    have hH : Nat.card H.Carrier=p^D := by
      rw [Nat.card_eq_fintype_card,← he.card_eq hk,← Nat.card_eq_fintype_card,hc]
    obtain ⟨c,t,ht,⟨f⟩⟩ := decode_covers D hH
    letI := t
    have htest := h c
    rw [ht] at htest
    have he' : GroupEquivalent version k G (Carrier p D) :=
      he.trans (groupEquivalent_of_isomorphic f.symm version k)
    obtain ⟨e⟩ := htest he'
    exact ⟨e.trans f⟩

end GroupWL.PGroupCandidates
