import GroupWL.PGroupIdentification
import GroupWL.NumericPGroupCandidates

/-! Exact bounded numeric candidate condition for full identification. -/
namespace GroupWL.NumericPGroupCandidates
open Refinement
universe u
variable {p D : ℕ} [Fact p.Prime]

def CandidateGood (version : Version) (k D : ℕ) (G : Type u) [Group G] [Fintype G] (q : ℕ) : Prop :=
  match decode (p:=p) D q with
  | none => True
  | some t => letI := t
      letI : Mul (Fin (p^D)) := t.toMul
      GroupEquivalent version k G (Fin (p^D)) → Nonempty (G≃*Fin (p^D))

def IdentifiesCandidates (version : Version) (k D : ℕ) (G : Type u) [Group G] [Fintype G] : Prop :=
  ∀q<p^(D^3),CandidateGood (p:=p) version k D G q

theorem identifies_iff_candidates {G : Type u} [Group G] [Fintype G]
    (version : Version) {k : ℕ} (hk : k≠0) (hc : Nat.card G=p^D) :
    Refinement.Identifies version k G ↔ IdentifiesCandidates (p:=p) version k D G := by
  constructor
  · intro h q hq
    unfold CandidateGood
    cases he : decode (p:=p) D q with
    | none => trivial
    | some t =>
      letI := t
      letI : Mul (Fin (p^D)) := t.toMul
      exact h ⟨Fin (p^D),t,inferInstance⟩
  · intro h H he
    have hH : Nat.card H.Carrier=p^D := by
      rw [Nat.card_eq_fintype_card,←he.card_eq hk,←Nat.card_eq_fintype_card,hc]
    obtain ⟨q,hq,t,ht,⟨f⟩⟩ := decode_covers_exponential D hH
    letI := t
    letI : Mul (Fin (p^D)) := t.toMul
    have htest := h q hq
    unfold CandidateGood at htest
    rw [ht] at htest
    have he' : GroupEquivalent version k G (Fin (p^D)) :=
      he.trans (groupEquivalent_of_isomorphic f.symm version k)
    obtain ⟨e⟩ := htest he'
    exact ⟨e.trans f⟩

end GroupWL.NumericPGroupCandidates
