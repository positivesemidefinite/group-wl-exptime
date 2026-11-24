import GroupWL.IncidenceRecognition
import GroupWL.HistoryNaming
import GroupWL.TwistNormalization
import GroupWL.IncidenceRigidity

/-! Full reconstruction and normalization, retaining the actual histories
needed by the frame argument. -/
namespace GroupWL.NamedChargeReduction
open IncidenceTensor IncidenceCoordinates IncidenceGroup FrameResponses
open CoordinateNames PebbleGame

variable {p : ℕ} [Fact p.Prime] [NeZero (2 : ZMod p)]
  {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {V : J → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module (ZMod p) (V j)]
  (A : AffineSystem (ZMod p) I J V) (q : ℕ) (hq : 2 ≤ q)

theorem zero_coordinates :
    twistCoordinates A q (inputCoordinates A q) (outputCoordinates A q)
      AlternatingBilinearMap.zero = AlternatingBilinearMap.zero := by
  unfold twistCoordinates AlternatingBilinearMap.zero
  congr 1
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change (outputCoordinates A q) 0 = 0
  exact map_zero (outputCoordinates A q)

theorem zero_charge_iso [Nonempty I] (hq3 : 3 ≤ q) (β : I → ZMod p) :
    Nonempty (ZeroGroup A q hq ≃* ChargedGroup A q hq β) ↔
      β ∈ LinearMap.range A.linearMap := by
  have h := IncidenceRigidity.zero_charge_iso_iff A q hq3 β
  change Nonempty (TensorGroup (evaluationTwist (Y A q hq)
    (twistCoordinates A q (inputCoordinates A q) (outputCoordinates A q)
      AlternatingBilinearMap.zero)) ≃* ChargedGroup A q hq β) ↔ _
  rw [zero_coordinates A q]
  exact h

/-- Every winning opponent has a charge presentation in which all subsequent
pure frame queries carry their exact named input coordinates. -/
theorem exists_named_charge {H : Type*} [Group H] [Finite H]
    (hodd : Odd p) {k : ℕ} (hk : 9 ≤ k)
    {pos : Position (k + 1) (ZeroGroup A q hq) H} (hp : Winning pos) :
    ∃ (β : I → ZMod p) (e : H ≃* ChargedGroup A q hq β)
      (anchors : Finset (Fin (k + 1)))
      (initial : Position (k + 1) (ZeroGroup A q hq) (ChargedGroup A q hq β)),
      anchors.card ≤ 4 ∧ Winning initial ∧ RingTransfer.Named A q hq β anchors initial := by
  obtain ⟨C, η, f, _, hf, _⟩ := IncidenceRecognition.winning_named_reconstruction
    A q (by omega)
    (twistCoordinates A q (inputCoordinates A q) (outputCoordinates A q)
      AlternatingBilinearMap.zero) hodd hk hp
  obtain ⟨β, g, hg, _⟩ := GlobalCokernel.every_twist_isomorphic_charge_preserving
    A q (NeZero.ne (2 : ZMod p)) hq η
  let Q := C.toQuotientNamingContext
  let e : H ≃* ChargedGroup A q hq β := f.trans g
  have he (h : H) : (e h).fst.1 = Q.quotient h := (hg (f h)).trans (hf h)
  exact ⟨β, e, Q.anchorSlots, mapRight e C.position, Q.anchorSlots_card,
    C.winning.mapRight e, RingTransfer.named_of_reconstruction A q hq Q β e he⟩

end GroupWL.NamedChargeReduction
