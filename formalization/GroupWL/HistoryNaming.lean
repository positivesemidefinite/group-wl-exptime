import GroupWL.QuotientMarked
import GroupWL.FrameHistory
import GroupWL.RingTransfer

/-! The coordinate labels used in frame decoding follow from the concrete
anchor formulas along every actual retained history. -/
namespace GroupWL.CoordinateNames.QuotientNamingContext
open PebbleGame FrameHistory

variable {F X Z H K : Type*} [Field F] [NeZero (2 : F)]
  [AddCommGroup X] [Module F X] [AddCommGroup Z] [Module F Z]
  [Group H] [Finite H] [Group K]
  {Y : Submodule F (X →ₗ[F] Z)} {ε : AlternatingBilinearMap F X Z}
  [Finite (TensorGroup (evaluationTwist Y ε))] {n : ℕ}
  (C : QuotientNamingContext Y ε H n)

def anchorSlots : Finset (Fin (n + 1)) :=
  ({0, 1, 2, 3} : Finset (Fin 9)).image (fun i => (C.slot i).castSucc)

theorem anchorSlots_card : C.anchorSlots.card ≤ 4 := by
  exact (Finset.card_image_le).trans (by decide)

theorem history_quotient {α : Type*} (query : α → TensorGroup (evaluationTwist Y ε))
    (e : H ≃* K) (coordinate : K → X) (he : ∀ h, coordinate (e h) = C.quotient h)
    {pos : Position (n + 1) (TensorGroup (evaluationTwist Y ε)) K}
    (hist : History C.anchorSlots query (mapRight e C.position) pos)
    {i : Fin (n + 1)} {g : TensorGroup (evaluationTwist Y ε)} {h : K}
    (hm : pos i = some (g, h)) : coordinate h = g.fst.1 := by
  have hp : Winning (mapRight e.symm pos) := hist.winning.mapRight e.symm
  have ha : ∀ j ∈ ({0, 1, 2} : Finset (Fin 9)),
      mapRight e.symm pos (C.slot j).castSucc =
        some (C.reference (C.slot j), C.opponent (C.slot j)) := by
    intro j hj
    have hj4 : j ∈ ({0, 1, 2, 3} : Finset (Fin 9)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj ⊢
      tauto
    have hs := hist.anchors_preserved (C.slot j).castSucc
      (Finset.mem_image.mpr ⟨j, hj4, rfl⟩)
    unfold mapRight
    rw [hs]
    change (mapRight e.symm (mapRight e C.position)) (C.slot j).castSucc = _
    rw [mapRight_symm]
    exact C.anchors j hj
  have hmark : mapRight e.symm pos i = some (g, e.symm h) := by
    simp only [mapRight, hm, Option.map_some]
  have hq := C.quotient_of_marked hp ha hmark
  rw [← he (e.symm h), e.apply_symm_apply] at hq
  exact hq

end GroupWL.CoordinateNames.QuotientNamingContext

namespace GroupWL.RingTransfer
open IncidenceTensor IncidenceCoordinates IncidenceGroup FrameResponses
open CoordinateNames PebbleGame

variable {p : ℕ} [Fact p.Prime] [NeZero (2 : ZMod p)]
  {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {V : J → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module (ZMod p) (V j)]
  (A : AffineSystem (ZMod p) I J V) (q : ℕ) (hq : 2 ≤ q)
  {H : Type*} [Group H] [Finite H] {n : ℕ}

/-- The prior `Named` interface is now discharged by genuine anchor formulas
and a reconstructed isomorphism preserving their quotient coordinate. -/
theorem named_of_reconstruction
    (C : QuotientNamingContext (Y A q hq)
      (twistCoordinates A q (inputCoordinates A q) (outputCoordinates A q)
        AlternatingBilinearMap.zero) H n)
    (β : I → ZMod p) (e : H ≃* ChargedGroup A q hq β)
    (he : ∀ h, (e h).fst.1 = C.quotient h) :
    Named A q hq β C.anchorSlots (mapRight e C.position) := by
  intro pos hist slot v a g hm
  exact C.history_quotient (pureQuery A q hq) e (fun h => h.fst.1) he hist hm

end GroupWL.RingTransfer
