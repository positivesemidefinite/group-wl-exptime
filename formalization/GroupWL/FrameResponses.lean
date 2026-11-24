import GroupWL.FrameOrthogonality
import GroupWL.GameRefinement
import GroupWL.RefinementGame

/-! # Decoding actual marked group responses

Only preservation of the named input coordinates is supplied by coordinate
recognition. Admissibility and every affine decoding identity are derived
from the actual group elements and the marked-subgroup game condition.
-/
set_option linter.unusedSectionVars false

namespace GroupWL
namespace PebbleGame

variable {G H : Type*} [Group G] [Group H] {m : ℕ}

theorem Atomic.marked_commutes {p : Position m G H} (hp : Atomic p)
    {i j : Fin m} {g g' : G} {h h' : H}
    (hi : p i = some (g,h)) (hj : p j = some (g',h'))
    (hcomm : g * g' = g' * g) : h * h' = h' * h := by
  obtain ⟨S,T,e,he⟩ := hp
  obtain ⟨hg,hh,hi'⟩ := he i g h hi
  obtain ⟨hg',hh',hj'⟩ := he j g' h' hj
  have hc : (⟨g,hg⟩ : S) * ⟨g',hg'⟩ = ⟨g',hg'⟩ * ⟨g,hg⟩ := Subtype.ext hcomm
  have hc' := congrArg e hc
  rw [map_mul, map_mul, hi', hj'] at hc'
  exact congrArg Subtype.val hc'

theorem Winning.marked_commutes {p : Position m G H} (hp : Winning p)
    {i j : Fin m} {g g' : G} {h h' : H}
    (hi : p i = some (g,h)) (hj : p j = some (g',h'))
    (s : Fin m) (his : i ≠ s) (hjs : j ≠ s)
    (hcomm : g * g' = g' * g) : h * h' = h' * h := by
  apply (winning_step hp s).1.marked_commutes (i := i) (j := j)
  · simpa only [erase_ne _ _ _ his] using hi
  · simpa only [erase_ne _ _ _ hjs] using hj
  · exact hcomm

end PebbleGame

namespace FrameResponses

open IncidenceTensor IncidenceCoordinates IncidenceGroup FrameDecoding FrameOrthogonality
open ObstructionDuality MatrixEvaluationGroup PebbleGame
open scoped BigOperators
universe u
variable {F I J : Type u} [Field F] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {V : J → Type u} [∀ j, AddCommGroup (V j)] [∀ j, Module F (V j)]
variable (A : AffineSystem F I J V) (q : ℕ) (hq : 2 ≤ q)

noncomputable abbrev C := coordinateObstruction A q (by omega) (inputCoordinates A q) (outputCoordinates A q)
noncomputable abbrev Y := operatorSpace (C A q hq)
abbrev ZeroGroup := ConstructedGroup A q (by omega) (inputCoordinates A q)
  (outputCoordinates A q) AlternatingBilinearMap.zero
abbrev ChargedGroup (β : I → F) := ConstructedGroup A q (by omega)
  (inputCoordinates A q) (outputCoordinates A q) (epsilonCharge A q hq β)

/-- A scalar-unit pure input query in the actual zero-twist group. -/
noncomputable def query (v : I ⊕ J) (a : Fin q) : ZeroGroup A q hq :=
  ⟨(inputCoordinates A q (oldUnit A q v a,0),0),0⟩

/-- Decode the matrix component of a group answer as a physical operator. -/
noncomputable def responseOperator {β : I → F} (g : ChargedGroup A q hq β) :
    PaddedInput A q →ₗ[F] PaddedOutput A q :=
  ((inputCoordinates A q).arrowCongr (outputCoordinates A q)).symm g.fst.2.val

@[simp] theorem responseOperator_apply {β : I → F} (g : ChargedGroup A q hq β)
    (x : PaddedInput A q) :
    responseOperator A q hq g x =
      (outputCoordinates A q).symm (g.fst.2.val (inputCoordinates A q x)) := rfl

theorem responseOperator_admissible {β : I → F} (g : ChargedGroup A q hq β) :
    Admissible A q (by omega) (responseOperator A q hq g) := by
  obtain ⟨c,hc,he⟩ := g.fst.2.property
  change matrixLinearEquiv.symm
    (((inputCoordinates A q).arrowCongr (outputCoordinates A q))
      (((inputCoordinates A q).arrowCongr (outputCoordinates A q)).symm g.fst.2.val)) ∈ _
  rw [LinearEquiv.apply_symm_apply, ← he]
  change matrixLinearEquiv.symm (matrixLinearEquiv c) ∈ _
  rw [LinearEquiv.symm_apply_apply]
  exact hc

@[simp] theorem query_commutes (v w : I ⊕ J) (a b : Fin q) :
    query A q hq v a * query A q hq w b = query A q hq w b * query A q hq v a := by
  apply TensorGroup.ext
  · change (inputCoordinates A q (oldUnit A q v a,0),0) +
        (inputCoordinates A q (oldUnit A q w b,0),0) =
      (inputCoordinates A q (oldUnit A q w b,0),0) +
        (inputCoordinates A q (oldUnit A q v a,0),0)
    exact add_comm _ _
  · change (0 : OutputIndex A q → F) + 0 + (2 : F)⁻¹ •
        (0 - 0 + outputCoordinates A q 0) =
      0 + 0 + (2 : F)⁻¹ • (0 - 0 + outputCoordinates A q 0)
    rfl

/-- Input-coordinate names are the only interface to the recognition layer. -/
def HasQueryCoordinate {β : I → F} (g : ChargedGroup A q hq β)
    (v : I ⊕ J) (a : Fin q) : Prop :=
  g.fst.1 = inputCoordinates A q (oldUnit A q v a,0)

/-- Commuting named answers satisfy the exact response commutator equation. -/
theorem responses_commute [NeZero (2 : F)] {β : I → F}
    {g h : ChargedGroup A q hq β} {v w : I ⊕ J} {a b : Fin q}
    (hg : HasQueryCoordinate A q hq g v a) (hh : HasQueryCoordinate A q hq h w b)
    (hc : g * h = h * g) :
    oldPart A q (responseOperator A q hq g) (oldUnit A q w b) -
      oldPart A q (responseOperator A q hq h) (oldUnit A q v a) =
      (epsilonCharge A q hq β (oldUnit A q v a,0) (oldUnit A q w b,0)).1 := by
  dsimp only [HasQueryCoordinate] at hg hh
  have he := (TensorGroup.mul_comm_iff g h).mp hc
  simp only [evaluationTwist_apply, hg, hh] at he
  have he' : g.fst.2.val (inputCoordinates A q (oldUnit A q w b,0)) -
      h.fst.2.val (inputCoordinates A q (oldUnit A q v a,0)) =
      outputCoordinates A q
        (epsilonCharge A q hq β (oldUnit A q v a,0) (oldUnit A q w b,0)) := by
    have ht : twistCoordinates A q (inputCoordinates A q) (outputCoordinates A q)
        (epsilonCharge A q hq β)
        (inputCoordinates A q (oldUnit A q v a,0))
        (inputCoordinates A q (oldUnit A q w b,0)) =
        outputCoordinates A q
          (epsilonCharge A q hq β (oldUnit A q v a,0) (oldUnit A q w b,0)) := by
      simp [twistCoordinates]
    change _ + (twistCoordinates A q (inputCoordinates A q) (outputCoordinates A q)
      (epsilonCharge A q hq β)) (inputCoordinates A q (oldUnit A q v a,0))
        (inputCoordinates A q (oldUnit A q w b,0)) = 0 at he
    rw [ht] at he
    exact (sub_eq_iff_eq_add).mpr (by linear_combination -he)
  have hp := congrArg (fun z => ((outputCoordinates A q).symm z).1) he'
  simpa [oldPart_apply, responseOperator_apply] using hp

/-- A fully retained frame records its actual marked answers. -/
def TracksFrame {β : I → F} {m : ℕ}
    (p : Position m (ZeroGroup A q hq) (ChargedGroup A q hq β))
    (slot : Fin q → Fin m) (v : I ⊕ J) (f : Fin q → ChargedGroup A q hq β) : Prop :=
  ∀ a, p (slot a) = some (query A q hq v a, f a)

theorem winning_frame_commutes [NeZero (2 : F)] {β : I → F} {m : ℕ}
    {p : Position m (ZeroGroup A q hq) (ChargedGroup A q hq β)} (hp : Winning p)
    {slot : Fin q → Fin m} {v : I ⊕ J} {f : Fin q → ChargedGroup A q hq β}
    (hf : TracksFrame A q hq p slot v f)
    (hcoord : ∀ a, HasQueryCoordinate A q hq (f a) v a)
    (spare : Fin m) (hs : ∀ a, slot a ≠ spare) :
    FrameCommutes A q hq β v (fun a => oldPart A q (responseOperator A q hq (f a))) := by
  intro a b
  apply responses_commute A q hq (hcoord a) (hcoord b)
  exact hp.marked_commutes (hf a) (hf b) spare (hs a) (hs b) (query_commutes A q hq v v a b)

theorem winning_equation_frame [NeZero (2 : F)] {β : I → F} {m : ℕ}
    {p : Position m (ZeroGroup A q hq) (ChargedGroup A q hq β)} (hp : Winning p)
    {slot : Fin q → Fin m} {i : I} {f : Fin q → ChargedGroup A q hq β}
    (hf : TracksFrame A q hq p slot (.inl i) f)
    (hcoord : ∀ a, HasQueryCoordinate A q hq (f a) (.inl i) a)
    (spare : Fin m) (hs : ∀ a, slot a ≠ spare) :
    (∑ j : Scope A i,
      thetaEquation A q (fun a => oldPart A q (responseOperator A q hq (f a)))
        (scopeEdge A i j)) = β i := by
  apply equation_frame_decodes A q hq β i _
    (fun a => responseOperator_admissible A q hq (f a))
  exact winning_frame_commutes A q hq hp hf hcoord spare hs

theorem winning_readout_frame [NeZero (2 : F)] {β : I → F} {m : ℕ}
    {p : Position m (ZeroGroup A q hq) (ChargedGroup A q hq β)} (hp : Winning p)
    {slot : Fin q → Fin m} {j : J} {f : Fin q → ChargedGroup A q hq β}
    (hf : TracksFrame A q hq p slot (.inr j) f)
    (hcoord : ∀ a, HasQueryCoordinate A q hq (f a) (.inr j) a)
    (spare : Fin m) (hs : ∀ a, slot a ≠ spare) :
    ∃ z : V j, ∀ i : Neighbors A j, A.coefficient i.1 j z =
      thetaReadout A q (fun a => oldPart A q (responseOperator A q hq (f a)))
        (neighborEdge A j i) := by
  apply actual_readout_frame_decodes A q hq β j _
    (fun a => responseOperator_admissible A q hq (f a))
  exact winning_frame_commutes A q hq hp hf hcoord spare hs

/-- Coexisting endpoint frames decode the same incidence value directly from
winning atomic preservation of their commuting pure queries. -/
theorem winning_endpoint_agreement [NeZero (2 : F)] {β : I → F} {m : ℕ}
    {p : Position m (ZeroGroup A q hq) (ChargedGroup A q hq β)} (hp : Winning p)
    (e : Incidence A) {left right : Fin q → Fin m}
    {f g : Fin q → ChargedGroup A q hq β}
    (hf : TracksFrame A q hq p left (.inl e.1.1) f)
    (hg : TracksFrame A q hq p right (.inr e.1.2) g)
    (hcf : ∀ a, HasQueryCoordinate A q hq (f a) (.inl e.1.1) a)
    (hcg : ∀ b, HasQueryCoordinate A q hq (g b) (.inr e.1.2) b)
    (spare : Fin m) (hl : ∀ a, left a ≠ spare) (hr : ∀ b, right b ≠ spare) :
    thetaEquation A q (fun a => oldPart A q (responseOperator A q hq (f a))) e =
      thetaReadout A q (fun b => oldPart A q (responseOperator A q hq (g b))) e := by
  apply endpoint_values_agree A q hq β e
  intro a b
  apply responses_commute A q hq (hcf a) (hcg b)
  exact hp.marked_commutes (hf a) (hg b) spare (hl a) (hr b)
    (query_commutes A q hq (.inl e.1.1) (.inr e.1.2) a b)

end FrameResponses
end GroupWL
