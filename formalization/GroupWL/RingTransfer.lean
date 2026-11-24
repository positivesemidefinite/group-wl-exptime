import GroupWL.FrameResponses
import GroupWL.FrameExchange
import GroupWL.SourceLayout.Images

/-! # Ring transfer through actual winning histories

The only recognition input is that the fixed anchor names identify each pure
query's input coordinate throughout a retained history. All response equations
and consistency tests below follow from the game and the actual annihilator.
-/
set_option linter.unusedSectionVars false

namespace GroupWL.RingTransfer

open PebbleGame FrameHistory FrameExchange FrameResponses FrameDecoding FrameOrthogonality
open IncidenceTensor
open scoped BigOperators
universe u

/-- Fewer queried slots than available pebbles leave an after-pickup test slot. -/
theorem exists_spare {η : Type*} [Fintype η] {m : ℕ}
    (slot : η → Fin m) (hm : Fintype.card η < m) :
    ∃ s : Fin m, ∀ i, slot i ≠ s := by
  have hn : ¬ Function.Surjective slot := by
    intro h
    have hc := Fintype.card_le_of_surjective slot h
    simp only [Fintype.card_fin] at hc
    omega
  simpa only [Function.Surjective, not_forall, not_exists] using hn

/-- The unoccupied complement of finitely many forbidden slots contains a
whole new frame whenever its explicit cardinal budget permits it. -/
theorem fresh_slots {m q : ℕ} (forbidden : Finset (Fin m))
    (hm : q + forbidden.card ≤ m) :
    ∃ fresh : Fin q ↪ Fin m, ∀ a, fresh a ∉ forbidden := by
  classical
  have hc : Fintype.card (Fin q) ≤ (Finset.univ \ forbidden).card := by
    rw [Fintype.card_fin, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨f,hf⟩ := Function.Embedding.exists_of_card_le_finset hc
  refine ⟨f,fun a => ?_⟩
  exact (Finset.mem_sdiff.mp (hf ⟨a,rfl⟩)).2

variable {F I J : Type u} [Field F] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {V : J → Type u} [∀ j, AddCommGroup (V j)] [∀ j, Module F (V j)]
variable (A : AffineSystem F I J V) (q : ℕ) (hq : 2 ≤ q) (β : I → F)
variable {m : ℕ}

abbrev Position := PebbleGame.Position m (ZeroGroup A q hq) (ChargedGroup A q hq β)

noncomputable def pureQuery (va : (I ⊕ J) × Fin q) : ZeroGroup A q hq := query A q hq va.1 va.2

abbrev Hist (anchors : Finset (Fin m)) (initial p : Position A q hq β (m := m)) :=
  History anchors (pureQuery A q hq) initial p

/-- Exact coordinate-name preservation, the interface supplied by recognition. -/
def Named (anchors : Finset (Fin m)) (initial : Position A q hq β (m := m)) : Prop :=
  ∀ p, Hist A q hq β anchors initial p → ∀ (slot : Fin m) (v : I ⊕ J) (a : Fin q)
    (g : ChargedGroup A q hq β),
    p slot = some (query A q hq v a,g) → HasQueryCoordinate A q hq g v a

noncomputable def decodedFrame (f : Fin q → ChargedGroup A q hq β) : Frame A q :=
  fun a => oldPart A q (responseOperator A q hq (f a))

variable [NeZero (2 : F)]
variable {anchors : Finset (Fin m)} {initial p : Position A q hq β (m := m)}

theorem equation_frame (named : Named A q hq β anchors initial)
    (hp : Hist A q hq β anchors initial p) (hm : q < m)
    {slot : Fin q → Fin m} {i : I} {f : Fin q → ChargedGroup A q hq β}
    (hf : TracksFrame A q hq p slot (.inl i) f) :
    (∑ j : Scope A i, thetaEquation A q (decodedFrame A q hq β f) (scopeEdge A i j)) = β i := by
  obtain ⟨spare,hs⟩ := exists_spare slot (by simpa using hm)
  exact winning_equation_frame A q hq hp.winning hf
    (fun a => named p hp (slot a) (.inl i) a (f a) (hf a)) spare hs

theorem readout_frame (named : Named A q hq β anchors initial)
    (hp : Hist A q hq β anchors initial p) (hm : q < m)
    {slot : Fin q → Fin m} {j : J} {f : Fin q → ChargedGroup A q hq β}
    (hf : TracksFrame A q hq p slot (.inr j) f) :
    ∃ z : V j, ∀ i : Neighbors A j, A.coefficient i.1 j z =
      thetaReadout A q (decodedFrame A q hq β f) (neighborEdge A j i) := by
  obtain ⟨spare,hs⟩ := exists_spare slot (by simpa using hm)
  exact winning_readout_frame A q hq hp.winning hf
    (fun a => named p hp (slot a) (.inr j) a (f a) (hf a)) spare hs

theorem endpoint_agreement (named : Named A q hq β anchors initial)
    (hp : Hist A q hq β anchors initial p) (hm : 2*q < m)
    (e : Incidence A) {left right : Fin q → Fin m}
    {f g : Fin q → ChargedGroup A q hq β}
    (hf : TracksFrame A q hq p left (.inl e.1.1) f)
    (hg : TracksFrame A q hq p right (.inr e.1.2) g) :
    thetaEquation A q (decodedFrame A q hq β f) e =
      thetaReadout A q (decodedFrame A q hq β g) e := by
  obtain ⟨spare,hs⟩ := exists_spare (Sum.elim left right) (by simpa [two_mul] using hm)
  exact winning_endpoint_agreement A q hq hp.winning e hf hg
    (fun a => named p hp (left a) (.inl e.1.1) a (f a) (hf a))
    (fun b => named p hp (right b) (.inr e.1.2) b (g b) (hg b))
    spare (fun a => hs (.inl a)) (fun b => hs (.inr b))

/-- A hypothetical continuation querying a common readout proves consistency
of two already retained equation frames. It uses one additional frame and
does not require retaining that readout in the original position. -/
theorem two_equation_consistency (named : Named A q hq β anchors initial)
    (hp : Hist A q hq β anchors initial p) (hm : 3*q + anchors.card ≤ m)
    (j : J) (i i' : Neighbors A j) {left right : Fin q → Fin m}
    {f g : Fin q → ChargedGroup A q hq β}
    (hf : TracksFrame A q hq p left (.inl i.1) f)
    (hg : TracksFrame A q hq p right (.inl i'.1) g) :
    ∃ z : V j,
      A.coefficient i.1 j z = thetaEquation A q (decodedFrame A q hq β f) (neighborEdge A j i) ∧
      A.coefficient i'.1 j z = thetaEquation A q (decodedFrame A q hq β g) (neighborEdge A j i') := by
  classical
  let forbidden := anchors ∪ frameSlots left ∪ frameSlots right
  have hcard : forbidden.card ≤ anchors.card + 2*q := by
    calc
      forbidden.card ≤ (anchors ∪ frameSlots left).card + (frameSlots right).card :=
        Finset.card_union_le _ _
      _ ≤ anchors.card + (frameSlots left).card + (frameSlots right).card := by
        exact Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ anchors.card + q + q := by
        gcongr <;> exact (Finset.card_image_le.trans (by simp))
      _ = anchors.card + 2*q := by omega
  obtain ⟨fresh,hfresh⟩ := fresh_slots (q := q) forbidden (by omega)
  obtain ⟨p',h,hp',hh,hpreserve⟩ := hp.query_frame q fresh
    (fun a ha => hfresh a (Finset.mem_union_left _ (Finset.mem_union_left _ ha)))
    (fun a => ((.inr j : I ⊕ J),a))
  have hf' : TracksFrame A q hq p' left (.inl i.1) f := by
    intro a
    rw [hpreserve (left a) (by
      intro b heq
      exact hfresh b (heq.symm ▸ Finset.mem_union_left _
        (Finset.mem_union_right _ ((mem_frameSlots left (left a)).mpr ⟨a,rfl⟩))))]
    exact hf a
  have hg' : TracksFrame A q hq p' right (.inl i'.1) g := by
    intro a
    rw [hpreserve (right a) (by
      intro b heq
      exact hfresh b (heq.symm ▸ Finset.mem_union_right _
        ((mem_frameSlots right (right a)).mpr ⟨a,rfl⟩)))]
    exact hg a
  obtain ⟨z,hz⟩ := readout_frame A q hq β named hp' (by omega) hh
  refine ⟨z,?_,?_⟩
  · exact (hz i).trans (endpoint_agreement A q hq β named hp' (by omega)
      (neighborEdge A j i) hf' hh).symm
  · exact (hz i').trans (endpoint_agreement A q hq β named hp' (by omega)
      (neighborEdge A j i') hg' hh).symm

/-- Extend an equation frame's incidence values by zero outside its scope. -/
noncomputable def incidenceValue (B : I) (f : Fin q → ChargedGroup A q hq β) (j : J) : F :=
  if hj : j ∈ A.scope B then
    thetaEquation A q (decodedFrame A q hq β f) ⟨(B,j),hj⟩ else 0

@[simp] theorem incidenceValue_mem (B : I) (f : Fin q → ChargedGroup A q hq β)
    (j : J) (hj : j ∈ A.scope B) :
    incidenceValue A q hq β B f j =
      thetaEquation A q (decodedFrame A q hq β f) ⟨(B,j),hj⟩ := by
  simp [incidenceValue,hj]

theorem sum_incidenceValue (B : I) (f : Fin q → ChargedGroup A q hq β) :
    (∑ j ∈ A.scope B, incidenceValue A q hq β B f j) =
      ∑ j : Scope A B, thetaEquation A q (decodedFrame A q hq β f) (scopeEdge A B j) := by
  classical
  rw [← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro j _
  simp [incidenceValue,j.property,scopeEdge]

theorem equation_scope_sum (named : Named A q hq β anchors initial)
    (hp : Hist A q hq β anchors initial p) (hm : q < m)
    {slot : Fin q → Fin m} {i : I} {f : Fin q → ChargedGroup A q hq β}
    (hf : TracksFrame A q hq p slot (.inl i) f) :
    (∑ j ∈ A.scope i, incidenceValue A q hq β i f j) = β i := by
  rw [sum_incidenceValue]
  exact equation_frame A q hq β named hp hm hf

end GroupWL.RingTransfer
