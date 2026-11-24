import GroupWL.RingTransfer
import GroupWL.SourceLayout.FrameCoefficients
import GroupWL.SourceLayout.WireImages

/-! # Scalar image sets extracted from retained source rings -/
set_option linter.unusedSectionVars false

namespace GroupWL.SourceRingTransfer

open SourceLayout SourceLayout.ComparisonData
open IncidenceTensor FrameDecoding FrameResponses FrameHistory FrameExchange RingTransfer
open scoped BigOperators
variable {F T E : Type} [Field F] [Fintype T] [Fintype E] {n : ℕ}
variable (C : ComparisonData F T E (n+3)) (L q : ℕ) (hq : 2 ≤ q)

noncomputable abbrev system := C.affineSystem (L := L)
abbrev G₀ := ZeroGroup (system C L) q hq
abbrev G (β : C.Block L → F) := ChargedGroup (system C L) q hq β
abbrev Pos (β : C.Block L → F) (m : ℕ) := PebbleGame.Position m (G₀ C L q hq) (G C L q hq β)

def ringLabels (t : Node T E L) (a : C.NodeAddress t) :
    Fin (n+3) → Fin q → (C.Block L ⊕ C.Readout L) × Fin q :=
  fun i k => (.inr (.inl (C.ringReadout t a i)),k)

def squareLabels (l : Link E L) (a : C.DomainAddress l.comparison) :
    Fin (n+3) → Fin q → (C.Block L ⊕ C.Readout L) × Fin q :=
  fun i k => (.inl (.inr (C.squareAt l a i)),k)

variable (β : C.Block L → F) {m : ℕ} (anchors : Finset (Fin m))
variable (initial : Pos C L q hq β m)

/-- A retained ring in a genuine continuation, together with decoded vectors.
The vectors need agree only with their own frame's incidence values. -/
structure RingState (t : Node T E L) (a : C.NodeAddress t) where
  position : Pos C L q hq β m
  history : Hist (system C L) q hq β anchors initial position
  packing : Packing (n+3) q m
  outside : ∀ k, packing k ∉ anchors
  answer : Fin (n+3) → Fin q → G C L q hq β
  tracks : Tracks (pureQuery (system C L) q hq) position packing (ringLabels C L q t a) answer
  value : Fin (n+3) → C.nodeSpace L t
  decoded : ∀ i (B : Neighbors (system C L) (.inl (C.ringReadout t a i))),
    (system C L).coefficient B.1 (.inl (C.ringReadout t a i)) (value i) =
      thetaReadout (system C L) q (decodedFrame (system C L) q hq β (answer i))
        (neighborEdge (system C L) (.inl (C.ringReadout t a i)) B)

noncomputable def RingState.total {t : Node T E L} {a : C.NodeAddress t}
    (w : RingState C L q hq β anchors initial t a) : C.nodeSpace L t := ∑ i, w.value i

variable [NeZero (2 : F)]
variable (named : Named (system C L) q hq β anchors initial)

include named in
/-- The actual frame decoder assigns source vectors to any acquired ring. -/
theorem state_of_tracks (hm : q < m) (t : Node T E L) (a : C.NodeAddress t)
    (p : Pos C L q hq β m) (hp : Hist (system C L) q hq β anchors initial p)
    (s : Packing (n+3) q m) (hs : ∀ k, s k ∉ anchors)
    (f : Fin (n+3) → Fin q → G C L q hq β)
    (hf : Tracks (pureQuery (system C L) q hq) p s (ringLabels C L q t a) f) :
    ∃ w : RingState C L q hq β anchors initial t a,
      w.position = p ∧ w.packing = s ∧ w.answer = f := by
  have hd : ∀ i, ∃ z : C.nodeSpace L t,
      ∀ B : Neighbors (system C L) (.inl (C.ringReadout t a i)),
        (system C L).coefficient B.1 (.inl (C.ringReadout t a i)) z =
          thetaReadout (system C L) q (decodedFrame (system C L) q hq β (f i))
            (neighborEdge (system C L) (.inl (C.ringReadout t a i)) B) := by
    intro i
    exact readout_frame (system C L) q hq β named hp hm (hf i)
  choose z hz using hd
  exact ⟨⟨p,hp,s,hs,f,hf,z,hz⟩,rfl,rfl,rfl⟩

include named in
/-- Every full address has a retained ring continuation within the stated
frame budget; the bijections are supplied by the winning game. -/
theorem ringState_nonempty (hp : PebbleGame.Winning initial)
    (hm : q*((n+3)+1) + anchors.card ≤ m) (t : Node T E L) (a : C.NodeAddress t) :
    Nonempty (RingState C L q hq β anchors initial t a) := by
  classical
  obtain ⟨s,hs⟩ := packing_exists (n := n+3) (q := q) anchors hm
  let active : (Fin (n+3) × Fin q) ↪ Fin m :=
    ⟨fun ik => s (some ik.1,ik.2),fun i j h => by
      have hh := s.injective h
      exact Prod.ext (Option.some.inj (Prod.mk.inj hh).1) (Prod.mk.inj hh).2⟩
  obtain ⟨p,f,hp',hf,houtside⟩ := (History.start (query := pureQuery (system C L) q hq) hp).query_finite
    active (fun ik => hs (some ik.1,ik.2)) (fun ik => ringLabels C L q t a ik.1 ik.2)
  obtain ⟨w,_,_,_⟩ := state_of_tracks C L q hq β anchors initial named (by nlinarith)
    t a p hp' s hs (fun i k => f (i,k)) (fun i k => hf (i,k))
  exact ⟨w⟩


noncomputable def leftValue (s : C.Square L) (f : Fin q → G C L q hq β) : F :=
  incidenceValue (system C L) q hq β (.inr s) f (.inl (C.squareLeft L s))
noncomputable def rightValue (s : C.Square L) (f : Fin q → G C L q hq β) : F :=
  incidenceValue (system C L) q hq β (.inr s) f (.inl (C.squareRight L s))
noncomputable def afterValue (s : C.Square L) (f : Fin q → G C L q hq β) : F :=
  incidenceValue (system C L) q hq β (.inr s) f (.inr (C.squareAfter L s))
noncomputable def beforeValue (s : C.Square L) (f : Fin q → G C L q hq β) : F :=
  incidenceValue (system C L) q hq β (.inr s) f (.inr (C.squareBefore L s))

def leftEdge (s : C.Square L) : Incidence (system C L) :=
  ⟨(.inr s,.inl (C.squareLeft L s)),C.squareLeft_mem_scope s⟩
def rightEdge (s : C.Square L) : Incidence (system C L) :=
  ⟨(.inr s,.inl (C.squareRight L s)),C.squareRight_mem_scope s⟩
def afterEdge (s : C.Square L) : Incidence (system C L) :=
  ⟨(.inr s,.inr (C.squareAfter L s)),C.squareAfter_mem_scope s⟩
def beforeEdge (s : C.Square L) : Incidence (system C L) :=
  ⟨(.inr s,.inr (C.squareBefore L s)),C.squareBefore_mem_scope s⟩

@[simp] theorem leftValue_eq (s : C.Square L) (f : Fin q → G C L q hq β) :
    leftValue C L q hq β s f =
      thetaEquation (system C L) q (decodedFrame (system C L) q hq β f) (leftEdge C L s) :=
  incidenceValue_mem _ _ _ _ _ _ _ (C.squareLeft_mem_scope s)
@[simp] theorem rightValue_eq (s : C.Square L) (f : Fin q → G C L q hq β) :
    rightValue C L q hq β s f =
      thetaEquation (system C L) q (decodedFrame (system C L) q hq β f) (rightEdge C L s) :=
  incidenceValue_mem _ _ _ _ _ _ _ (C.squareRight_mem_scope s)
@[simp] theorem afterValue_eq (s : C.Square L) (f : Fin q → G C L q hq β) :
    afterValue C L q hq β s f =
      thetaEquation (system C L) q (decodedFrame (system C L) q hq β f) (afterEdge C L s) :=
  incidenceValue_mem _ _ _ _ _ _ _ (C.squareAfter_mem_scope s)
@[simp] theorem beforeValue_eq (s : C.Square L) (f : Fin q → G C L q hq β) :
    beforeValue C L q hq β s f =
      thetaEquation (system C L) q (decodedFrame (system C L) q hq β f) (beforeEdge C L s) :=
  incidenceValue_mem _ _ _ _ _ _ _ (C.squareBefore_mem_scope s)

include named in
/-- Each retained square obeys the four-term source equation with its actual
incidence signs, as a consequence of the tensor frame decoder. -/
theorem square_identity (hm : q < m) {p : Pos C L q hq β m}
    (hp : Hist (system C L) q hq β anchors initial p)
    (s : C.Square L) {slot : Fin q → Fin m} {f : Fin q → G C L q hq β}
    (hf : TracksFrame (system C L) q hq p slot (.inl (.inr s)) f) :
    leftValue C L q hq β s f + rightValue C L q hq β s f +
      afterValue C L q hq β s f + beforeValue C L q hq β s f = β (.inr s) := by
  have h := equation_scope_sum (system C L) q hq β named hp hm hf
  change (∑ j ∈ C.scope L (.inr s),
    incidenceValue (system C L) q hq β (.inr s) f j) = β (.inr s) at h
  rw [C.sum_scope_square] at h
  exact h

include named in
/-- Adjacent retained square frames have matching vertical values. The
common vertical readout is queried only in a hypothetical continuation. -/
theorem vertical_consistency (hm : 3*q + anchors.card ≤ m)
    {p : Pos C L q hq β m} (hp : Hist (system C L) q hq β anchors initial p)
    (l : Link E L) (a : C.DomainAddress l.comparison)
    (slots : Packing (n+3) q m) (f : Fin (n+3) → Fin q → G C L q hq β)
    (hf : Tracks (pureQuery (system C L) q hq) p slots (squareLabels C L q l a) f)
    (i : Fin (n+3)) :
    afterValue C L q hq β (C.squareAt l a i) (f i) +
      beforeValue C L q hq β (C.squareAt l a (finRotate (n+3) i)) (f (finRotate (n+3) i)) = 0 := by
  let j : C.Readout L := .inr (C.squareAfter L (C.squareAt l a i))
  let B : Neighbors (system C L) j :=
    ⟨.inr (C.squareAt l a i),C.squareAfter_mem_scope _⟩
  let B' : Neighbors (system C L) j :=
    ⟨.inr (C.squareAt l a (finRotate (n+3) i)),C.squareBefore_mem_scope _⟩
  obtain ⟨z,hz,hz'⟩ := two_equation_consistency (system C L) q hq β named hp hm j B B'
    (hf i) (hf (finRotate (n+3) i))
  change C.coefficient (.inr (C.squareAt l a i))
    (.inr (C.squareAfter L (C.squareAt l a i))) z = _ at hz
  rw [C.coefficient_square_after] at hz
  change C.coefficient (.inr (C.squareAt l a (finRotate (n+3) i)))
    (.inr (C.squareBefore L (C.squareAt l a (finRotate (n+3) i)))) z = _ at hz'
  rw [C.coefficient_square_before] at hz'
  rw [afterValue_eq,beforeValue_eq]
  change z = thetaEquation (system C L) q (decodedFrame (system C L) q hq β (f i))
    (afterEdge C L (C.squareAt l a i)) at hz
  change -z = thetaEquation (system C L) q
    (decodedFrame (system C L) q hq β (f (finRotate (n+3) i)))
    (beforeEdge C L (C.squareAt l a (finRotate (n+3) i))) at hz'
  rw [← hz,← hz',add_neg_cancel]

include named in
/-- Summing actual retained square equations cancels their vertical terms. -/
theorem square_ring_balance (hm : 3*q + anchors.card ≤ m)
    {p : Pos C L q hq β m} (hp : Hist (system C L) q hq β anchors initial p)
    (l : Link E L) (a : C.DomainAddress l.comparison)
    (slots : Packing (n+3) q m) (f : Fin (n+3) → Fin q → G C L q hq β)
    (hf : Tracks (pureQuery (system C L) q hq) p slots (squareLabels C L q l a) f) :
    (∑ i, leftValue C L q hq β (C.squareAt l a i) (f i)) +
      (∑ i, rightValue C L q hq β (C.squareAt l a i) (f i)) = C.linkDelta β l a := by
  have hv : (∑ i, afterValue C L q hq β (C.squareAt l a i) (f i)) +
      (∑ i, beforeValue C L q hq β (C.squareAt l a i) (f i)) = 0 := by
    rw [← Equiv.sum_comp (finRotate (n+3))
      (fun i => beforeValue C L q hq β (C.squareAt l a i) (f i)),← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i _
    exact vertical_consistency C L q hq β anchors initial named hm hp l a slots f hf i
  have he := Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin (n+3)))) =>
    square_identity C L q hq β anchors initial named (by omega) hp (C.squareAt l a i) (hf i))
  simp only [Finset.sum_add_distrib] at he
  change _ = C.linkDelta β l a at he
  linear_combination he - hv


include named in
/-- A departure ring is transferred through a complete retained square ring
and then to its arrival ring. Each frame is placed before its predecessor is
removed, and the vertical consistency test is derived from Winning. -/
theorem transfer_forward (hm : q*((n+3)+1) + anchors.card ≤ m)
    (l : Link E L) (a : C.DomainAddress l.comparison)
    (w : RingState C L q hq β anchors initial (C.leftNode L l) (C.leftAddress l a)) :
    ∃ w' : RingState C L q hq β anchors initial (C.rightNode L l) (C.rightAddress l a),
      C.leftForm L l w.total - C.rightForm L l w'.total = C.linkDelta β l a := by
  classical
  have hm3 : 3*q + anchors.card ≤ m := by nlinarith [Nat.zero_le (q*n)]
  have hm2 : 2*q < m := by omega
  obtain ⟨p1,s1,f1,hp1,hs1,hf1,hcopy1⟩ := exchange_all w.history w.packing w.outside
    (ringLabels C L q (C.leftNode L l) (C.leftAddress l a)) (squareLabels C L q l a) w.answer w.tracks
    (fun i old new => leftValue C L q hq β (C.squareAt l a i) new =
      thetaReadout (system C L) q (decodedFrame (system C L) q hq β old)
        (leftEdge C L (C.squareAt l a i))) (by
      intro i p hp old fresh f g hfold hgfresh
      rw [leftValue_eq]
      exact endpoint_agreement (system C L) q hq β named hp hm2
        (leftEdge C L (C.squareAt l a i)) hgfresh hfold)
  have hleft (i : Fin (n+3)) : leftValue C L q hq β (C.squareAt l a i) (f1 i) =
      C.leftForm L l (w.value i) := by
    have hd := w.decoded i ⟨.inr (C.squareAt l a i),C.squareLeft_mem_scope _⟩
    change C.coefficient (.inr (C.squareAt l a i))
      (.inl (C.squareLeft L (C.squareAt l a i))) (w.value i) = _ at hd
    rw [C.coefficient_square_left] at hd
    exact (hcopy1 i).trans hd.symm
  have hbalance := square_ring_balance C L q hq β anchors initial named hm3 hp1 l a s1 f1 hf1
  obtain ⟨p2,s2,f2,hp2,hs2,hf2,hcopy2⟩ := exchange_all hp1 s1 hs1
    (squareLabels C L q l a) (ringLabels C L q (C.rightNode L l) (C.rightAddress l a)) f1 hf1
    (fun i old new => rightValue C L q hq β (C.squareAt l a i) old =
      thetaReadout (system C L) q (decodedFrame (system C L) q hq β new)
        (rightEdge C L (C.squareAt l a i))) (by
      intro i p hp old fresh f g hfold hgfresh
      rw [rightValue_eq]
      exact endpoint_agreement (system C L) q hq β named hp hm2
        (rightEdge C L (C.squareAt l a i)) hfold hgfresh)
  obtain ⟨w',hpos,hslots,hanswers⟩ := state_of_tracks C L q hq β anchors initial named (by omega)
    (C.rightNode L l) (C.rightAddress l a) p2 hp2 s2 hs2 f2 hf2
  have hright (i : Fin (n+3)) : rightValue C L q hq β (C.squareAt l a i) (f1 i) =
      -C.rightForm L l (w'.value i) := by
    have hd := w'.decoded i ⟨.inr (C.squareAt l a i),C.squareRight_mem_scope _⟩
    rw [hanswers] at hd
    change C.coefficient (.inr (C.squareAt l a i))
      (.inl (C.squareRight L (C.squareAt l a i))) (w'.value i) = _ at hd
    rw [C.coefficient_square_right] at hd
    exact (hcopy2 i).trans hd.symm
  refine ⟨w',?_⟩
  have hl : (∑ i, leftValue C L q hq β (C.squareAt l a i) (f1 i)) = C.leftForm L l w.total := by
    rw [RingState.total,map_sum]
    exact Finset.sum_congr rfl (fun i _ => hleft i)
  have hr : (∑ i, rightValue C L q hq β (C.squareAt l a i) (f1 i)) = -C.rightForm L l w'.total := by
    simp_rw [hright]
    rw [Finset.sum_neg_distrib,← map_sum]
    rfl
  rw [hl,hr] at hbalance
  simpa only [sub_eq_add_neg] using hbalance


include named in
/-- Reverse transfer uses the same actual history construction, starting at
the arrival readouts, and proves the reverse inclusion of scalar images. -/
theorem transfer_reverse (hm : q*((n+3)+1) + anchors.card ≤ m)
    (l : Link E L) (a : C.DomainAddress l.comparison)
    (w : RingState C L q hq β anchors initial (C.rightNode L l) (C.rightAddress l a)) :
    ∃ w' : RingState C L q hq β anchors initial (C.leftNode L l) (C.leftAddress l a),
      C.leftForm L l w'.total - C.rightForm L l w.total = C.linkDelta β l a := by
  classical
  have hm3 : 3*q + anchors.card ≤ m := by nlinarith [Nat.zero_le (q*n)]
  have hm2 : 2*q < m := by omega
  obtain ⟨p1,s1,f1,hp1,hs1,hf1,hcopy1⟩ := exchange_all w.history w.packing w.outside
    (ringLabels C L q (C.rightNode L l) (C.rightAddress l a)) (squareLabels C L q l a) w.answer w.tracks
    (fun i old new => rightValue C L q hq β (C.squareAt l a i) new =
      thetaReadout (system C L) q (decodedFrame (system C L) q hq β old)
        (rightEdge C L (C.squareAt l a i))) (by
      intro i p hp old fresh f g hfold hgfresh
      rw [rightValue_eq]
      exact endpoint_agreement (system C L) q hq β named hp hm2
        (rightEdge C L (C.squareAt l a i)) hgfresh hfold)
  have hright (i : Fin (n+3)) : rightValue C L q hq β (C.squareAt l a i) (f1 i) =
      -C.rightForm L l (w.value i) := by
    have hd := w.decoded i ⟨.inr (C.squareAt l a i),C.squareRight_mem_scope _⟩
    change C.coefficient (.inr (C.squareAt l a i))
      (.inl (C.squareRight L (C.squareAt l a i))) (w.value i) = _ at hd
    rw [C.coefficient_square_right] at hd
    exact (hcopy1 i).trans hd.symm
  have hbalance := square_ring_balance C L q hq β anchors initial named hm3 hp1 l a s1 f1 hf1
  obtain ⟨p2,s2,f2,hp2,hs2,hf2,hcopy2⟩ := exchange_all hp1 s1 hs1
    (squareLabels C L q l a) (ringLabels C L q (C.leftNode L l) (C.leftAddress l a)) f1 hf1
    (fun i old new => leftValue C L q hq β (C.squareAt l a i) old =
      thetaReadout (system C L) q (decodedFrame (system C L) q hq β new)
        (leftEdge C L (C.squareAt l a i))) (by
      intro i p hp old fresh f g hfold hgfresh
      rw [leftValue_eq]
      exact endpoint_agreement (system C L) q hq β named hp hm2
        (leftEdge C L (C.squareAt l a i)) hfold hgfresh)
  obtain ⟨w',hpos,hslots,hanswers⟩ := state_of_tracks C L q hq β anchors initial named (by omega)
    (C.leftNode L l) (C.leftAddress l a) p2 hp2 s2 hs2 f2 hf2
  have hleft (i : Fin (n+3)) : leftValue C L q hq β (C.squareAt l a i) (f1 i) =
      C.leftForm L l (w'.value i) := by
    have hd := w'.decoded i ⟨.inr (C.squareAt l a i),C.squareLeft_mem_scope _⟩
    rw [hanswers] at hd
    change C.coefficient (.inr (C.squareAt l a i))
      (.inl (C.squareLeft L (C.squareAt l a i))) (w'.value i) = _ at hd
    rw [C.coefficient_square_left] at hd
    exact (hcopy2 i).trans hd.symm
  refine ⟨w',?_⟩
  have hl : (∑ i, leftValue C L q hq β (C.squareAt l a i) (f1 i)) = C.leftForm L l w'.total := by
    rw [RingState.total,map_sum]
    exact Finset.sum_congr rfl (fun i _ => hleft i)
  have hr : (∑ i, rightValue C L q hq β (C.squareAt l a i) (f1 i)) = -C.rightForm L l w.total := by
    simp_rw [hright]
    rw [Finset.sum_neg_distrib,← map_sum]
    rfl
  rw [hl,hr] at hbalance
  simpa only [sub_eq_add_neg] using hbalance

/-- The source image set consists of all decoded ring sums in retained
continuations of the fixed anchoring history. -/
def nodeImages : C.NodeImages (L := L) :=
  fun t a => {z | ∃ w : RingState C L q hq β anchors initial t a, w.total = z}

include named in
theorem nodeImages_nonempty (hp : PebbleGame.Winning initial)
    (hm : q*((n+3)+1) + anchors.card ≤ m) :
    ∀ t a, (nodeImages C L q hq β anchors initial t a).Nonempty := by
  intro t a
  obtain ⟨w⟩ := ringState_nonempty C L q hq β anchors initial named hp hm t a
  exact ⟨w.total,w,rfl⟩

include named in
/-- Both actual retained-history transfers give the exact translated equality
of scalar image sets across every link. -/
theorem link_images (hm : q*((n+3)+1) + anchors.card ≤ m)
    (l : Link E L) (a : C.DomainAddress l.comparison) :
    C.leftForm L l '' nodeImages C L q hq β anchors initial (C.leftNode L l) (C.leftAddress l a) =
      (fun z => C.linkDelta β l a + z) ''
        (C.rightForm L l '' nodeImages C L q hq β anchors initial (C.rightNode L l) (C.rightAddress l a)) := by
  ext x
  constructor
  · rintro ⟨z,⟨w,rfl⟩,rfl⟩
    obtain ⟨w',hw'⟩ := transfer_forward C L q hq β anchors initial named hm l a w
    refine ⟨C.rightForm L l w'.total,⟨w'.total,⟨w',rfl⟩,rfl⟩,?_⟩
    exact (sub_eq_iff_eq_add.mp hw').symm
  · rintro ⟨z,⟨u,⟨w,rfl⟩,rfl⟩,rfl⟩
    obtain ⟨w',hw'⟩ := transfer_reverse C L q hq β anchors initial named hm l a w
    exact ⟨w'.total,⟨w',rfl⟩,sub_eq_iff_eq_add.mp hw'⟩

include named in
/-- A named winning anchoring history produces the manuscript's source
scalar-image sets, from literal finite frame histories and their budget. -/
theorem scalarImages_of_winning (hp : PebbleGame.Winning initial)
    (hm : q*((n+3)+1) + anchors.card ≤ m) :
    C.ScalarImages β (C.realImages (nodeImages C L q hq β anchors initial)) := by
  exact C.scalarImages_of_link_images β (nodeImages C L q hq β anchors initial)
    (nodeImages_nonempty C L q hq β anchors initial named hp hm)
    (link_images C L q hq β anchors initial named hm)

include named in
/-- Site rows have zero shift: their only incidence has zero coefficient,
which is tested by querying the owned readout in a continuation. -/
theorem site_shift_zero (hp : PebbleGame.Winning initial)
    (hm : q*((n+3)+1) + anchors.card ≤ m) (h : C.Horizontal L) : β (.inl h) = 0 := by
  classical
  have hm3 : 3*q + anchors.card ≤ m := by nlinarith [Nat.zero_le (q*n)]
  obtain ⟨slot,hslot⟩ := fresh_slots (q := q) anchors (by omega)
  obtain ⟨p,f,hp',hf,houtside⟩ := (History.start (query := pureQuery (system C L) q hq) hp).query_frame
    q slot hslot (fun k => (.inl (.inl h),k))
  have heq := equation_scope_sum (system C L) q hq β named hp' (by omega) hf
  change (∑ j ∈ C.scope L (.inl h),incidenceValue (system C L) q hq β (.inl h) f j) = β (.inl h) at heq
  rw [C.scope_site,Finset.sum_singleton] at heq
  let B : Neighbors (system C L) (.inl h) := ⟨.inl h,by simp [system,affineSystem,scope]⟩
  obtain ⟨z,hz,hz'⟩ := two_equation_consistency (system C L) q hq β named hp' hm3
    (.inl h) B B hf hf
  change C.coefficient (.inl h) (.inl h) z = _ at hz
  rw [C.coefficient_site] at hz
  rw [incidenceValue_mem _ _ _ _ _ _ _ (by simp [system,affineSystem,scope])] at heq
  exact heq.symm.trans hz.symm

/-- Any ring witness can end with precisely its ring and the anchors
retained. Removing all unrelated marks preserves every decoded vector. -/
theorem RingState.clean {t : Node T E L} {a : C.NodeAddress t}
    (w : RingState C L q hq β anchors initial t a) :
    ∃ w' : RingState C L q hq β anchors initial t a, w'.total = w.total ∧
      ∀ j, j ∉ anchors → (∀ i k, w'.packing (some i,k) ≠ j) → w'.position j = none := by
  classical
  let active : Finset (Fin m) := Finset.univ.image (fun ik : Fin (n+3) × Fin q => w.packing (some ik.1,ik.2))
  let p := FrameHistory.keep w.position (anchors ∪ active)
  have hp : Hist (system C L) q hq β anchors initial p := w.history.keep _ (Finset.subset_union_left)
  have ht : Tracks (pureQuery (system C L) q hq) p w.packing (ringLabels C L q t a) w.answer := by
    intro i k
    dsimp only [p,active]
    rw [FrameHistory.keep_mem _ (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨(i,k),Finset.mem_univ _,rfl⟩))]
    exact w.tracks i k
  let w' : RingState C L q hq β anchors initial t a :=
    ⟨p,hp,w.packing,w.outside,w.answer,ht,w.value,w.decoded⟩
  refine ⟨w',rfl,?_⟩
  intro j hj hslots
  change FrameHistory.keep w.position (anchors ∪ active) j = none
  apply FrameHistory.keep_not_mem
  simp only [Finset.mem_union,not_or]
  refine ⟨hj,?_⟩
  rintro ha
  obtain ⟨⟨i,k⟩,_,heq⟩ := Finset.mem_image.mp ha
  exact hslots i k heq

/-- The image-set definition is unchanged if endpoints are required to retain
only the queried ring and the fixed anchors, exactly as in the manuscript. -/
theorem mem_nodeImages_iff_clean (t : Node T E L) (a : C.NodeAddress t) (z : C.nodeSpace L t) :
    z ∈ nodeImages C L q hq β anchors initial t a ↔
      ∃ w : RingState C L q hq β anchors initial t a, w.total = z ∧
        ∀ j, j ∉ anchors → (∀ i k, w.packing (some i,k) ≠ j) → w.position j = none := by
  constructor
  · rintro ⟨w,hw⟩
    obtain ⟨w',ht,hclean⟩ := w.clean
    exact ⟨w',ht.trans hw,hclean⟩
  · rintro ⟨w,hw,_⟩
    exact ⟨w,hw⟩

end GroupWL.SourceRingTransfer
