import GroupWL.SourceLayout.GaugeExtension
import GroupWL.SourceLayout.LabelConsistency

namespace GroupWL.SourceLayout.ComparisonData

variable {F T E : Type*} [Field F] {n L : ℕ}
variable (C : ComparisonData F T E (n + 3))
variable [Fintype T] [Fintype E]

def UncutOn (cut : Cuts (E := E) (L := L)) (S : Finset (C.Block L)) : Prop :=
  ∀ l ∈ C.activeLinks S, l.position ≠ cut l.comparison

def cornerTag (cut : Cuts (E := E) (L := L)) (v : C.Corner L) : T × Bool :=
  (C.root cut v.1, C.alignedLabel cut v.2.1 v.1 v.2.2.val)

def blockTags (cut : Cuts (E := E) (L := L)) : C.Block L → (T × Bool) × (T × Bool)
  | .inl h => (C.cornerTag cut (C.horizontalStart L h), C.cornerTag cut (C.horizontalEnd L h))
  | .inr s => (C.cornerTag cut (C.horizontalStart L (C.squareLeft L s)),
      C.cornerTag cut (C.horizontalEnd L (C.squareLeft L s)))

theorem blockTags_root_eq (cut : Cuts (E := E) (L := L)) (B : C.Block L) :
    (C.blockTags cut B).1.1 = (C.blockTags cut B).2.1 := by cases B <;> rfl

theorem vertical_tags_eq (cut : Cuts (E := E) (L := L)) (S : Finset (C.Block L))
    (hcut : C.UncutOn cut S) (v : C.Vertical L) (hv : Sum.inr v ∈ C.usedReadouts S) :
    C.cornerTag cut (C.verticalStart L v) = C.cornerTag cut (C.verticalEnd L v) := by
  have hl := hcut v.1 (C.vertical_link_mem_active S v hv)
  exact Prod.ext (C.root_eq_of_uncut cut v.1 hl)
    (C.alignedLabel_eq_of_uncut cut v.1 hl v.2.1 v.2.2)

theorem horizontal_tags_of_mem_scope (cut : Cuts (E := E) (L := L)) (S : Finset (C.Block L))
    (hcut : C.UncutOn cut S) (h : C.Horizontal L) (B : C.Block L)
    (hB : B ∈ S) (hh : Sum.inl h ∈ C.scope L B) :
    (C.cornerTag cut (C.horizontalStart L h), C.cornerTag cut (C.horizontalEnd L h)) =
      C.blockTags cut B := by
  classical
  cases B with
  | inl q =>
    have heq : h = q := by simpa [scope] using hh
    subst q
    rfl
  | inr s =>
    have heq : h = C.squareLeft L s ∨ h = C.squareRight L s := by simpa [scope] using hh
    rcases heq with rfl | rfl
    · rfl
    · have hl := hcut s.1 (C.square_link_mem_active hB)
      apply Prod.ext
      · exact (Prod.ext (C.root_eq_of_uncut cut s.1 hl)
          (C.alignedLabel_eq_of_uncut cut s.1 hl s.2.1 s.2.2.1)).symm
      · exact (Prod.ext (C.root_eq_of_uncut cut s.1 hl)
          (C.alignedLabel_eq_of_uncut cut s.1 hl (finRotate (n + 3) s.2.1) s.2.2.2)).symm

private theorem rotate_invariant_eq_zero {A : Type*} (f : Fin (n + 3) → A)
    (hf : ∀ i, f (finRotate (n + 3) i) = f i) : ∀ i, f i = f 0 := by
  intro i
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
    have h := hf i.castSucc
    have hrot : finRotate (n + 3) i.castSucc = i.succ := finRotate_of_lt i.isLt
    rw [hrot] at h
    exact h.trans ih

/-- All readouts in a minimum wrapping block set use the same real root and
one aligned full address. -/
def CompatibleAddress (cut : Cuts (E := E) (L := L)) (S : Finset (C.Block L))
    (t : T) (a : Fin (n + 3) → Bool) : Prop :=
  ∀ q ∈ C.usedReadouts S,
    C.cornerTag cut (C.readoutStart L q) = (t, a (C.cornerRow (C.readoutStart L q))) ∧
    C.cornerTag cut (C.readoutEnd L q) = (t, a (C.cornerRow (C.readoutEnd L q)))

theorem exists_compatible_address (cut : Cuts (E := E) (L := L)) (S : Finset (C.Block L))
    (hcut : C.UncutOn cut S) (hwrap : (C.wrappingLayout S).Wraps) (hcard : S.card = n + 3) :
    ∃ t a, C.CompatibleAddress cut S t a := by
  classical
  let B (i : Fin (n + 3)) : {B // B ∈ S} :=
    Classical.choose (C.wrapping_unique_block_per_row S hwrap hcard i)
  have hB (i : Fin (n + 3)) : C.blockRow (B i).val = i :=
    (Classical.choose_spec (C.wrapping_unique_block_per_row S hwrap hcard i)).1
  have huniq (i : Fin (n + 3)) (D : C.Block L) (hD : D ∈ S) (hr : C.blockRow D = i) :
      D = (B i).val := by
    have h := (Classical.choose_spec (C.wrapping_unique_block_per_row S hwrap hcard i)).2 ⟨D, hD⟩ hr
    exact congrArg Subtype.val h
  let left (i : Fin (n + 3)) : T × Bool := (C.blockTags cut (B i).val).1
  let right (i : Fin (n + 3)) : T × Bool := (C.blockTags cut (B i).val).2
  have htags (h : C.Horizontal L) (hh : Sum.inl h ∈ C.usedReadouts S) :
      C.cornerTag cut (C.horizontalStart L h) = left h.2.1 ∧
        C.cornerTag cut (C.horizontalEnd L h) = right h.2.1 := by
    obtain ⟨D, hD, hhD⟩ := Finset.mem_biUnion.mp hh
    have hd := huniq h.2.1 D hD (C.horizontal_row_eq_of_mem_scope h D hhD).symm
    have hp := C.horizontal_tags_of_mem_scope cut S hcut h D hD hhD
    rw [hd] at hp
    exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
  have hvert (u v : C.Corner L) (huv : (C.cornerGraph S).Adj u v)
      (hr : C.cornerRow u = C.cornerRow v) : C.cornerTag cut u = C.cornerTag cut v := by
    rcases huv.2 with ⟨q, hq, rfl, rfl⟩ | ⟨q, hq, rfl, rfl⟩
    · cases q with
      | inl h => exact False.elim (CyclicLifting.finRotate_no_fixed n h.2.1 hr.symm)
      | inr v => exact C.vertical_tags_eq cut S hcut v hq
    · cases q with
      | inl h => exact False.elim (CyclicLifting.finRotate_no_fixed n h.2.1 hr)
      | inr v => exact (C.vertical_tags_eq cut S hcut v hq).symm
  have hforw (u v : C.Corner L) (huv : (C.cornerGraph S).Adj u v)
      (hr : C.cornerRow v = finRotate (n + 3) (C.cornerRow u)) :
      C.cornerTag cut u = left (C.cornerRow u) ∧ C.cornerTag cut v = right (C.cornerRow u) := by
    rcases huv.2 with ⟨q, hq, rfl, rfl⟩ | ⟨q, hq, rfl, rfl⟩
    · cases q with
      | inl h => exact htags h hq
      | inr v => exact False.elim (CyclicLifting.finRotate_no_fixed n v.2.1 hr.symm)
    · cases q with
      | inl h => exact False.elim (CyclicLifting.finRotate_no_two_cycle n h.2.1 hr.symm)
      | inr v => exact False.elim (CyclicLifting.finRotate_no_fixed n v.2.1 hr.symm)
  have hmatch (i : Fin (n + 3)) : right i = left (finRotate (n + 3) i) :=
    labels_match_of_wrapping (C.wrappingLayout S) (C.cornerTag cut) left right hvert hforw hwrap i
  have hroot (i : Fin (n + 3)) : (left i).1 = (left 0).1 := by
    apply rotate_invariant_eq_zero (fun i => (left i).1)
    intro j
    rw [← hmatch j]
    exact (C.blockTags_root_eq cut (B j).val).symm
  let t := (left 0).1
  let a (i : Fin (n + 3)) := (left i).2
  have hleft (i : Fin (n + 3)) : left i = (t, a i) := Prod.ext (hroot i) rfl
  have hright (i : Fin (n + 3)) : right i = (t, a (finRotate (n + 3) i)) :=
    (hmatch i).trans (hleft _)
  have hhoriz (h : C.Horizontal L) (hh : Sum.inl h ∈ C.usedReadouts S) :
      C.cornerTag cut (C.horizontalStart L h) = (t, a h.2.1) ∧
      C.cornerTag cut (C.horizontalEnd L h) = (t, a (finRotate (n + 3) h.2.1)) :=
    ⟨(htags h hh).1.trans (hleft _), (htags h hh).2.trans (hright _)⟩
  refine ⟨t, a, ?_⟩
  intro q hq
  cases q with
  | inl h => exact hhoriz h hq
  | inr v =>
    have hv := C.vertical_tags_eq cut S hcut v hq
    obtain ⟨D, hD, hqD⟩ := Finset.mem_biUnion.mp hq
    cases D with
    | inl h => simpa [affineSystem, scope] using hqD
    | inr s =>
      have heq : v = C.squareAfter L s ∨ v = C.squareBefore L s := by
        simpa [affineSystem, scope] using hqD
      have hused : Sum.inl (C.squareLeft L s) ∈ C.usedReadouts S :=
        Finset.mem_biUnion.mpr ⟨Sum.inr s, hD, by simp [affineSystem, scope]⟩
      have hpair := hhoriz (C.squareLeft L s) hused
      rcases heq with rfl | rfl
      · exact ⟨hpair.2, hv.symm.trans hpair.2⟩
      · exact ⟨hpair.1, hv.symm.trans hpair.1⟩

end GroupWL.SourceLayout.ComparisonData
