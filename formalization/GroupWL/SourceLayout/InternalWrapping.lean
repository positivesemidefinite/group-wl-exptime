import GroupWL.SourceLayout.AddressTransport
import GroupWL.SourceLayout.Images

namespace GroupWL.SourceLayout.ComparisonData

variable {F T E : Type*} [Field F] {n L : ℕ}
variable (C : ComparisonData F T E (n + 3)) [Fintype T] [Fintype E]

def NoRealCorners (S : Finset (C.Block L)) : Prop :=
  ∀ (t : T) (i : Fin (n + 3)) (a : C.Label L (.inl t) i),
    ¬ C.UsedCorner S ⟨.inl t, i, a⟩

theorem active_link_middle (S : Finset (C.Block L)) (hn : C.NoRealCorners S)
    (l : Link E L) (hl : l ∈ C.activeLinks S) : ∃ e j, l = .middle e j := by
  classical
  obtain ⟨B, hB, hlB⟩ := Finset.mem_biUnion.mp hl
  cases B with
  | inl h => simp [blockLinks] at hlB
  | inr s =>
    have heq : l = s.1 := by simpa [blockLinks] using hlB
    subst l
    obtain ⟨l, i, a, b⟩ := s
    cases l with
    | middle e j => exact ⟨e, j, rfl⟩
    | first e =>
      exfalso
      apply hn (C.source e) i (C.leftLabel L (.first e) i a)
      exact ⟨.inl (C.squareLeft L ⟨.first e, i, a, b⟩),
        C.scope_subset_used hB (by simp [scope]), Or.inl rfl⟩
    | last e =>
      exfalso
      apply hn (C.target e) i (C.rightLabel L (.last e) i a)
      exact ⟨.inl (C.squareRight L ⟨.last e, i, a, b⟩),
        C.scope_subset_used hB (by simp [scope]), Or.inl rfl⟩

def internalTag (cut : Cuts (E := E) (L := L)) :
    Node T E L → Option (E × (Fin (n + 3) → Equiv.Perm Bool))
  | .inl _ => none
  | .inr (e, j) => some (e, fun i => C.alignedPermutation cut i (.inr (e, j)))

theorem internalTag_middle (cut : Cuts (E := E) (L := L)) (e : E) (j : Fin L)
    (h : (Link.middle e j).position ≠ cut e) :
    C.internalTag cut (.inr (e, j.castSucc)) = C.internalTag cut (.inr (e, j.succ)) := by
  have hz : (cut e).val ≠ j.val + 1 :=
    fun hz => h (Fin.ext (by simpa [Link.position] using hz.symm))
  have hs : j.val < (cut e).val ↔ j.val + 1 < (cut e).val := by omega
  simp only [internalTag, alignedPermutation, Fin.val_castSucc, Fin.val_succ, hs]
  rfl

theorem internalTag_adj (cut : Cuts (E := E) (L := L)) (S : Finset (C.Block L))
    (hc : C.UncutOn cut S) (hn : C.NoRealCorners S)
    {u v : C.Corner L} (h : (C.cornerGraph S).Adj u v) :
    C.internalTag cut u.1 = C.internalTag cut v.1 := by
  rcases h.2 with ⟨q, hq, rfl, rfl⟩ | ⟨q, hq, rfl, rfl⟩
  all_goals cases q with
  | inl h => rfl
  | inr w =>
    have hl := C.vertical_link_mem_active S w hq
    obtain ⟨e, j, he⟩ := C.active_link_middle S hn w.1 hl
    have hm := C.internalTag_middle cut e j (by simpa only [he] using hc w.1 hl)
    first
    | simpa only [readoutStart, readoutEnd, verticalStart, verticalEnd, he, leftNode, rightNode] using hm
    | simpa only [readoutStart, readoutEnd, verticalStart, verticalEnd, he, leftNode, rightNode] using hm.symm

theorem internalTag_walk (cut : Cuts (E := E) (L := L)) (S : Finset (C.Block L))
    (hc : C.UncutOn cut S) (hn : C.NoRealCorners S)
    {u v : C.Corner L} (p : (C.cornerGraph S).Walk u v) :
    C.internalTag cut u.1 = C.internalTag cut v.1 := by
  induction p with
  | nil => rfl
  | cons h p ih => exact (C.internalTag_adj cut S hc hn h).trans ih

theorem internal_wrapping_same_wire (cut : Cuts (E := E) (L := L))
    (S : Finset (C.Block L)) (hc : C.UncutOn cut S) (hn : C.NoRealCorners S)
    (hcard : S.card = n + 3) (hwrap : (C.wrappingLayout S).Wraps)
    (e : E) (j : Fin (L + 1)) (i : Fin (n + 3)) (a : C.DomainLabel e i)
    (hu : C.UsedCorner S ⟨.inr (e, j), i, a⟩)
    (v : C.Corner L) (hv : C.UsedCorner S v) :
    ∃ k : Fin (L + 1), v.1 = .inr (e, k) ∧
      ∀ i, C.alignedPermutation cut i v.1 = C.alignedPermutation cut i (.inr (e, j)) := by
  obtain ⟨p⟩ := C.minimal_wrapping_used_connected S hcard hwrap hu hv
  have ht := C.internalTag_walk cut S hc hn p
  cases hvnode : v.1 with
  | inl t => simp [hvnode, internalTag] at ht
  | inr q =>
    obtain ⟨e', k⟩ := q
    simp only [hvnode, internalTag, Option.some.injEq, Prod.mk.injEq] at ht
    obtain ⟨hee, hp⟩ := ht
    subst e'
    exact ⟨k, rfl, fun i => (congrFun hp i).symm⟩

/-- A wrapping component containing only internal wire types determines a
full address in that wire's product domain, not just isolated allowed bits. -/
theorem internal_wrapping_domain (cut : Cuts (E := E) (L := L))
    (S : Finset (C.Block L)) (hc : C.UncutOn cut S) (hn : C.NoRealCorners S)
    (hcard : S.card = n + 3) (hwrap : (C.wrappingLayout S).Wraps)
    (t : T) (a : Fin (n + 3) → Bool) (ha : C.CompatibleAddress cut S t a)
    (e : E) (j : Fin (L + 1)) (i₀ : Fin (n + 3)) (b : C.DomainLabel e i₀)
    (hu : C.UsedCorner S ⟨.inr (e, j), i₀, b⟩) :
    ∃ d : C.DomainAddress e,
      ∀ i, C.alignedPermutation cut i (.inr (e, j)) (d i).val = a i := by
  let raw (i : Fin (n + 3)) := (C.alignedPermutation cut i (.inr (e, j))).symm (a i)
  have hraw (i : Fin (n + 3)) : raw i ∈ C.domain e i := by
    obtain ⟨B, hBi, _⟩ := C.wrapping_unique_block_per_row S hwrap hcard i
    let q : C.Readout L := .inl (C.blockHorizontal B.val)
    have hq : q ∈ C.usedReadouts S := C.scope_subset_used B.property (C.blockHorizontal_mem_scope B.val)
    let v := C.readoutStart L q
    have hv : C.UsedCorner S v := ⟨q, hq, Or.inl rfl⟩
    have hrow : C.cornerRow v = i := (C.blockHorizontal_row B.val).trans hBi
    obtain ⟨k, hvnode, hp⟩ := C.internal_wrapping_same_wire cut S hc hn hcard hwrap e j i₀ b hu v hv
    have hmem : v.2.2.val ∈ C.labelDomain L v.1 (C.cornerRow v) := v.2.2.property
    have hmem' : v.2.2.val ∈ C.domain e i := by
      simpa only [hvnode, hrow, labelDomain] using hmem
    have hbit := congrArg Prod.snd (C.compatibleAddress_at_usedCorner cut S t a ha v hv)
    change C.alignedLabel cut (C.cornerRow v) v.1 v.2.2.val = a (C.cornerRow v) at hbit
    rw [hrow, ← alignedPermutation_apply, hp i] at hbit
    have heq : raw i = v.2.2.val := by
      apply (C.alignedPermutation cut i (.inr (e, j))).injective
      simpa only [raw, Equiv.apply_symm_apply] using hbit.symm
    exact heq ▸ hmem'
  exact ⟨fun i => ⟨raw i, hraw i⟩, fun i => Equiv.apply_symm_apply _ _⟩

end GroupWL.SourceLayout.ComparisonData
