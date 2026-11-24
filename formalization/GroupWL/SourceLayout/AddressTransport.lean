import GroupWL.SourceLayout.CutTransport
import GroupWL.SourceLayout.ShiftPropagation

namespace GroupWL.SourceLayout.ComparisonData

variable {F T E : Type*} [Field F] {n L : ℕ}
variable (C : ComparisonData F T E (n + 3)) [Fintype T] [Fintype E]

def blockHorizontal : C.Block L → C.Horizontal L
  | .inl h => h
  | .inr s => C.squareLeft L s

theorem blockHorizontal_row (B : C.Block L) : (C.blockHorizontal B).2.1 = C.blockRow B := by
  cases B <;> rfl

theorem blockHorizontal_mem_scope (B : C.Block L) :
    Sum.inl (C.blockHorizontal B) ∈ C.scope L B := by
  classical
  cases B <;> simp [blockHorizontal, scope]

theorem compatibleAddress_at_usedCorner (cut : Cuts (E := E) (L := L))
    (S : Finset (C.Block L)) (t : T) (a : Fin (n + 3) → Bool)
    (ha : C.CompatibleAddress cut S t a) (v : C.Corner L) (hv : C.UsedCorner S v) :
    C.cornerTag cut v = (t, a (C.cornerRow v)) := by
  obtain ⟨q, hq, rfl | rfl⟩ := hv
  · exact (ha q hq).1
  · exact (ha q hq).2

theorem cutTransport_alignedLabel (old new : Cuts (E := E) (L := L))
    (i : Fin (n + 3)) (v : Node T E L) (b : Bool) :
    C.alignedLabel new i v b = C.cutTransport old new i v (C.alignedLabel old i v b) := by
  simp only [← alignedPermutation_apply, cutTransport, Equiv.trans_apply, Equiv.symm_apply_apply]

/-- Changing missing links changes a wrapping address by the coordinate
permutations at any one corner of its connected support. -/
theorem compatible_addresses_transport (old new : Cuts (E := E) (L := L))
    (S : Finset (C.Block L)) (ho : C.UncutOn old S) (hn : C.UncutOn new S)
    (hcard : S.card = n + 3) (hwrap : (C.wrappingLayout S).Wraps)
    (t₀ t₁ : T) (a₀ a₁ : Fin (n + 3) → Bool)
    (ha₀ : C.CompatibleAddress old S t₀ a₀) (ha₁ : C.CompatibleAddress new S t₁ a₁)
    (u : C.Corner L) (hu : C.UsedCorner S u) :
    C.root old u.1 = t₀ ∧ C.root new u.1 = t₁ ∧
      ∀ i, a₁ i = C.cutTransport old new i u.1 (a₀ i) := by
  refine ⟨congrArg Prod.fst (C.compatibleAddress_at_usedCorner old S t₀ a₀ ha₀ u hu),
    congrArg Prod.fst (C.compatibleAddress_at_usedCorner new S t₁ a₁ ha₁ u hu), ?_⟩
  intro i
  obtain ⟨B, hBi, _⟩ := C.wrapping_unique_block_per_row S hwrap hcard i
  let q : C.Readout L := .inl (C.blockHorizontal B.val)
  have hq : q ∈ C.usedReadouts S := C.scope_subset_used B.property (C.blockHorizontal_mem_scope B.val)
  let v := C.readoutStart L q
  have hv : C.UsedCorner S v := ⟨q, hq, Or.inl rfl⟩
  have hrow : C.cornerRow v = i := (C.blockHorizontal_row B.val).trans hBi
  obtain ⟨p⟩ := C.minimal_wrapping_used_connected S hcard hwrap hu hv
  have ht := C.cutTransport_walk old new S ho hn i p
  have h₀ : C.alignedLabel old i v.1 v.2.2.val = a₀ i := by
    have hh := congrArg Prod.snd (C.compatibleAddress_at_usedCorner old S t₀ a₀ ha₀ v hv)
    change C.alignedLabel old (C.cornerRow v) v.1 v.2.2.val = a₀ (C.cornerRow v) at hh
    simpa only [hrow] using hh
  have h₁ : C.alignedLabel new i v.1 v.2.2.val = a₁ i := by
    have hh := congrArg Prod.snd (C.compatibleAddress_at_usedCorner new S t₁ a₁ ha₁ v hv)
    change C.alignedLabel new (C.cornerRow v) v.1 v.2.2.val = a₁ (C.cornerRow v) at hh
    simpa only [hrow] using hh
  calc
    a₁ i = C.alignedLabel new i v.1 v.2.2.val := h₁.symm
    _ = C.cutTransport old new i v.1 (C.alignedLabel old i v.1 v.2.2.val) :=
      C.cutTransport_alignedLabel old new i v.1 v.2.2.val
    _ = C.cutTransport old new i u.1 (a₀ i) := by rw [← ht, h₀]

theorem compatible_addresses_eq_of_real_corner (old new : Cuts (E := E) (L := L))
    (S : Finset (C.Block L)) (ho : C.UncutOn old S) (hn : C.UncutOn new S)
    (hcard : S.card = n + 3) (hwrap : (C.wrappingLayout S).Wraps)
    (t₀ t₁ : T) (a₀ a₁ : Fin (n + 3) → Bool)
    (ha₀ : C.CompatibleAddress old S t₀ a₀) (ha₁ : C.CompatibleAddress new S t₁ a₁)
    (t : T) (i : Fin (n + 3)) (b : C.Label L (.inl t) i)
    (hu : C.UsedCorner S ⟨.inl t, i, b⟩) : t₀ = t₁ ∧ a₀ = a₁ := by
  obtain ⟨h₀, h₁, ha⟩ := C.compatible_addresses_transport old new S ho hn hcard hwrap
    t₀ t₁ a₀ a₁ ha₀ ha₁ ⟨.inl t, i, b⟩ hu
  refine ⟨h₀.symm.trans h₁, funext (fun j => ?_)⟩
  simpa [cutTransport, alignedPermutation] using (ha j).symm

end GroupWL.SourceLayout.ComparisonData
