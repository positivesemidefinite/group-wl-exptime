import GroupWL.SourceLayout.MinimalWrapping

namespace GroupWL.SourceLayout.ComparisonData

variable {F T E : Type*} [Field F] {r n L : ℕ}
variable (C : ComparisonData F T E r)

def alignedPermutation (cut : Cuts (E := E) (L := L)) (i : Fin r) :
    Node T E L → Equiv.Perm Bool
  | .inl _ => Equiv.refl Bool
  | .inr (e, j) => if j.val < (cut e).val then Equiv.refl Bool else C.permutation e i

@[simp] theorem alignedPermutation_apply (cut : Cuts (E := E) (L := L))
    (i : Fin r) (v : Node T E L) (a : Bool) :
    C.alignedPermutation cut i v a = C.alignedLabel cut i v a := by
  cases v with
  | inl t => rfl
  | inr p => simp [alignedPermutation, alignedLabel]; split_ifs <;> rfl

/-- The coordinate change between two choices of missing links. -/
def cutTransport (old new : Cuts (E := E) (L := L)) (i : Fin r)
    (v : Node T E L) : Equiv.Perm Bool :=
  (C.alignedPermutation old i v).symm.trans (C.alignedPermutation new i v)

theorem cutTransport_link (old new : Cuts (E := E) (L := L)) (i : Fin r)
    (l : Link E L) (ho : l.position ≠ old l.comparison)
    (hn : l.position ≠ new l.comparison) :
    C.cutTransport old new i (C.leftNode L l) =
      C.cutTransport old new i (C.rightNode L l) := by
  have hfirst (cut : Cuts (E := E) (L := L)) (e : E)
      (h : (Link.first e : Link E L).position ≠ cut e) : 0 < (cut e).val := by
    have hz : (cut e).val ≠ 0 := fun hz => h (Fin.ext (by simpa [Link.position] using hz.symm))
    omega
  have hlast (cut : Cuts (E := E) (L := L)) (e : E)
      (h : (Link.last e : Link E L).position ≠ cut e) : ¬ L < (cut e).val := by
    have hz : (cut e).val ≠ L + 1 := fun hz => h (Fin.ext (by simpa [Link.position] using hz.symm))
    have := (cut e).isLt
    omega
  have hmiddle (cut : Cuts (E := E) (L := L)) (e : E) (j : Fin L)
      (h : (Link.middle e j).position ≠ cut e) :
      j.val < (cut e).val ↔ j.val + 1 < (cut e).val := by
    have hz : (cut e).val ≠ j.val + 1 :=
      fun hz => h (Fin.ext (by simpa [Link.position] using hz.symm))
    omega
  cases l with
  | first e => simp [cutTransport, alignedPermutation, leftNode, rightNode,
      hfirst old e ho, hfirst new e hn]
  | middle e j => simp only [cutTransport, alignedPermutation, leftNode, rightNode,
      Fin.val_castSucc, Fin.val_succ, hmiddle old e j ho, hmiddle new e j hn]; rfl
  | last e => simp [cutTransport, alignedPermutation, leftNode, rightNode,
      hlast old e ho, hlast new e hn]

variable (C : ComparisonData F T E (n + 3)) [Fintype T] [Fintype E]

theorem cutTransport_adj (old new : Cuts (E := E) (L := L))
    (S : Finset (C.Block L)) (ho : C.UncutOn old S) (hn : C.UncutOn new S)
    (i : Fin (n + 3)) {u v : C.Corner L} (h : (C.cornerGraph S).Adj u v) :
    C.cutTransport old new i u.1 = C.cutTransport old new i v.1 := by
  rcases h.2 with ⟨q, hq, rfl, rfl⟩ | ⟨q, hq, rfl, rfl⟩
  all_goals cases q with
  | inl h => rfl
  | inr w =>
      have hl := C.vertical_link_mem_active S w hq
      first
      | exact C.cutTransport_link old new i w.1 (ho _ hl) (hn _ hl)
      | exact (C.cutTransport_link old new i w.1 (ho _ hl) (hn _ hl)).symm

theorem cutTransport_walk (old new : Cuts (E := E) (L := L))
    (S : Finset (C.Block L)) (ho : C.UncutOn old S) (hn : C.UncutOn new S)
    (i : Fin (n + 3)) {u v : C.Corner L} (p : (C.cornerGraph S).Walk u v) :
    C.cutTransport old new i u.1 = C.cutTransport old new i v.1 := by
  induction p with
  | nil => rfl
  | cons h p ih => exact (C.cutTransport_adj old new S ho hn i h).trans ih

end GroupWL.SourceLayout.ComparisonData
