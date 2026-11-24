import GroupWL.SourceLayout.Core

namespace GroupWL.SourceLayout

namespace Link

variable {E : Type*} {L : ℕ}

def position : Link E L → Fin (L + 2)
  | .first _ => 0
  | .middle _ i => i.succ.castSucc
  | .last _ => Fin.last (L + 1)

def atPosition (e : E) (i : Fin (L + 2)) : Link E L :=
  if h0 : i.val = 0 then .first e
  else if hlast : i.val = L + 1 then .last e
  else .middle e ⟨i.val - 1, by have := i.isLt; omega⟩

@[simp] theorem atPosition_position (l : Link E L) : atPosition l.comparison l.position = l := by
  cases l with
  | first e => simp [atPosition, position, comparison]
  | middle e i =>
    have hi := i.isLt
    simp [atPosition, position, comparison, Nat.ne_of_lt hi]
  | last e => simp [atPosition, position, comparison]

@[simp] theorem position_atPosition (e : E) (i : Fin (L + 2)) :
    (atPosition e i).position = i := by
  unfold atPosition
  split_ifs with h0 hlast
  all_goals apply Fin.ext; simp [position]; omega

@[simp] theorem comparison_atPosition (e : E) (i : Fin (L + 2)) :
    (atPosition e i).comparison = e := by
  unfold atPosition
  split_ifs <;> rfl

theorem atPosition_injective (e : E) : Function.Injective (atPosition (L := L) e) :=
  fun _ _ h => by simpa only [position_atPosition] using congrArg position h

end Link

namespace ComparisonData

variable {F T E : Type*} [Field F] {r L : ℕ}
variable (C : ComparisonData F T E r)

/-- The selected missing link on each private wire. -/
abbrev Cuts := E → Fin (L + 2)

/-- Complete every cut wire to its two real endpoints. This gives an explicit
root for every type and avoids choosing paths in its type-support tree. -/
def root (cut : Cuts (E := E) (L := L)) : Node T E L → T
  | .inl t => t
  | .inr (e, j) => if j.val < (cut e).val then C.source e else C.target e

/-- Labels aligned with the real root. On the target arm the wire's coordinate
permutation is applied. -/
def alignedLabel (cut : Cuts (E := E) (L := L)) (i : Fin r) : Node T E L → Bool → Bool
  | .inl _, a => a
  | .inr (e, j), a => if j.val < (cut e).val then a else C.permutation e i a

def linkConstant (b : E → F) : Link E L → F
  | .first _ => 0
  | .middle _ _ => 0
  | .last e => b e

/-- The compatible type shifts obtained from arbitrary real shifts after
cutting one link per wire. -/
def completedShift (cut : Cuts (E := E) (L := L))
    (h : ∀ t, Fin (C.dim t) → F) (b : E → F) : ∀ t : Node T E L, C.nodeSpace L t
  | .inl t => h t
  | .inr (e, j) => if j.val < (cut e).val then C.sourceForm e (h (C.source e))
      else C.targetForm e (h (C.target e)) + b e

private theorem first_not_cut {cut : Cuts (E := E) (L := L)} {e : E}
    (h : (Link.first e : Link E L).position ≠ cut e) : 0 < (cut e).val := by
  have hn : (cut e).val ≠ 0 := by
    intro he
    apply h
    apply Fin.ext
    simpa [Link.position] using he.symm
  omega

private theorem middle_not_cut {cut : Cuts (E := E) (L := L)} {e : E} {i : Fin L}
    (h : (Link.middle e i).position ≠ cut e) :
    i.val < (cut e).val ↔ i.val + 1 < (cut e).val := by
  have hn : (cut e).val ≠ i.val + 1 := by
    intro he
    apply h
    apply Fin.ext
    simpa [Link.position] using he.symm
  omega

private theorem last_not_cut {cut : Cuts (E := E) (L := L)} {e : E}
    (h : (Link.last e : Link E L).position ≠ cut e) : ¬ L < (cut e).val := by
  have hn : (cut e).val ≠ L + 1 := by
    intro he
    apply h
    apply Fin.ext
    simpa [Link.position] using he.symm
  have := (cut e).isLt
  omega

/-- Every uncut link preserves its real root. In particular an active path
cannot join two distinct real types. -/
theorem root_eq_of_uncut (cut : Cuts (E := E) (L := L)) (l : Link E L)
    (hl : l.position ≠ cut l.comparison) :
    C.root cut (C.leftNode L l) = C.root cut (C.rightNode L l) := by
  cases l with
  | first e => simp [root, leftNode, rightNode, first_not_cut hl]
  | middle e i => simp only [root, leftNode, rightNode, Fin.val_castSucc, Fin.val_succ,
      middle_not_cut hl]; rfl
  | last e => simp [root, leftNode, rightNode, last_not_cut hl]

/-- Actual matching labels have identical aligned labels on every uncut link. -/
theorem alignedLabel_eq_of_uncut (cut : Cuts (E := E) (L := L))
    (l : Link E L) (hl : l.position ≠ cut l.comparison) (i : Fin r)
    (a : C.DomainLabel l.comparison i) :
    C.alignedLabel cut i (C.leftNode L l) (C.leftLabel L l i a).val =
      C.alignedLabel cut i (C.rightNode L l) (C.rightLabel L l i a).val := by
  cases l with
  | first e => simp [alignedLabel, leftNode, rightNode, leftLabel, rightLabel, first_not_cut hl]
  | middle e j => simp only [alignedLabel, leftNode, rightNode, leftLabel, rightLabel,
      Fin.val_castSucc, Fin.val_succ, middle_not_cut hl]; rfl
  | last e => simp [alignedLabel, leftNode, rightNode, leftLabel, rightLabel, last_not_cut hl]

/-- Completed shifts solve every uncut type-shift equation, including shifted
last links and zero endpoint forms. -/
theorem completedShift_equation (cut : Cuts (E := E) (L := L))
    (h : ∀ t, Fin (C.dim t) → F) (b : E → F)
    (l : Link E L) (hl : l.position ≠ cut l.comparison) :
    C.leftForm L l (C.completedShift cut h b (C.leftNode L l)) -
      C.rightForm L l (C.completedShift cut h b (C.rightNode L l)) = linkConstant b l := by
  cases l with
  | first e =>
    change C.sourceForm e (h (C.source e)) -
      (if 0 < (cut e).val then C.sourceForm e (h (C.source e))
       else C.targetForm e (h (C.target e)) + b e) = 0
    rw [if_pos (first_not_cut hl), sub_self]
  | middle e i =>
    change (if i.val < (cut e).val then C.sourceForm e (h (C.source e))
      else C.targetForm e (h (C.target e)) + b e) -
      (if i.val + 1 < (cut e).val then C.sourceForm e (h (C.source e))
      else C.targetForm e (h (C.target e)) + b e) = 0
    simp only [middle_not_cut hl, sub_self]
  | last e =>
    change (if L < (cut e).val then C.sourceForm e (h (C.source e))
      else C.targetForm e (h (C.target e)) + b e) - C.targetForm e (h (C.target e)) = b e
    rw [if_neg (last_not_cut hl)]
    abel

end ComparisonData
end GroupWL.SourceLayout
