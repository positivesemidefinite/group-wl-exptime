import GroupWL.SourceLayout.GaugeExtension
import GroupWL.SourceLayout.RingEquations

/-! # The four distinct incidences in a square frame -/
set_option linter.unusedSectionVars false

namespace GroupWL.SourceLayout.ComparisonData

open scoped BigOperators
variable {F T E : Type*} [Field F] {n L : ℕ}
variable (C : ComparisonData F T E (n+3)) [Fintype T] [Fintype E]

 theorem squareLeft_ne_right (s : C.Square L) : C.squareLeft L s ≠ C.squareRight L s := by
  intro h
  exact C.link_nodes_ne s.1 (congrArg Sigma.fst h)

theorem squareAfter_ne_before (s : C.Square L) : C.squareAfter L s ≠ C.squareBefore L s := by
  intro h
  exact CyclicLifting.finRotate_no_fixed n s.2.1
    (congrArg (fun v : C.Vertical L => v.2.1) h)

theorem coefficient_square_left (s : C.Square L) (z : C.nodeSpace L (C.leftNode L s.1)) :
    C.coefficient (.inr s) (.inl (C.squareLeft L s)) z = C.leftForm L s.1 z := by
  classical
  change C.blockEquation L (.inr s) (Pi.single (.inl (C.squareLeft L s)) z) = _
  rw [blockEquation_square]
  simp [(C.squareLeft_ne_right s).symm]
  exact (C.rightForm L s.1).map_zero

theorem coefficient_square_right (s : C.Square L) (z : C.nodeSpace L (C.rightNode L s.1)) :
    C.coefficient (.inr s) (.inl (C.squareRight L s)) z = -C.rightForm L s.1 z := by
  classical
  change C.blockEquation L (.inr s) (Pi.single (.inl (C.squareRight L s)) z) = _
  rw [blockEquation_square]
  simp [C.squareLeft_ne_right s]
  exact (C.leftForm L s.1).map_zero

theorem coefficient_square_after (s : C.Square L) (z : F) :
    C.coefficient (.inr s) (.inr (C.squareAfter L s)) z = z := by
  classical
  change C.blockEquation L (.inr s) (Pi.single (.inr (C.squareAfter L s)) z) = _
  rw [blockEquation_square]
  simp [(C.squareAfter_ne_before s).symm]
  exact sub_eq_zero.mpr ((C.leftForm L s.1).map_zero.trans (C.rightForm L s.1).map_zero.symm)

theorem coefficient_square_before (s : C.Square L) (z : F) :
    C.coefficient (.inr s) (.inr (C.squareBefore L s)) z = -z := by
  classical
  change C.blockEquation L (.inr s) (Pi.single (.inr (C.squareBefore L s)) z) = _
  rw [blockEquation_square]
  simp [C.squareAfter_ne_before s]
  exact sub_eq_zero.mpr ((C.leftForm L s.1).map_zero.trans (C.rightForm L s.1).map_zero.symm)

theorem coefficient_site (h : C.Horizontal L) (j : C.Readout L)
    (z : C.readoutSpace L j) : C.coefficient (.inl h) j z = 0 := by
  simp [coefficient,blockEquation]

@[simp] theorem squareLeft_mem_scope (s : C.Square L) :
    Sum.inl (C.squareLeft L s) ∈ C.scope L (.inr s) := by classical simp [scope]
@[simp] theorem squareRight_mem_scope (s : C.Square L) :
    Sum.inl (C.squareRight L s) ∈ C.scope L (.inr s) := by classical simp [scope]
@[simp] theorem squareAfter_mem_scope (s : C.Square L) :
    Sum.inr (C.squareAfter L s) ∈ C.scope L (.inr s) := by classical simp [scope]
@[simp] theorem squareBefore_mem_scope (s : C.Square L) :
    Sum.inr (C.squareBefore L s) ∈ C.scope L (.inr s) := by classical simp [scope]

/-- The frame's scope sum really has these four distinct terms. -/
theorem sum_scope_square (s : C.Square L) (f : C.Readout L → F) :
    (∑ j ∈ C.scope L (.inr s), f j) =
      f (.inl (C.squareLeft L s)) + f (.inl (C.squareRight L s)) +
      f (.inr (C.squareAfter L s)) + f (.inr (C.squareBefore L s)) := by
  classical
  simp [scope,C.squareLeft_ne_right s,C.squareAfter_ne_before s,add_assoc]

@[simp] theorem squareAt_left (l : Link E L) (a : C.DomainAddress l.comparison) (i : Fin (n+3)) :
    C.squareLeft L (C.squareAt l a i) = C.ringReadout (C.leftNode L l) (C.leftAddress l a) i := rfl
@[simp] theorem squareAt_right (l : Link E L) (a : C.DomainAddress l.comparison) (i : Fin (n+3)) :
    C.squareRight L (C.squareAt l a i) = C.ringReadout (C.rightNode L l) (C.rightAddress l a) i := rfl
@[simp] theorem squareAt_after (l : Link E L) (a : C.DomainAddress l.comparison) (i : Fin (n+3)) :
    C.squareAfter L (C.squareAt l a i) =
      C.squareBefore L (C.squareAt l a (finRotate (n+3) i)) := rfl

end GroupWL.SourceLayout.ComparisonData
