import GroupWL.ConstructiveSourceTensor

/-! Explicit source-matrix entries, retaining zero-coefficient incidences. -/
namespace GroupWL.SourceTableCoefficients

open SourceLayout ConstructiveCoordinates

variable {F T E : Type} [Field F] [DecidableEq F]
  {r : ℕ} (C : ComparisonData F T E r) (L : ℕ)
variable [FiniteCode (C.Readout L)]

local instance : DecidableEq (C.Readout L) := (FiniteCode.equiv (α := C.Readout L)).decidableEq

def unit (j : C.Readout L) (k : ℕ) : C.readoutSpace L j :=
  (ComputableSource.readoutCoordinates C j).equiv.symm (fun i => if i.val = k then 1 else 0)

def entry (B : C.Block L) (j : C.Readout L) (k : ℕ) : F :=
  ComputableSource.coefficient C B j (unit C L j k)

def leftEntry (s : C.Square L) (k : ℕ) : F :=
  C.leftForm L s.1 (unit C L (.inl (C.squareLeft L s)) k)

def rightEntry (s : C.Square L) (k : ℕ) : F :=
  C.rightForm L s.1 (unit C L (.inl (C.squareRight L s)) k)

@[simp] theorem unit_vertical (v : C.Vertical L) (k : ℕ) :
    unit C L (.inr v) k = if k = 0 then 1 else 0 := by
  change (if (0 : ℕ) = k then (1 : F) else 0) = _
  simp only [eq_comm]

@[simp] theorem entry_site (h : C.Horizontal L) (j : C.Readout L) (k : ℕ) :
    entry C L (.inl h) j k = 0 := rfl

theorem entry_square (s : C.Square L) (j : C.Readout L) (k : ℕ) :
    entry C L (.inr s) j k =
      (if j = .inl (C.squareLeft L s) then leftEntry C L s k else 0) -
      (if j = .inl (C.squareRight L s) then rightEntry C L s k else 0) +
      (if j = .inr (C.squareAfter L s) ∧ k = 0 then 1 else 0) -
      (if j = .inr (C.squareBefore L s) ∧ k = 0 then 1 else 0) := by
  change C.leftForm L s.1 ((Pi.single j (unit C L j k)) (.inl (C.squareLeft L s))) -
    C.rightForm L s.1 ((Pi.single j (unit C L j k)) (.inl (C.squareRight L s))) +
    (Pi.single j (unit C L j k)) (.inr (C.squareAfter L s)) -
    (Pi.single j (unit C L j k)) (.inr (C.squareBefore L s)) = _
  have hl : C.leftForm L s.1 ((Pi.single j (unit C L j k)) (.inl (C.squareLeft L s))) =
      if j = .inl (C.squareLeft L s) then leftEntry C L s k else 0 := by
    by_cases h : j = .inl (C.squareLeft L s)
    · subst j; simp [leftEntry]
    · rw [Pi.single_eq_of_ne (Ne.symm h)]
      simp only [if_neg h]
      exact (C.leftForm L s.1).map_zero
  have hr : C.rightForm L s.1 ((Pi.single j (unit C L j k)) (.inl (C.squareRight L s))) =
      if j = .inl (C.squareRight L s) then rightEntry C L s k else 0 := by
    by_cases h : j = .inl (C.squareRight L s)
    · subst j; simp [rightEntry]
    · rw [Pi.single_eq_of_ne (Ne.symm h)]
      simp only [if_neg h]
      exact (C.rightForm L s.1).map_zero
  have hv (v : C.Vertical L) : (Pi.single j (unit C L j k)) (.inr v) =
      if j = .inr v ∧ k = 0 then 1 else 0 := by
    by_cases h : j = .inr v
    · subst j; simp
    · rw [Pi.single_eq_of_ne (Ne.symm h)]
      simp [h]
  rw [hl,hr,hv,hv]

theorem scope_site (h : C.Horizontal L) (j : C.Readout L) :
    j ∈ ComputableSource.scope C (.inl h) ↔ j = .inl h := by
  simp [ComputableSource.scope]

theorem scope_square (s : C.Square L) (j : C.Readout L) :
    j ∈ ComputableSource.scope C (.inr s) ↔
      j = .inl (C.squareLeft L s) ∨ j = .inl (C.squareRight L s) ∨
      j = .inr (C.squareAfter L s) ∨ j = .inr (C.squareBefore L s) := by
  simp [ComputableSource.scope]

end GroupWL.SourceTableCoefficients
