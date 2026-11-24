import GroupWL.SourceLayout.MinimalWrapping

namespace GroupWL.SourceLayout.ComparisonData

variable {F T E : Type*} [Field F] {n L : ℕ}
variable (C : ComparisonData F T E (n + 3)) [Fintype T] [Fintype E]

def UsedCorner (S : Finset (C.Block L)) (v : C.Corner L) : Prop :=
  ∃ q ∈ C.usedReadouts S, v = C.readoutStart L q ∨ v = C.readoutEnd L q

theorem adj_usedCorners (S : Finset (C.Block L)) {u v : C.Corner L}
    (h : (C.cornerGraph S).Adj u v) : C.UsedCorner S u ∧ C.UsedCorner S v := by
  rcases h.2 with ⟨q, hq, rfl, rfl⟩ | ⟨q, hq, rfl, rfl⟩
  · exact ⟨⟨q, hq, Or.inl rfl⟩, ⟨q, hq, Or.inr rfl⟩⟩
  · exact ⟨⟨q, hq, Or.inr rfl⟩, ⟨q, hq, Or.inl rfl⟩⟩

theorem minimal_wrapping_used_connected (S : Finset (C.Block L))
    (hcard : S.card = n + 3) (hwrap : (C.wrappingLayout S).Wraps)
    {u v : C.Corner L} (hu : C.UsedCorner S u) (hv : C.UsedCorner S v) :
    (C.cornerGraph S).Reachable u v := by
  obtain ⟨w, p, hp⟩ := hwrap
  have hall := C.minimal_wrapping_connected S hcard w p hp
  have hreach {v : C.Corner L} (hv : C.UsedCorner S v) : (C.cornerGraph S).Reachable w v := by
    obtain ⟨q, hq, rfl | rfl⟩ := hv
    · exact (hall q hq).1
    · exact (hall q hq).2
  exact (hreach hu).symm.trans (hreach hv)

theorem usedCorner_of_wrappingAt (S : Finset (C.Block L)) (v : C.Corner L)
    (hv : ¬ NonwrappingAt (C.cornerGraph S) C.edgeMarker v) : C.UsedCorner S v := by
  classical
  obtain ⟨p, hp⟩ := not_forall.mp hv
  cases p with
  | nil => exact False.elim (hp rfl)
  | cons h p => exact (C.adj_usedCorners S h).1

def ShiftEquations (S : Finset (C.Block L)) (b : E → F) (h : C.TypeShift (L := L)) : Prop :=
  ∀ l ∈ C.activeLinks S,
    C.leftForm L l (h (C.leftNode L l)) - C.rightForm L l (h (C.rightNode L l)) =
      linkConstant b l

theorem vertical_shift_eq_iff (S : Finset (C.Block L)) (b : E → F)
    (old new : C.TypeShift (L := L)) (ho : C.ShiftEquations S b old)
    (hn : C.ShiftEquations S b new)
    (hreal : ∀ (t : T) (i : Fin (n + 3)) (a : C.Label L (.inl t) i),
      C.UsedCorner S ⟨.inl t, i, a⟩ → new (.inl t) = old (.inl t))
    (v : C.Vertical L) (hv : Sum.inr v ∈ C.usedReadouts S) :
    new (C.leftNode L v.1) = old (C.leftNode L v.1) ↔
      new (C.rightNode L v.1) = old (C.rightNode L v.1) := by
  have hl := C.vertical_link_mem_active S v hv
  have heo := ho v.1 hl
  have hen := hn v.1 hl
  obtain ⟨l, i, a⟩ := v
  cases l with
  | first e =>
    have h := hreal (C.source e) i (C.leftLabel L (.first e) i a)
      ⟨.inr ⟨.first e, i, a⟩, hv, Or.inl rfl⟩
    change C.sourceForm e (old (.inl (C.source e))) - old (.inr (e, 0)) = 0 at heo
    change C.sourceForm e (new (.inl (C.source e))) - new (.inr (e, 0)) = 0 at hen
    rw [h] at hen
    have hi : new (.inr (e, 0)) = old (.inr (e, 0)) := by linear_combination heo - hen
    exact ⟨fun _ => hi, fun _ => h⟩
  | middle e j =>
    change old (.inr (e, j.castSucc)) - old (.inr (e, j.succ)) = 0 at heo
    change new (.inr (e, j.castSucc)) - new (.inr (e, j.succ)) = 0 at hen
    constructor
    · intro h
      change new (.inr (e, j.castSucc)) = old (.inr (e, j.castSucc)) at h
      change new (.inr (e, j.succ)) = old (.inr (e, j.succ))
      linear_combination heo - hen + h
    · intro h
      change new (.inr (e, j.succ)) = old (.inr (e, j.succ)) at h
      change new (.inr (e, j.castSucc)) = old (.inr (e, j.castSucc))
      linear_combination hen - heo + h
  | last e =>
    have h := hreal (C.target e) i (C.rightLabel L (.last e) i a)
      ⟨.inr ⟨.last e, i, a⟩, hv, Or.inr rfl⟩
    change old (.inr (e, Fin.last L)) - C.targetForm e (old (.inl (C.target e))) = b e at heo
    change new (.inr (e, Fin.last L)) - C.targetForm e (new (.inl (C.target e))) = b e at hen
    rw [h] at hen
    have hi : new (.inr (e, Fin.last L)) = old (.inr (e, Fin.last L)) := by
      linear_combination hen - heo
    exact ⟨fun _ => h, fun _ => hi⟩

/-- Once real-type shifts are fixed, equality at one corner propagates along
the component, since all internal type spaces are one-dimensional. -/
theorem shift_eq_of_walk (S : Finset (C.Block L)) (b : E → F)
    (old new : C.TypeShift (L := L)) (ho : C.ShiftEquations S b old)
    (hn : C.ShiftEquations S b new)
    (hreal : ∀ (t : T) (i : Fin (n + 3)) (a : C.Label L (.inl t) i),
      C.UsedCorner S ⟨.inl t, i, a⟩ → new (.inl t) = old (.inl t))
    {u v : C.Corner L} (p : (C.cornerGraph S).Walk u v)
    (hu : new u.1 = old u.1) : new v.1 = old v.1 := by
  induction p with
  | nil => exact hu
  | @cons u v w h p ih =>
    apply ih
    rcases h.2 with ⟨q, hq, rfl, rfl⟩ | ⟨q, hq, rfl, rfl⟩
    · cases q with
      | inl h => exact hu
      | inr w => exact (C.vertical_shift_eq_iff S b old new ho hn hreal w hq).mp hu
    · cases q with
      | inl h => exact hu
      | inr w => exact (C.vertical_shift_eq_iff S b old new ho hn hreal w hq).mpr hu

end GroupWL.SourceLayout.ComparisonData
