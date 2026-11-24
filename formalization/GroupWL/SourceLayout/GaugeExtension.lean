import GroupWL.SourceLayout.PotentialAssignments
import GroupWL.SourceLayout.CornerGraph
import GroupWL.SourceLayout.NonwrappingPotential

namespace GroupWL.SourceLayout.ComparisonData

variable {F T E : Type*} [Field F] {n L : ℕ}
variable (C : ComparisonData F T E (n + 3))
variable [Fintype T] [Fintype E]

theorem link_nodes_ne (l : Link E L) : C.leftNode L l ≠ C.rightNode L l := by
  cases l with
  | first e => simp [leftNode, rightNode]
  | middle e i =>
    intro h
    have hv := congrArg (fun p : E × Fin (L + 1) => p.2.val) (Sum.inr.inj h)
    simp [leftNode, rightNode] at hv
  | last e => simp [leftNode, rightNode]

theorem readout_endpoints_ne (q : C.Readout L) : C.readoutStart L q ≠ C.readoutEnd L q := by
  cases q with
  | inl h =>
    intro heq
    have hr := congrArg C.cornerRow heq
    exact CyclicLifting.finRotate_no_fixed n h.2.1 hr.symm
  | inr v =>
    intro heq
    exact C.link_nodes_ne v.1 (congrArg Sigma.fst heq)

theorem readout_adj (S : Finset (C.Block L)) (q : C.Readout L) (hq : q ∈ C.usedReadouts S) :
    (C.cornerGraph S).Adj (C.readoutStart L q) (C.readoutEnd L q) :=
  ⟨C.readout_endpoints_ne q, Or.inl ⟨q, hq, rfl, rfl⟩⟩

theorem vertical_link_mem_active (S : Finset (C.Block L)) (v : C.Vertical L)
    (hv : Sum.inr v ∈ C.usedReadouts S) : v.1 ∈ C.activeLinks S := by
  classical
  obtain ⟨B, hB, hvB⟩ := Finset.mem_biUnion.mp hv
  cases B with
  | inl h => simpa [affineSystem, scope] using hvB
  | inr s =>
    have heq : v = C.squareAfter L s ∨ v = C.squareBefore L s := by
      simpa [affineSystem, scope] using hvB
    rcases heq with rfl | rfl <;> exact C.square_link_mem_active hB

theorem rowMarker_eq_seamMarker (i : Fin (n + 3)) :
    (rowMarker i : F) = Wrapping.seamMarker (n + 2) 1 i := by
  by_cases hi : i = Fin.last (n + 2)
  · subst i
    simp [rowMarker, Wrapping.seamMarker]
  · have hn : i.val + 1 ≠ n + 3 := by
      intro h
      apply hi
      apply Fin.ext
      simp
      omega
    simp only [rowMarker, Wrapping.seamMarker, if_neg hi, if_neg hn]

/-- Changing type shifts while preserving them on old wrapping components
extends every old potential assignment without changing any old readout. -/
theorem gauge_extension (S : Finset (C.Block L)) (b : E → F)
    (old new : C.TypeShift (L := L)) (M : C.CornerPotential (L := L))
    (hold : ∀ l ∈ C.activeLinks S,
      C.leftForm L l (old (C.leftNode L l)) - C.rightForm L l (old (C.rightNode L l)) =
        linkConstant b l)
    (hnew : ∀ l ∈ C.activeLinks S,
      C.leftForm L l (new (C.leftNode L l)) - C.rightForm L l (new (C.rightNode L l)) =
        linkConstant b l)
    (hkeep : ∀ v : C.Corner L,
      ¬ NonwrappingAt (C.cornerGraph S) C.edgeMarker v → new v.1 = old v.1) :
    ∃ M' : C.CornerPotential (L := L), ∀ q ∈ C.usedReadouts S,
      C.potentialAssignment new M' q = C.potentialAssignment old M q := by
  classical
  obtain ⟨s, hs⟩ := exists_nonwrapping_potential (C.cornerGraph S) C.edgeMarker
  let M' : C.CornerPotential (L := L) := fun v => M v + s v • (new v.1 - old v.1)
  refine ⟨M', ?_⟩
  intro q hq
  have hadj := C.readout_adj S q hq
  have hpot := hs _ _ hadj
  cases q with
  | inl h =>
    let u : C.Corner L := ⟨h.1, h.2.1, h.2.2.1⟩
    let v : C.Corner L := ⟨h.1, finRotate (n + 3) h.2.1, h.2.2.2⟩
    change (if NonwrappingAt (C.cornerGraph S) C.edgeMarker u then C.edgeMarker u v else 0) =
      s v - s u at hpot
    by_cases hu : NonwrappingAt (C.cornerGraph S) C.edgeMarker u
    · have hmarker : (rowMarker h.2.1 : F) = s v - s u := by
        rw [if_pos hu] at hpot
        have hm := C.marker_forward (u := u) (v := v) rfl
        exact (rowMarker_eq_seamMarker (F := F) h.2.1).trans (hm.symm.trans hpot)
      exact GraphPotentials.horizontal_gauge_preserves (M u) (M v) (old h.1) (new h.1)
        (s u) (s v) (rowMarker h.2.1) hmarker
    · have hk : new h.1 = old h.1 := hkeep u hu
      change (M u + s u • (new h.1 - old h.1)) -
        (M v + s v • (new h.1 - old h.1)) + (rowMarker h.2.1 : F) • new h.1 =
        M u - M v + (rowMarker h.2.1 : F) • old h.1
      rw [hk, sub_self, smul_zero, smul_zero, add_zero, add_zero]
  | inr w =>
    let u := C.verticalStart L w
    let v := C.verticalEnd L w
    change (if NonwrappingAt (C.cornerGraph S) C.edgeMarker u then C.edgeMarker u v else 0) =
      s v - s u at hpot
    have hz : C.edgeMarker u v = 0 := C.marker_same_row rfl
    have heq : s u = s v := by
      have hpot' : (0 : F) = s v - s u := by simpa only [hz, ite_self] using hpot
      exact (sub_eq_zero.mp hpot'.symm).symm
    have hg := GraphPotentials.shift_difference_compatible
      (C.leftForm L w.1) (C.rightForm L w.1)
      (old (C.leftNode L w.1)) (new (C.leftNode L w.1))
      (old (C.rightNode L w.1)) (new (C.rightNode L w.1)) (linkConstant b w.1)
      (hold w.1 (C.vertical_link_mem_active S w hq))
      (hnew w.1 (C.vertical_link_mem_active S w hq))
    exact GraphPotentials.vertical_gauge_preserves (C.leftForm L w.1) (C.rightForm L w.1)
      (M u) (M v) (new u.1 - old u.1) (new v.1 - old v.1) (s u) (s v) heq hg

end GroupWL.SourceLayout.ComparisonData
