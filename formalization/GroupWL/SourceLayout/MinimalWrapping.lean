import GroupWL.SourceLayout.WrappingAddress

namespace GroupWL.SourceLayout

open GraphPotentials

/-- Transfer a walk when every edge in its initial connected component is
present in the new graph. Its marker integral is unchanged. -/
theorem transfer_walk_in_component {V K : Type*} [AddCommGroup K]
    (G H : SimpleGraph V) (m : V → V → K) (root : V)
    (hedge : ∀ u v, G.Reachable root u → G.Adj u v → H.Adj u v)
    {u v : V} (p : G.Walk u v) (hu : G.Reachable root u) :
    ∃ q : H.Walk u v, integral m q = integral m p := by
  induction p with
  | nil => exact ⟨.nil, rfl⟩
  | @cons u v w h p ih =>
    obtain ⟨q, hq⟩ := ih (hu.trans h.reachable)
    exact ⟨.cons (hedge u v hu h) q, by simp only [integral_cons, hq]⟩

namespace ComparisonData

variable {F T E : Type*} [Field F] {n L : ℕ}
variable (C : ComparisonData F T E (n + 3))
variable [Fintype T] [Fintype E]

def blockBase : C.Block L → C.Corner L
  | .inl h => C.horizontalStart L h
  | .inr s => C.horizontalStart L (C.squareLeft L s)

theorem scope_subset_used {S : Finset (C.Block L)} {B : C.Block L} (hB : B ∈ S) :
    C.scope L B ⊆ C.usedReadouts S := by
  intro q hq
  exact Finset.mem_biUnion.mpr ⟨B, hB, hq⟩

/-- The one-edge site and the four-edge square each have connected support. -/
theorem block_support_connected (S : Finset (C.Block L)) (B : C.Block L) (hB : B ∈ S)
    (q : C.Readout L) (hq : q ∈ C.scope L B) :
    (C.cornerGraph S).Reachable (C.blockBase B) (C.readoutStart L q) ∧
    (C.cornerGraph S).Reachable (C.blockBase B) (C.readoutEnd L q) := by
  classical
  have he (q : C.Readout L) (hq : q ∈ C.scope L B) :=
    (C.readout_adj S q (C.scope_subset_used hB hq)).reachable
  cases B with
  | inl h =>
    have hq' : q = Sum.inl h := by simpa [scope] using hq
    subst q
    exact ⟨.rfl, he (Sum.inl h) (by simp [scope])⟩
  | inr s =>
    have hleft := he (Sum.inl (C.squareLeft L s)) (by simp [scope])
    have hright := he (Sum.inl (C.squareRight L s)) (by simp [scope])
    have hbefore := he (Sum.inr (C.squareBefore L s)) (by simp [scope])
    have hafter := he (Sum.inr (C.squareAfter L s)) (by simp [scope])
    have hq' : q = Sum.inl (C.squareLeft L s) ∨ q = Sum.inl (C.squareRight L s) ∨
        q = Sum.inr (C.squareAfter L s) ∨ q = Sum.inr (C.squareBefore L s) := by
      simpa [scope] using hq
    rcases hq' with rfl | rfl | rfl | rfl
    · exact ⟨.rfl, hleft⟩
    · exact ⟨hbefore, hbefore.trans hright⟩
    · exact ⟨hleft, hleft.trans hafter⟩
    · exact ⟨.rfl, hbefore⟩

/-- With exactly one block per row, a wrapping component contains every
readout: a disjoint block could be discarded, violating the wrapping bound. -/
theorem minimal_wrapping_connected (S : Finset (C.Block L))
    (hcard : S.card = n + 3) (u : C.Corner L)
    (p : (C.cornerGraph S).Walk u u) (hp : integral C.edgeMarker p ≠ 0) :
    ∀ q ∈ C.usedReadouts S,
      (C.cornerGraph S).Reachable u (C.readoutStart L q) ∧
      (C.cornerGraph S).Reachable u (C.readoutEnd L q) := by
  classical
  let R := S.filter (fun B => (C.cornerGraph S).Reachable u (C.blockBase B))
  have hsub : R ⊆ S := Finset.filter_subset _ _
  have hedge (v w : C.Corner L) (hv : (C.cornerGraph S).Reachable u v)
      (hvw : (C.cornerGraph S).Adj v w) : (C.cornerGraph R).Adj v w := by
    refine ⟨hvw.1, ?_⟩
    rcases hvw.2 with ⟨q, hq, rfl, rfl⟩ | ⟨q, hq, rfl, rfl⟩
    · obtain ⟨B, hB, hqB⟩ := Finset.mem_biUnion.mp hq
      have hbase := hv.trans (C.block_support_connected S B hB q hqB).1.symm
      exact Or.inl ⟨q, C.scope_subset_used (Finset.mem_filter.mpr ⟨hB, hbase⟩) hqB, rfl, rfl⟩
    · obtain ⟨B, hB, hqB⟩ := Finset.mem_biUnion.mp hq
      have hbase := hv.trans (C.block_support_connected S B hB q hqB).2.symm
      exact Or.inr ⟨q, C.scope_subset_used (Finset.mem_filter.mpr ⟨hB, hbase⟩) hqB, rfl, rfl⟩
  obtain ⟨p', hp'⟩ := transfer_walk_in_component (C.cornerGraph S) (C.cornerGraph R)
    C.edgeMarker u hedge p (.refl u)
  have hwrap : (C.wrappingLayout R).Wraps := by
    refine ⟨u, p', ?_⟩
    change integral C.edgeMarker p' ≠ 0
    rw [hp']
    exact hp
  have heq : R = S := Finset.eq_of_subset_of_card_le hsub
    (by rw [hcard]; exact C.wrapping_card_bound R hwrap)
  intro q hq
  obtain ⟨B, hB, hqB⟩ := Finset.mem_biUnion.mp hq
  have hBR : B ∈ R := heq.symm ▸ hB
  have hbase := (Finset.mem_filter.mp hBR).2
  exact ⟨hbase.trans (C.block_support_connected S B hB q hqB).1,
    hbase.trans (C.block_support_connected S B hB q hqB).2⟩

end ComparisonData
end GroupWL.SourceLayout
