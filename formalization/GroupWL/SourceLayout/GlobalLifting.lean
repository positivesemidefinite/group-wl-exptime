import GroupWL.SourceLayout.ComparisonRows

/-! Global lifting from real-type row functions to all site-and-square equations. -/
namespace GroupWL.SourceLayout.ComparisonData

open scoped BigOperators

variable {F T E : Type*} [Field F] {n L : ℕ}
  (C : ComparisonData F T E (n+3))

abbrev RealRows := ∀ t : T, Fin (n+3) → Bool → Bool → (Fin (C.dim t) → F)

def realRowValue (R : C.RealRows) (t : T) (a : C.RealAddress) : Fin (C.dim t) → F :=
  ∑ i, R t i (a i) (a (finRotate (n+3) i))

private def rowPrefix {L : ℕ} (f : Fin L → F) (j : ℕ) : F :=
  ∑ k ∈ Finset.range j, if hk : k < L then f ⟨k,hk⟩ else 0

private theorem rowPrefix_zero (f : Fin L → F) : rowPrefix f 0 = 0 := by simp [rowPrefix]

private theorem rowPrefix_succ (f : Fin L → F) (j : Fin L) :
    rowPrefix f j.succ.val = rowPrefix f j.castSucc.val + f j := by
  simp [rowPrefix, Finset.sum_range_succ, j.isLt]

private theorem rowPrefix_last (f : Fin L → F) : rowPrefix f L = ∑ k, f k := by
  rw [rowPrefix, ← Fin.sum_univ_eq_sum_range]
  simp

/-- Real rows extend down each private wire by subtracting the actual preceding
square charges. This extension makes the first and middle squares exact before
any vertical potentials are introduced. -/
noncomputable def extendedRows (β : C.Block L → F) (R : C.RealRows) :
    ∀ h : C.Horizontal L, C.nodeSpace L h.1
  | ⟨.inl t,i,u,v⟩ => R t i u.val v.val
  | ⟨.inr (e,j),i,u,v⟩ =>
      C.sourceForm e (R (C.source e) i u.val v.val) -
        β (.inr ⟨.first e,i,u,v⟩) -
        rowPrefix (fun k : Fin L => β (.inr ⟨.middle e k,i,u,v⟩)) j.val

private theorem extended_first (β : C.Block L → F) (R : C.RealRows)
    (e : E) (i : Fin (n+3)) (u : C.DomainLabel e i)
    (v : C.DomainLabel e (finRotate (n+3) i)) :
    C.leftForm L (.first e) (C.extendedRows β R (C.squareLeft L ⟨.first e,i,u,v⟩)) -
      C.rightForm L (.first e) (C.extendedRows β R (C.squareRight L ⟨.first e,i,u,v⟩)) =
        β (.inr ⟨.first e,i,u,v⟩) := by
  change C.sourceForm e (R (C.source e) i u.val v.val) -
    (C.sourceForm e (R (C.source e) i u.val v.val) - β (.inr ⟨.first e,i,u,v⟩) -
      rowPrefix _ 0) = _
  rw [rowPrefix_zero]
  ring

private theorem extended_middle (β : C.Block L → F) (R : C.RealRows)
    (e : E) (j : Fin L) (i : Fin (n+3)) (u : C.DomainLabel e i)
    (v : C.DomainLabel e (finRotate (n+3) i)) :
    C.leftForm L (.middle e j) (C.extendedRows β R (C.squareLeft L ⟨.middle e j,i,u,v⟩)) -
      C.rightForm L (.middle e j) (C.extendedRows β R (C.squareRight L ⟨.middle e j,i,u,v⟩)) =
        β (.inr ⟨.middle e j,i,u,v⟩) := by
  change (C.sourceForm e (R (C.source e) i u.val v.val) -
    β (.inr ⟨.first e,i,u,v⟩) - rowPrefix _ j.castSucc.val) -
    (C.sourceForm e (R (C.source e) i u.val v.val) -
    β (.inr ⟨.first e,i,u,v⟩) - rowPrefix _ j.succ.val) = _
  rw [rowPrefix_succ]
  dsimp only [leftLabel, rightLabel]
  ring

private theorem extended_last (β : C.Block L → F) (R : C.RealRows)
    (e : E) (i : Fin (n+3)) (u : C.DomainLabel e i)
    (v : C.DomainLabel e (finRotate (n+3) i)) :
    C.leftForm L (.last e) (C.extendedRows β R (C.squareLeft L ⟨.last e,i,u,v⟩)) -
      C.rightForm L (.last e) (C.extendedRows β R (C.squareRight L ⟨.last e,i,u,v⟩)) =
      C.sourceForm e (R (C.source e) i u.val v.val) -
      C.targetForm e (R (C.target e) i (C.permutation e i u.val)
        (C.permutation e (finRotate (n+3) i) v.val)) -
      β (.inr ⟨.first e,i,u,v⟩) -
      ∑ k : Fin L, β (.inr ⟨.middle e k,i,u,v⟩) := by
  change (C.sourceForm e (R (C.source e) i u.val v.val) -
    β (.inr ⟨.first e,i,u,v⟩) - rowPrefix _ L) - _ = _
  rw [rowPrefix_last]
  dsimp only [leftLabel, rightLabel, rightForm, squareRight, extendedRows, rightNode]
  ring_nf
  rfl

/-- Every complete comparison equation between real row sums has a simultaneous
solution of all individual squares, with no conditions on the square charges. -/
theorem exists_global_solution [Fintype T] [Fintype E]
    (β : C.Block L → F) (R : C.RealRows)
    (hsite : ∀ h : C.Horizontal L, β (.inl h) = 0)
    (hrows : ∀ e (a : C.DomainAddress e),
      C.sourceForm e (C.realRowValue R (C.source e) (C.sourceAddress a)) -
        C.targetForm e (C.realRowValue R (C.target e) (C.targetAddress a)) =
      C.comparisonDelta β e a) :
    β ∈ LinearMap.range (C.affineSystem (L := L)).linearMap := by
  classical
  let horizontal := C.extendedRows β R
  have hlast (e : E) : ∃ Y : Fin (n+3) → Bool → F,
      ∀ i (u : C.DomainLabel e i) (v : C.DomainLabel e (finRotate (n+3) i)),
      C.leftForm L (.last e) (horizontal (C.squareLeft L ⟨.last e,i,u,v⟩)) -
        C.rightForm L (.last e) (horizontal (C.squareRight L ⟨.last e,i,u,v⟩)) +
        Y (finRotate (n+3) i) v.val - Y i u.val = β (.inr ⟨.last e,i,u,v⟩) := by
    let left : Fin (n+3) → Bool → Bool → F := fun i u v =>
      if hu : u ∈ C.domain e i then
        if hv : v ∈ C.domain e (finRotate (n+3) i) then
          horizontal (C.squareLeft L ⟨.last e,i,⟨u,hu⟩,⟨v,hv⟩⟩)
        else 0
      else 0
    let right : Fin (n+3) → Bool → Bool → F := fun i u v =>
      C.targetForm e (R (C.target e) i (C.permutation e i u)
        (C.permutation e (finRotate (n+3) i) v))
    let charge : Fin (n+3) → Bool → Bool → F := fun i u v =>
      if hu : u ∈ C.domain e i then
        if hv : v ∈ C.domain e (finRotate (n+3) i) then
          β (.inr ⟨.last e,i,⟨u,hu⟩,⟨v,hv⟩⟩)
        else 0
      else 0
    have hl (i) (u : C.DomainLabel e i) (v : C.DomainLabel e (finRotate (n+3) i)) :
        left i u.val v.val - right i u.val v.val =
        C.sourceForm e (R (C.source e) i u.val v.val) -
          C.targetForm e (R (C.target e) i (C.permutation e i u.val)
            (C.permutation e (finRotate (n+3) i) v.val)) -
          β (.inr ⟨.first e,i,u,v⟩) -
          ∑ k : Fin L, β (.inr ⟨.middle e k,i,u,v⟩) := by
      simpa only [left, right, dif_pos u.property, dif_pos v.property] using
        C.extended_last β R e i u v
    have hr (a : Fin (n+3) → Bool) (ha : ∀ i, a i ∈ (C.domain e i : Set Bool)) :
        (∑ i, (left i (a i) (a (finRotate (n+3) i)) -
          right i (a i) (a (finRotate (n+3) i)))) =
        ∑ i, charge i (a i) (a (finRotate (n+3) i)) := by
      change ∀ i, a i ∈ C.domain e i at ha
      let ad : C.DomainAddress e := fun i => ⟨a i,ha i⟩
      have h := hrows e ad
      simp only [realRowValue, map_sum] at h
      simp_rw [show ∀ i, left i (a i) (a (finRotate (n+3) i)) -
          right i (a i) (a (finRotate (n+3) i)) =
          C.sourceForm e (R (C.source e) i (a i) (a (finRotate (n+3) i))) -
          C.targetForm e (R (C.target e) i (C.permutation e i (a i))
            (C.permutation e (finRotate (n+3) i) (a (finRotate (n+3) i)))) -
          β (.inr ⟨.first e,i,ad i,ad (finRotate (n+3) i)⟩) -
          ∑ k : Fin L, β (.inr ⟨.middle e k,i,ad i,ad (finRotate (n+3) i)⟩) from
        fun i => hl i (ad i) (ad (finRotate (n+3) i))]
      simp only [Finset.sum_sub_distrib]
      simp only [comparisonDelta, linkDelta] at h
      rw [Finset.sum_comm] at h
      have hc (i : Fin (n+3)) : charge i (a i) (a (finRotate (n+3) i)) =
          β (.inr ⟨.last e,i,ad i,ad (finRotate (n+3) i)⟩) := by
        simp only [charge, dif_pos (ha i), dif_pos (ha (finRotate (n+3) i))]
        rfl
      simp_rw [hc]
      dsimp [sourceAddress, targetAddress, ad, squareAt] at h
      linear_combination h
    obtain ⟨Y,hY⟩ := CyclicLifting.lift_square_equations n left right charge
      (fun i => (C.domain e i : Set Bool)) (fun i => C.domain_nonempty e i) hr
    refine ⟨Y, ?_⟩
    intro i u v
    simpa only [left, right, charge, dif_pos u.property, dif_pos v.property] using
      hY i u.val v.val u.property v.property
  choose Y hY using hlast
  let z : C.Assignment L
    | .inl h => horizontal h
    | .inr ⟨.first _,_,_⟩ => 0
    | .inr ⟨.middle _ _,_,_⟩ => 0
    | .inr ⟨.last e,i,u⟩ => Y e i u.val
  refine ⟨z, (C.solves_iff β z).mpr ?_⟩
  intro B
  rcases B with h | ⟨l,i,u,v⟩
  · exact (C.blockEquation_site L h z).trans (hsite h).symm
  · cases l with
    | first e =>
      simpa only [blockEquation_square, z, squareAfter, squareBefore, add_zero, sub_zero]
        using C.extended_first β R e i u v
    | middle e j =>
      simpa only [blockEquation_square, z, squareAfter, squareBefore, add_zero, sub_zero]
        using C.extended_middle β R e j i u v
    | last e => exact hY e i u v

end GroupWL.SourceLayout.ComparisonData
