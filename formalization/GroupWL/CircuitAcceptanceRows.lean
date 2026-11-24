import GroupWL.CircuitAcceptanceValues
import GroupWL.SourceLayout.GlobalLifting

/-! Actual row decompositions of the accepting circuit's scalar values. -/
namespace GroupWL.CircuitComparisons

open AddressedCircuit SourceLayout SourceLayout.ComparisonData
open scoped BigOperators

variable {T F : Type*} {n L : ℕ} [Field F] (C : Circuit T (n+3))
  (β : (comparisons C F).Block L → F) (Q : (comparisons C F).ImageSets)
  (hQ : (comparisons C F).ScalarImages β Q) (hacc : C.Accepts)

/-- The identity buffers give an explicit row formula for every primary
coordinate. The dummy is assigned zero, as its comparison form is zero. -/
noncomputable def primaryRows :
    ∀ t : Primary T, Fin (n+3) → Bool → Bool → (Fin (primaryDim C t) → F)
  | .gate t, i, u, v, j =>
      (comparisons C F).comparisonRows β (.copy (.identity t j) false) i u v +
      (comparisons C F).comparisonRows β (.copy (.identity t j) true) i u v +
      (comparisons C F).comparisonRows β (.sum (.identity t j)) i u v
  | .broadcast, i, u, v, _ =>
      (comparisons C F).comparisonRows β (.copy (.broadcastIdentity false) false) i u v +
      (comparisons C F).comparisonRows β (.copy (.broadcastIdentity false) true) i u v +
      (comparisons C F).comparisonRows β (.sum (.broadcastIdentity false)) i u v
  | .dummy, _, _, _, _ => 0

include hQ hacc in
theorem primaryRows_gate_sum (t : T) (a : Address (n+3)) :
    (∑ i, primaryRows C β (.gate t) i (a i) (a (finRotate (n+3) i))) =
      chosenValue C β Q hQ (.inl (.gate t)) a := by
  funext j
  have h := chosen_gate_identity C β Q hQ hacc t a j
  simp only [(comparisons C F).comparisonDelta_eq_sum_rows,
    identityCopyAddress, identitySumAddress] at h
  simpa only [Finset.sum_apply, primaryRows, Finset.sum_add_distrib] using h.symm

include hQ hacc in
theorem primaryRows_broadcast_sum (a : Address (n+3)) :
    (∑ i, primaryRows C β .broadcast i (a i) (a (finRotate (n+3) i))) =
      chosenValue C β Q hQ (.inl .broadcast) a := by
  funext j
  change Fin 1 at j
  have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
  subst j
  have h := chosen_broadcast_identity C β Q hQ hacc a
  simp only [(comparisons C F).comparisonDelta_eq_sum_rows,
    broadcastIdentityCopyAddress, broadcastIdentitySumAddress] at h
  simpa only [Finset.sum_apply, primaryRows, Finset.sum_add_distrib] using h.symm

include hQ hacc in
theorem primaryRows_source_sum (e : Connection C) (a : Address (n+3)) :
    (∑ i, primaryRows C β (e.source C) i (a i) (a (finRotate (n+3) i))) =
      chosenValue C β Q hQ (.inl (e.source C)) a := by
  cases e with
  | circuit e => exact primaryRows_gate_sum C β Q hQ hacc _ a
  | test k => exact primaryRows_gate_sum C β Q hQ hacc _ a
  | flip i => exact primaryRows_broadcast_sum C β Q hQ hacc a
  | broadcast t j => exact primaryRows_broadcast_sum C β Q hQ hacc a
  | identity t j => exact primaryRows_gate_sum C β Q hQ hacc _ a
  | broadcastIdentity b => exact primaryRows_broadcast_sum C β Q hQ hacc a

include hQ hacc in
theorem primaryRows_target_sum (e : Connection C) (a : Address (n+3)) :
    (∑ i, primaryRows C β (e.target C) i (a i) (a (finRotate (n+3) i))) =
      chosenValue C β Q hQ (.inl (e.target C)) a := by
  cases e with
  | circuit e => exact primaryRows_gate_sum C β Q hQ hacc _ a
  | test k => exact primaryRows_broadcast_sum C β Q hQ hacc a
  | flip i => exact primaryRows_broadcast_sum C β Q hQ hacc a
  | broadcast t j => exact primaryRows_gate_sum C β Q hQ hacc _ a
  | identity t j => exact primaryRows_gate_sum C β Q hQ hacc _ a
  | broadcastIdentity b => exact primaryRows_broadcast_sum C β Q hQ hacc a

/-- On a buffer's active domain, each coordinate is the source scalar minus
its copy-comparison shift. The same formula extends its rows to all labels. -/
noncomputable def acceptingRows : (comparisons C F).RealRows
  | .inl t, i, u, v => primaryRows C β t i u v
  | .inr e, i, u, v => fun j : Fin 2 =>
      e.sourceForm C F (primaryRows C β (e.source C) i u v) -
        (comparisons C F).comparisonRows β (.copy e (j.val = 1)) i u v

include hQ hacc in
theorem acceptingRows_buffer_sum (e : Connection C) (a : ConnectionAddress C e) :
    (comparisons C F).realRowValue (acceptingRows C β) (.inr e)
      (connectionSourceAddress C a) =
    chosenValue C β Q hQ (.inr e) (connectionSourceAddress C a) := by
  funext j
  change Fin 2 at j
  let b : Bool := decide (j.val = 1)
  have hj : (if b then (1 : Fin 2) else (0 : Fin 2)) = j := by
    fin_cases j <;> rfl
  have hc := chosen_comparison_equation C β Q hQ hacc (.copy e b) a
  change e.sourceForm C F
      (chosenValue C β Q hQ (.inl (e.source C)) (connectionSourceAddress C a)) -
    chosenValue C β Q hQ (.inr e) (connectionSourceAddress C a)
      (if b then (1 : Fin 2) else (0 : Fin 2)) = _ at hc
  have hidx := congrArg (fun k : Fin 2 =>
    chosenValue C β Q hQ (.inr e) (connectionSourceAddress C a) k) hj
  replace hc := (congrArg (fun v : F => e.sourceForm C F
    (chosenValue C β Q hQ (.inl (e.source C)) (connectionSourceAddress C a)) - v)
    hidx.symm).trans hc
  rw [(comparisons C F).comparisonDelta_eq_sum_rows] at hc
  change (∑ i, (acceptingRows C β (.inr e) i
      (a i).val (a (finRotate (n+3) i)).val : Fin 2 → F)) j = _
  rw [Finset.sum_apply]
  change (∑ i, (e.sourceForm C F (primaryRows C β (e.source C) i
      (a i).val (a (finRotate (n+3) i)).val) -
    (comparisons C F).comparisonRows β (.copy e (j.val = 1)) i
      (a i).val (a (finRotate (n+3) i)).val)) = _
  rw [Finset.sum_sub_distrib, ← map_sum]
  rw [show (∑ i, primaryRows C β (e.source C) i (a i).val
      (a (finRotate (n+3) i)).val) =
      chosenValue C β Q hQ (.inl (e.source C)) (connectionSourceAddress C a) from
    primaryRows_source_sum C β Q hQ hacc e (connectionSourceAddress C a)]
  linear_combination hc

include hQ hacc in
/-- Every actual comparison is satisfied by the row functions just constructed. -/
theorem acceptingRows_comparison (e : Comparison C)
    (a : (comparisons C F).DomainAddress e) :
    (comparisons C F).sourceForm e
      ((comparisons C F).realRowValue (acceptingRows C β)
        ((comparisons C F).source e) ((comparisons C F).sourceAddress a)) -
    (comparisons C F).targetForm e
      ((comparisons C F).realRowValue (acceptingRows C β)
        ((comparisons C F).target e) ((comparisons C F).targetAddress a)) =
    (comparisons C F).comparisonDelta β e a := by
  have hc := chosen_comparison_equation C β Q hQ hacc e a
  cases e with
  | seed k =>
    change gateOutput C F (C.seed k).gate
      (∑ i, primaryRows C β (.gate (C.seed k).gate) i (a i).val
        (a (finRotate (n+3) i)).val) - (0 : F) = _
    calc
      _ = gateOutput C F (C.seed k).gate
          (chosenValue C β Q hQ (.inl (.gate (C.seed k).gate)) (fun i => (a i).val)) - 0 :=
        congrArg (fun z => gateOutput C F (C.seed k).gate z - 0)
          (primaryRows_gate_sum C β Q hQ hacc (C.seed k).gate (fun i => (a i).val))
      _ = _ := hc
  | copy e b =>
    change e.sourceForm C F
      (∑ i, primaryRows C β (e.source C) i (a i).val (a (finRotate (n+3) i)).val) -
      ((comparisons C F).realRowValue (acceptingRows C β) (.inr e)
        (connectionSourceAddress C a)) (if b then (1 : Fin 2) else (0 : Fin 2)) = _
    calc
      _ = e.sourceForm C F
          (chosenValue C β Q hQ (.inl (e.source C)) (connectionSourceAddress C a)) -
          chosenValue C β Q hQ (.inr e) (connectionSourceAddress C a)
            (if b then (1 : Fin 2) else (0 : Fin 2)) :=
        congrArg₂ (fun x y => e.sourceForm C F x - y (if b then (1 : Fin 2) else (0 : Fin 2)))
          (primaryRows_source_sum C β Q hQ hacc e (connectionSourceAddress C a))
          (acceptingRows_buffer_sum C β Q hQ hacc e a)
      _ = _ := hc
  | sum e =>
    change (((comparisons C F).realRowValue (acceptingRows C β) (.inr e)
        (connectionSourceAddress C a)) (0 : Fin 2) +
      ((comparisons C F).realRowValue (acceptingRows C β) (.inr e)
        (connectionSourceAddress C a)) (1 : Fin 2)) -
      e.targetForm C F (∑ i, primaryRows C β (e.target C) i
        (e.permutation C i (a i).val)
        (e.permutation C (finRotate (n+3) i) (a (finRotate (n+3) i)).val)) = _
    rw [acceptingRows_buffer_sum C β Q hQ hacc e a]
    have hp := primaryRows_target_sum C β Q hQ hacc e (connectionTargetAddress C a)
    change (∑ i, primaryRows C β (e.target C) i
        (e.permutation C i (a i).val)
        (e.permutation C (finRotate (n+3) i) (a (finRotate (n+3) i)).val)) = _ at hp
    rw [hp]
    exact hc

end GroupWL.CircuitComparisons
