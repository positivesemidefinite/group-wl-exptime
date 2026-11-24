import GroupWL.CentralNaming
import GroupWL.OperatorRecovery

/-! Reconstruction of the arbitrary opponent from the actual transferred
coordinate names. -/

namespace GroupWL.CoordinateNames.CentralNamingContext

open Refinement CountingLogic PebbleGame

variable {p n : ℕ} [Fact p.Prime] [NeZero (2 : ZMod p)]
  {X Z H : Type*} [AddCommGroup X] [Module (ZMod p) X]
  [AddCommGroup Z] [Module (ZMod p) Z] [Group H] [Finite H]
  {Y : Submodule (ZMod p) (X →ₗ[ZMod p] Z)}
  {ε : AlternatingBilinearMap (ZMod p) X Z}
  [Finite (TensorGroup (evaluationTwist Y ε))]
  (C : CentralNamingContext Y ε H n) (D : Baer.Data p H)

/-- Actual retained responses determine the full cross-commutator law in the
opponent. The canonical matrix response is used only to read an element of
`Y`; the equality itself is forced by the central naming formula. -/
theorem operator_evaluation_group (a : Baer.Data.Vector D)
    (m : LinearMap.ker (C.toQuotientNamingContext.quotientLinear D)) :
    a.val * m.val.val * a.val⁻¹ * m.val.val⁻¹ =
      C.center ((C.toQuotientNamingContext.operatorRaw D m : X →ₗ[ZMod p] Z)
        (C.toQuotientNamingContext.quotientLinear D a)) := by
  let Q := C.toQuotientNamingContext
  let h := m.val.val
  let h' := a.val
  have ht (i : Fin 9)
      (hi : i ∈ ({0, 1, 2, 3} : Finset (Fin 9)) ∪ {4, 5}) :=
    Q.pair_tracks C.anchor_b_tracked h h' i hi
  have hq := Q.quotient_word (Q.pair_winning h h')
    (Q.pairReference h h') (Q.pairOpponent h h')
    (fun i hi => Q.pair_reference_anchor h h' i (by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi ⊢; tauto))
    (fun i hi => Q.pair_opponent_anchor h h' i (by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi ⊢; tauto))
    (.gen 5) (by decide) (by
      intro i hi
      apply ht i
      simp only [wordVariables, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hi ⊢
      tauto)
  have hq' : Q.quotient h' = ((Q.secondResponse h).symm h').fst.1 := by
    simpa only [GroupWord.eval, Function.comp_apply, Q.pairReference_five,
      Q.pairOpponent_five] using hq
  have htr := C.center_word (Q.pair_winning h h')
    (Q.pairReference h h') (Q.pairOpponent h h')
    (Q.pair_reference_anchor h h') (Q.pair_opponent_anchor h h')
    (commutatorWord (.gen 5) (.gen 4)) (by decide) (by
      intro i hi
      apply ht i
      simp only [commutatorWord, wordVariables, Finset.mem_union,
        Finset.mem_insert, Finset.mem_singleton] at hi ⊢
      tauto)
    ((Q.operatorRaw D m : X →ₗ[ZMod p] Z) (Q.quotient h'))
  change _ = C.center _ ↔ _ = (⟨0, _⟩ : TensorGroup (evaluationTwist Y ε)) at htr
  have hslot : C.slot = Q.slot := rfl
  rw [hslot] at htr
  simp only [commutatorWord, GroupWord.eval, Function.comp_apply,
    Q.pairOpponent_five, Q.pairOpponent_four,
    Q.pairReference_five, Q.pairReference_four] at htr
  apply htr.mpr
  rw [commutator_anchor Y ε _ _ (Q.operatorRaw D m) (Q.operatorRaw_preimage D m), hq']

theorem operator_evaluation (a : Baer.Data.Vector D)
    (m : LinearMap.ker (C.toQuotientNamingContext.quotientLinear D)) :
    D.bracket a m = C.centerLinear D
      ((C.toQuotientNamingContext.operatorRaw D m : X →ₗ[ZMod p] Z)
        (C.toQuotientNamingContext.quotientLinear D a)) :=
  Baer.Data.Vector.ext (C.operator_evaluation_group D a m)

/-- All the coordinate data are now constructed from the winning game. In
particular, no labels, linear maps, or isomorphisms on `H` are hypotheses. -/
noncomputable def recoveredCoordinateMaps : Recognition.CoordinateMaps D.bracket Y :=
  Recognition.coordinateMapsOfEvaluations D Y
    (C.toQuotientNamingContext.quotientLinear D)
    (C.toQuotientNamingContext.quotientLinear_surjective D)
    (C.centerLinear D) (C.centerLinear_injective D) (C.centerLinear_range D)
    (fun z => C.toQuotientNamingContext.quotientLinear_center D _ (by
      rw [← C.centerLinear_range D]
      exact LinearMap.mem_range_self _ z))
    (C.toQuotientNamingContext.operatorRaw D)
    (C.toQuotientNamingContext.operatorRaw_surjective D)
    (C.operator_evaluation D)

/-- Full arbitrary-opponent reconstruction, preserving every coordinate label
needed by the subsequent game argument. -/
theorem reconstruct :
    ∃ (η : AlternatingBilinearMap (ZMod p) X Z)
      (f : H ≃* TensorGroup (evaluationTwist Y η)),
      (∀ h : H, (f h).fst.1 = C.toQuotientNamingContext.quotient h) ∧
      (∀ z : Z, f (C.center z) = ⟨0, z⟩) ∧
      (∀ m : LinearMap.ker (C.toQuotientNamingContext.quotientLinear D),
        (f m.val.val).fst = (0, C.toQuotientNamingContext.operatorRaw D m)) := by
  obtain ⟨η, f, hfq, hfc, hfm⟩ := Recognition.exists_isomorphism_preserving_all_coordinates
    D Y (C.recoveredCoordinateMaps D)
  exact ⟨η, f, hfq, hfc, hfm⟩

include C in
/-- Existence of a tensor presentation for any finite winning opponent,
without presupposing its exponent, nilpotency class, or vector structure. -/
theorem isomorphic_to_twist (hodd : Odd p) :
    ∃ η : AlternatingBilinearMap (ZMod p) X Z,
      Nonempty (H ≃* TensorGroup (evaluationTwist Y η)) := by
  obtain ⟨η, f, _⟩ := C.reconstruct (C.toQuotientNamingContext.baerData hodd)
  exact ⟨η, ⟨f⟩⟩

end GroupWL.CoordinateNames.CentralNamingContext
