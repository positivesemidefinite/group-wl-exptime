import GroupWL.CircuitAcceptance

namespace GroupWL.CircuitComparisons

open AddressedCircuit SourceLayout SourceLayout.ComparisonData

variable {T F : Type*} {r L : ℕ} [Field F] (C : Circuit T r)
  (β : (comparisons C F).Block L → F) (Q : (comparisons C F).ImageSets)
  (hQ : (comparisons C F).ScalarImages β Q) (hacc : C.Accepts)

include hQ in
theorem buffer_subsingleton (e : Connection C) (a : ConnectionAddress C e)
    (hs : (SourceImage C Q e (connectionSourceAddress C a)).Subsingleton) :
    (Q (.inr e) (connectionSourceAddress C a)).Subsingleton := by
  have hcoord (b : Bool) :
      ((fun z : Fin 2 → F => z (if b then 1 else 0)) ''
        Q (.inr e) (connectionSourceAddress C a)).Subsingleton := by
    have hc := hQ.comparison (.copy e b) a
    change SourceImage C Q e (connectionSourceAddress C a) =
      (fun z => (comparisons C F).comparisonDelta β (.copy e b) a + z) ''
        ((fun z : Fin 2 → F => z (if b then 1 else 0)) ''
          Q (.inr e) (connectionSourceAddress C a)) at hc
    intro x hx y hy
    apply add_left_cancel (a := (comparisons C F).comparisonDelta β (.copy e b) a)
    apply hs
    · rw [hc]; exact ⟨x, hx, rfl⟩
    · rw [hc]; exact ⟨y, hy, rfl⟩
  intro u hu v hv
  funext i
  fin_cases i
  · exact hcoord false ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
  · exact hcoord true ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩

include hQ hacc in
theorem accepting_connection_source_subsingleton (e : Connection C) (a : Address r) :
    (Q (.inl (e.source C)) a).Subsingleton := by
  cases e with
  | circuit e => exact accepting_gate_subsingleton C β Q hQ hacc _ a
  | test k => exact accepting_gate_subsingleton C β Q hQ hacc _ a
  | flip i => exact accepting_broadcast_set_subsingleton C β Q hQ hacc a
  | broadcast t j => exact accepting_broadcast_set_subsingleton C β Q hQ hacc a
  | identity t j => exact accepting_gate_subsingleton C β Q hQ hacc t a
  | broadcastIdentity b => exact accepting_broadcast_set_subsingleton C β Q hQ hacc a

include hQ hacc in
theorem accepting_comparison_source_subsingleton
    (e : Comparison C) (a : (comparisons C F).DomainAddress e) :
    ((comparisons C F).sourceForm e ''
      Q ((comparisons C F).source e) ((comparisons C F).sourceAddress a)).Subsingleton := by
  cases e with
  | seed k => exact (accepting_gate_subsingleton C β Q hQ hacc _ _).image _
  | copy e b => exact (accepting_connection_source_subsingleton C β Q hQ hacc e _).image _
  | sum e =>
    exact (buffer_subsingleton C β Q hQ e a
      ((accepting_connection_source_subsingleton C β Q hQ hacc e _).image _)).image _

noncomputable def chosenValue (t : RealType C) (a : Address r) : Fin (dimension C t) → F :=
  Classical.choose (hQ.nonempty t a)

theorem chosenValue_mem (t : RealType C) (a : Address r) :
    chosenValue C β Q hQ t a ∈ Q t a := Classical.choose_spec (hQ.nonempty t a)

include hacc in
theorem chosen_comparison_equation (e : Comparison C)
    (a : (comparisons C F).DomainAddress e) :
    (comparisons C F).sourceForm e
        (chosenValue C β Q hQ ((comparisons C F).source e) ((comparisons C F).sourceAddress a)) -
      (comparisons C F).targetForm e
        (chosenValue C β Q hQ ((comparisons C F).target e) ((comparisons C F).targetAddress a)) =
      (comparisons C F).comparisonDelta β e a := by
  have he := accepting_comparison_source_subsingleton C β Q hQ hacc e a
    ⟨_, chosenValue_mem C β Q hQ _ _, rfl⟩
    (by
      rw [hQ.comparison e a]
      exact ⟨_, ⟨_, chosenValue_mem C β Q hQ _ _, rfl⟩, rfl⟩)
  exact sub_eq_iff_eq_add.mpr (by simpa [add_comm] using he)

def identityCopyAddress (t : T) (j : Fin (gateDim C t)) (a : Address r) (b : Bool) :
    (comparisons C F).DomainAddress (.copy (.identity t j) b) :=
  fun i => ⟨a i, Finset.mem_univ _⟩

def identitySumAddress (t : T) (j : Fin (gateDim C t)) (a : Address r) :
    (comparisons C F).DomainAddress (.sum (.identity t j)) :=
  fun i => ⟨a i, Finset.mem_univ _⟩

def broadcastIdentityCopyAddress (a : Address r) (b : Bool) :
    (comparisons C F).DomainAddress (.copy (.broadcastIdentity false) b) :=
  fun i => ⟨a i, Finset.mem_univ _⟩

def broadcastIdentitySumAddress (a : Address r) :
    (comparisons C F).DomainAddress (.sum (.broadcastIdentity false)) :=
  fun i => ⟨a i, Finset.mem_univ _⟩

include hacc in
theorem chosen_gate_identity (t : T) (a : Address r) (j : Fin (gateDim C t)) :
    chosenValue C β Q hQ (.inl (.gate t)) a j =
      (comparisons C F).comparisonDelta β (.copy (.identity t j) false)
        (identityCopyAddress C t j a false) +
      (comparisons C F).comparisonDelta β (.copy (.identity t j) true)
        (identityCopyAddress C t j a true) +
      (comparisons C F).comparisonDelta β (.sum (.identity t j))
        (identitySumAddress C t j a) := by
  have h₀ := chosen_comparison_equation C β Q hQ hacc
    (.copy (.identity t j) false) (identityCopyAddress C t j a false)
  have h₁ := chosen_comparison_equation C β Q hQ hacc
    (.copy (.identity t j) true) (identityCopyAddress C t j a true)
  have hs := chosen_comparison_equation C β Q hQ hacc
    (.sum (.identity t j)) (identitySumAddress C t j a)
  change chosenValue C β Q hQ (.inl (.gate t)) a j -
    chosenValue C β Q hQ (.inr (.identity t j)) a (0 : Fin 2) = _ at h₀
  change chosenValue C β Q hQ (.inl (.gate t)) a j -
    chosenValue C β Q hQ (.inr (.identity t j)) a (1 : Fin 2) = _ at h₁
  change chosenValue C β Q hQ (.inr (.identity t j)) a (0 : Fin 2) +
    chosenValue C β Q hQ (.inr (.identity t j)) a (1 : Fin 2) -
    chosenValue C β Q hQ (.inl (.gate t)) a j = _ at hs
  linear_combination h₀ + h₁ + hs

include hacc in
theorem chosen_broadcast_identity (a : Address r) :
    chosenValue C β Q hQ (.inl .broadcast) a (0 : Fin 1) =
      (comparisons C F).comparisonDelta β (.copy (.broadcastIdentity false) false)
        (broadcastIdentityCopyAddress C a false) +
      (comparisons C F).comparisonDelta β (.copy (.broadcastIdentity false) true)
        (broadcastIdentityCopyAddress C a true) +
      (comparisons C F).comparisonDelta β (.sum (.broadcastIdentity false))
        (broadcastIdentitySumAddress C a) := by
  have h₀ := chosen_comparison_equation C β Q hQ hacc
    (.copy (.broadcastIdentity false) false) (broadcastIdentityCopyAddress C a false)
  have h₁ := chosen_comparison_equation C β Q hQ hacc
    (.copy (.broadcastIdentity false) true) (broadcastIdentityCopyAddress C a true)
  have hs := chosen_comparison_equation C β Q hQ hacc
    (.sum (.broadcastIdentity false)) (broadcastIdentitySumAddress C a)
  change chosenValue C β Q hQ (.inl .broadcast) a (0 : Fin 1) -
    chosenValue C β Q hQ (.inr (.broadcastIdentity false)) a (0 : Fin 2) = _ at h₀
  change chosenValue C β Q hQ (.inl .broadcast) a (0 : Fin 1) -
    chosenValue C β Q hQ (.inr (.broadcastIdentity false)) a (1 : Fin 2) = _ at h₁
  change chosenValue C β Q hQ (.inr (.broadcastIdentity false)) a (0 : Fin 2) +
    chosenValue C β Q hQ (.inr (.broadcastIdentity false)) a (1 : Fin 2) -
    chosenValue C β Q hQ (.inl .broadcast) a (0 : Fin 1) = _ at hs
  linear_combination h₀ + h₁ + hs

end GroupWL.CircuitComparisons
