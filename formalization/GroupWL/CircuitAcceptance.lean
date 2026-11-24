import GroupWL.CircuitComparisons

/-! Singleton propagation through the actual buffered circuit comparisons. -/

namespace GroupWL.CircuitComparisons

open AddressedCircuit SourceLayout SourceLayout.ComparisonData

variable {T F : Type*} {r L : ℕ} [Field F] (C : Circuit T r)

abbrev ConnectionAddress (e : Connection C) :=
  ∀ i : Fin r, {b : Bool // b ∈ (e.domain C).coordinate i}

def connectionSourceAddress {e : Connection C} (a : ConnectionAddress C e) : Address r :=
  fun i => (a i).val

def connectionTargetAddress {e : Connection C} (a : ConnectionAddress C e) : Address r :=
  fun i => e.permutation C i (a i).val

def SourceImage (Q : (comparisons C F).ImageSets) (e : Connection C) (a : Address r) : Set F :=
  e.sourceForm C F '' Q (.inl (e.source C)) a

def TargetImage (Q : (comparisons C F).ImageSets) (e : Connection C) (a : Address r) : Set F :=
  e.targetForm C F '' Q (.inl (e.target C)) a

def OutputImage (Q : (comparisons C F).ImageSets) (t : T) (a : Address r) : Set F :=
  gateOutput C F t '' Q (.inl (.gate t)) a

def InputImage (Q : (comparisons C F).ImageSets) (t : T) (a : Address r) (b : Bool) : Set F :=
  gateInput C F t b '' Q (.inl (.gate t)) a

def BroadcastImage (Q : (comparisons C F).ImageSets) (a : Address r) : Set F :=
  (fun z : Fin 1 → F => z 0) '' Q (.inl .broadcast) a

private theorem subsingleton_of_translate {S : Set F} (d : F)
    (h : ((fun z => d + z) '' S).Subsingleton) : S.Subsingleton := by
  intro x hx y hy
  exact add_left_cancel (h ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩)

/-- One buffered connection propagates a singleton scalar image, for arbitrary
address-dependent comparison shifts. -/
theorem connection_subsingleton
    (β : (comparisons C F).Block L → F) (Q : (comparisons C F).ImageSets)
    (hQ : (comparisons C F).ScalarImages β Q) (e : Connection C) (a : ConnectionAddress C e)
    (hs : (SourceImage C Q e (connectionSourceAddress C a)).Subsingleton) :
    (TargetImage C Q e (connectionTargetAddress C a)).Subsingleton := by
  have hcoord (b : Bool) :
      ((fun z : Fin 2 → F => z (if b then 1 else 0)) ''
        Q (.inr e) (connectionSourceAddress C a)).Subsingleton := by
    have hc := hQ.comparison (.copy e b) a
    change SourceImage C Q e (connectionSourceAddress C a) =
      (fun z => (comparisons C F).comparisonDelta β (.copy e b) a + z) ''
        ((fun z : Fin 2 → F => z (if b then 1 else 0)) ''
          Q (.inr e) (connectionSourceAddress C a)) at hc
    apply subsingleton_of_translate ((comparisons C F).comparisonDelta β (.copy e b) a)
    rw [← hc]
    exact hs
  have hbuffer : (Q (.inr e) (connectionSourceAddress C a)).Subsingleton := by
    intro u hu v hv
    funext i
    fin_cases i
    · exact hcoord false ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
    · exact hcoord true ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
  have hsum := hbuffer.image (fun z : Fin 2 → F => z 0 + z 1)
  have hc := hQ.comparison (.sum e) a
  change (fun z : Fin 2 → F => z 0 + z 1) '' Q (.inr e) (connectionSourceAddress C a) =
    (fun z => (comparisons C F).comparisonDelta β (.sum e) a + z) ''
      TargetImage C Q e (connectionTargetAddress C a) at hc
  apply subsingleton_of_translate ((comparisons C F).comparisonDelta β (.sum e) a)
  rw [← hc]
  exact hsum

theorem seed_output_subsingleton
    (β : (comparisons C F).Block L → F) (Q : (comparisons C F).ImageSets)
    (hQ : (comparisons C F).ScalarImages β Q) (v : C.Node) (hv : C.Seed v) :
    (OutputImage C Q v.1 v.2).Subsingleton := by
  obtain ⟨k, hk, ha⟩ := hv
  let a : (comparisons C F).DomainAddress (.seed k) := fun i => ⟨v.2 i, ha i⟩
  have hc := hQ.comparison (.seed k) a
  rw [hk]
  change OutputImage C Q (C.seed k).gate v.2 =
    (fun z => (comparisons C F).comparisonDelta β (.seed k) a + z) ''
      ((0 : (Fin 1 → F) →ₗ[F] F) '' Q (.inl .dummy) v.2) at hc
  rw [hc]
  have hz : ((0 : (Fin 1 → F) →ₗ[F] F) '' Q (.inl .dummy) v.2).Subsingleton := by
    rintro x ⟨u, hu, rfl⟩ y ⟨w, hw, rfl⟩
    rfl
  exact hz.image _

theorem input_subsingleton_of_wire
    (β : (comparisons C F).Block L → F) (Q : (comparisons C F).ImageSets)
    (hQ : (comparisons C F).ScalarImages β Q) {u v : C.Node} {b : Bool}
    (hw : C.Wire u v b) (hu : (OutputImage C Q u.1 u.2).Subsingleton) :
    (InputImage C Q v.1 v.2 b).Subsingleton := by
  obtain ⟨e, a, ha, rfl, rfl, hport⟩ := hw
  rw [← hport]
  exact connection_subsingleton C β Q hQ (.circuit e) (fun i => ⟨a i, ha i⟩) hu

theorem true_output_subsingleton
    (β : (comparisons C F).Block L → F) (Q : (comparisons C F).ImageSets)
    (hQ : (comparisons C F).ScalarImages β Q) (v : C.Node) (hv : C.True v) :
    (OutputImage C Q v.1 v.2).Subsingleton := by
  induction hv with
  | seed hs => exact seed_output_subsingleton C β Q hQ _ hs
  | @scalar u v b hk hw hu ih =>
    have hi := input_subsingleton_of_wire C β Q hQ hw ih
    simpa [OutputImage, InputImage, gateOutput, gateInput, portCoordinate, hk] using hi
  | @andGate u₀ u₁ v hk hw₀ hw₁ hu₀ hu₁ ih₀ ih₁ =>
    have h₀ := input_subsingleton_of_wire C β Q hQ hw₀ ih₀
    have h₁ := input_subsingleton_of_wire C β Q hQ hw₁ ih₁
    rintro x ⟨u, hu, rfl⟩ y ⟨w, hw, rfl⟩
    have he₀ := h₀ ⟨u, hu, rfl⟩ ⟨w, hw, rfl⟩
    have he₁ := h₁ ⟨u, hu, rfl⟩ ⟨w, hw, rfl⟩
    change gateOutput C F v.1 u = gateOutput C F v.1 w
    simp only [gateOutput, hk, reduceCtorEq, ↓reduceIte, LinearMap.add_apply]
    rw [he₀, he₁]

theorem accepting_broadcast_subsingleton
    (β : (comparisons C F).Block L → F) (Q : (comparisons C F).ImageSets)
    (hQ : (comparisons C F).ScalarImages β Q) (hacc : C.Accepts) :
    ∃ a : Address r, (BroadcastImage C Q a).Subsingleton := by
  obtain ⟨v, ⟨k, hk, ha⟩, hv⟩ := hacc
  have hs := true_output_subsingleton C β Q hQ v hv
  rw [hk] at hs
  exact ⟨v.2, connection_subsingleton C β Q hQ (.test k) (fun i => ⟨v.2 i, ha i⟩) hs⟩

/-- Coordinatewise bit flips connect the entire addressed cube. -/
theorem predicate_of_bitflips (P : Address r → Prop) (a₀ : Address r) (ha₀ : P a₀)
    (hflip : ∀ a i, P a → P ((Connection.permutation C (.flip i)).apply a)) :
    ∀ a, P a := by
  have hupdate (a : Address r) (i : Fin r) (b : Bool) (ha : P a) :
      P (Function.update a i b) := by
    by_cases hab : a i = b
    · have he : Function.update a i b = a := by
        funext j
        by_cases hji : j = i
        · subst j; simp [hab]
        · simp [hji]
      rw [he]
      exact ha
    · have hbi : Equiv.swap false true (a i) = b := by
        cases hai : a i <;> cases b <;> simp_all
      have he : (Connection.permutation C (.flip i)).apply a = Function.update a i b := by
        funext j
        by_cases hji : j = i
        · subst j
          simpa [Connection.permutation, AddressMap.apply] using hbi
        · simp [Connection.permutation, AddressMap.apply, hji]
      rw [← he]
      exact hflip a i ha
  intro a
  have hall (S : Finset (Fin r)) : P (fun i => if i ∈ S then a i else a₀ i) := by
    induction S using Finset.induction with
    | empty => simpa using ha₀
    | @insert i S hi ih =>
      have hu := hupdate (fun j => if j ∈ S then a j else a₀ j) i (a i) ih
      have he : Function.update (fun j => if j ∈ S then a j else a₀ j) i (a i) =
          (fun j => if j ∈ insert i S then a j else a₀ j) := by
        funext j
        by_cases hji : j = i
        · subst j; simp
        · simp [hji]
      rwa [he] at hu
  simpa using hall Finset.univ

theorem accepting_all_broadcast_subsingleton
    (β : (comparisons C F).Block L → F) (Q : (comparisons C F).ImageSets)
    (hQ : (comparisons C F).ScalarImages β Q) (hacc : C.Accepts) :
    ∀ a : Address r, (BroadcastImage C Q a).Subsingleton := by
  obtain ⟨a₀, ha₀⟩ := accepting_broadcast_subsingleton C β Q hQ hacc
  apply predicate_of_bitflips C (fun a => (BroadcastImage C Q a).Subsingleton) a₀ ha₀
  intro a i ha
  exact connection_subsingleton C β Q hQ (.flip i) (fun j => ⟨a j, Finset.mem_univ _⟩) ha

theorem accepting_coordinate_subsingleton
    (β : (comparisons C F).Block L → F) (Q : (comparisons C F).ImageSets)
    (hQ : (comparisons C F).ScalarImages β Q) (hacc : C.Accepts)
    (t : T) (a : Address r) (j : Fin (gateDim C t)) :
    ((fun z : Fin (gateDim C t) → F => z j) '' Q (.inl (.gate t)) a).Subsingleton := by
  exact connection_subsingleton C β Q hQ (.broadcast t j)
    (fun i => ⟨a i, Finset.mem_univ _⟩)
    (accepting_all_broadcast_subsingleton C β Q hQ hacc a)

theorem accepting_gate_subsingleton
    (β : (comparisons C F).Block L → F) (Q : (comparisons C F).ImageSets)
    (hQ : (comparisons C F).ScalarImages β Q) (hacc : C.Accepts)
    (t : T) (a : Address r) : (Q (.inl (.gate t)) a).Subsingleton := by
  intro u hu v hv
  funext j
  exact accepting_coordinate_subsingleton C β Q hQ hacc t a j
    ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩

theorem accepting_broadcast_set_subsingleton
    (β : (comparisons C F).Block L → F) (Q : (comparisons C F).ImageSets)
    (hQ : (comparisons C F).ScalarImages β Q) (hacc : C.Accepts)
    (a : Address r) : (Q (.inl .broadcast) a).Subsingleton := by
  intro u hu v hv
  funext j
  have hj : j = (0 : Fin 1) := @Subsingleton.elim (Fin 1) inferInstance j 0
  subst j
  exact accepting_all_broadcast_subsingleton C β Q hQ hacc a ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩

end GroupWL.CircuitComparisons
