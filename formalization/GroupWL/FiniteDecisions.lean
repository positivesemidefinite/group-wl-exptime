import GroupWL.PGroupIdentification
import GroupWL.FiniteNeighborWL
import GroupWL.InputParsing

/-! # Executable decisions for the two actual input languages

These are finite algorithms with correctness proofs. Their implementations in
the explicit tape-machine model and their running-time bounds are separate
operational obligations, not asserted by this file.
-/
namespace GroupWL.Statement

open Refinement PGroupCandidates FiniteImageSearch
variable (p : ℕ) [Fact p.Prime]

def fieldElements : List (ZMod p) := List.ofFn (fun i : Fin p => (i.val : ZMod p))

theorem mem_fieldElements (x : ZMod p) : x ∈ fieldElements p := by
  apply List.mem_ofFn.mpr
  exact ⟨⟨x.val,ZMod.val_lt x⟩,by simp⟩

def tensorElements (T : TensorDescription p) : List T.Carrier :=
  (tuples (fieldElements p) T.inputDimension).flatMap (fun v =>
    (tuples (fieldElements p) T.outputDimension).map (fun z => ⟨v,z⟩))

theorem mem_tensorElements (T : TensorDescription p) (x : T.Carrier) : x ∈ tensorElements p T := by
  rcases x with ⟨v,z⟩
  apply List.mem_flatMap.mpr
  refine ⟨v,mem_tuples _ (mem_fieldElements p) _ _,?_⟩
  exact List.mem_map.mpr ⟨z,mem_tuples _ (mem_fieldElements p) _ _,rfl⟩

private theorem tensor_generator_exists (T : TensorDescription p) :
    ∃ a, a ∈ tuples (tensorElements p T) (T.inputDimension+T.outputDimension) ∧
      FiniteImageSearch.generates a=true := by
  obtain ⟨a,ha⟩ := PGroupDecomposition.exists_generating_tuple (G := T.Carrier)
    (show Nat.card T.Carrier=p^(T.inputDimension+T.outputDimension) by
      rw [Nat.card_eq_fintype_card,card_carrier])
  exact ⟨a,mem_tuples _ (mem_tensorElements p T) _ _,(generates_correct a).mpr ha⟩

def tensorGenerators (T : TensorDescription p) : Fin (T.inputDimension+T.outputDimension) → T.Carrier :=
  List.choose (fun a => FiniteImageSearch.generates a=true)
    (tuples (tensorElements p T) (T.inputDimension+T.outputDimension)) (tensor_generator_exists p T)

theorem tensorGenerators_generate (T : TensorDescription p) : Generates (tensorGenerators p T) :=
  (generates_correct _).mp (List.choose_property _ _ (tensor_generator_exists p T))

def candidatePasses (T : TensorDescription p) (version : Version) (k : ℕ)
    (c : Code p (T.inputDimension+T.outputDimension)) : Bool :=
  match decode _ c with
  | none => true
  | some t =>
      letI := t
      !(FiniteWL.groupTest (G := T.Carrier) (H := Carrier p (T.inputDimension+T.outputDimension)) version k) ||
        FiniteImageSearch.search (elements p (T.inputDimension+T.outputDimension)) (tensorGenerators p T)

theorem candidatePasses_correct (T : TensorDescription p) (version : Version) (k : ℕ)
    (c : Code p (T.inputDimension+T.outputDimension)) :
    candidatePasses p T version k c=true ↔
      match decode _ c with
      | none => True
      | some t => letI := t
          GroupEquivalent version k T.Carrier (Carrier p (T.inputDimension+T.outputDimension)) →
            Nonempty (T.Carrier ≃* Carrier p (T.inputDimension+T.outputDimension)) := by
  unfold candidatePasses
  cases he : decode _ c with
  | none => simp
  | some t =>
      letI := t
      have hc : Fintype.card T.Carrier=Fintype.card (Carrier p (T.inputDimension+T.outputDimension)) := by
        rw [card_carrier,PGroupCandidates.card_carrier]
      rw [Bool.or_eq_true,Bool.not_eq_true']
      rw [FiniteImageSearch.search_correct _ (mem_elements p _) (tensorGenerators_generate p T) hc]
      rw [show FiniteWL.groupTest (G := T.Carrier) (H := Carrier p (T.inputDimension+T.outputDimension)) version k=false ↔
          ¬ GroupEquivalent version k T.Carrier (Carrier p (T.inputDimension+T.outputDimension)) by
        rw [← FiniteWL.groupTest_correct]; exact Bool.eq_false_iff]
      tauto

def identifyTensor (T : TensorDescription p) (version : Version) (k : ℕ) : Bool :=
  decide (∀ c : Code p (T.inputDimension+T.outputDimension),candidatePasses p T version k c=true)

theorem identifyTensor_correct (T : TensorDescription p) (version : Version) {k : ℕ} (hk : k ≠ 0) :
    identifyTensor p T version k=true ↔ Refinement.Identifies version k T.Carrier := by
  rw [PGroupCandidates.identifies_iff_candidates (p := p) version hk
    (show Nat.card T.Carrier=p^(T.inputDimension+T.outputDimension) by
      rw [Nat.card_eq_fintype_card,card_carrier])]
  simp only [identifyTensor,decide_eq_true_eq,IdentifiesCandidates]
  apply forall_congr'
  intro c
  cases he : decode (p := p) (T.inputDimension+T.outputDimension) c with
  | none => simp [candidatePasses,he]
  | some t => simpa only [he] using candidatePasses_correct p T version k c

def decideIdentification (version : Version) (encoding : DimensionEncoding) (xs : Complexity.BitString) : Bool :=
  match readIdentification p encoding xs with
  | none => false
  | some (T,k) => identifyTensor p T version (min k T.wlCap)

def decideEquivalence (version : Version) (encoding : DimensionEncoding) (xs : Complexity.BitString) : Bool :=
  match readEquivalence p encoding xs with
  | none => false
  | some (T,U,k) => FiniteWL.groupTest (G := T.Carrier) (H := U.Carrier) version (min k T.wlCap)

theorem decideIdentification_correct [NeZero (2 : ZMod p)]
    (version : Version) (encoding : DimensionEncoding) (xs : Complexity.BitString) :
    decideIdentification p version encoding xs=true ↔ xs ∈ identificationLanguage p version encoding := by
  rw [identificationLanguage_iff_parsed]
  cases he : readIdentification p encoding xs with
  | none => simp [decideIdentification,he]
  | some v =>
      rcases v with ⟨T,k⟩
      obtain ⟨bits,hk,_⟩ := (readIdentification_eq_some_iff p encoding xs T k).mp he
      have hp : 0 < k := by
        cases encoding with
        | binary => exact hk.2.2
        | unary => exact hk.2
      have hcap : min k T.wlCap ≠ 0 := by unfold TensorDescription.wlCap; omega
      simp only [decideIdentification,he,Option.some.injEq,Prod.mk.injEq,exists_eq_left',true_and]
      rw [identifyTensor_correct p T version hcap,← identification_clamp T version k]
      constructor
      · intro h; exact ⟨T,k,⟨rfl,rfl⟩,h⟩
      · rintro ⟨T',k',⟨rfl,rfl⟩,h⟩; exact h

theorem decideEquivalence_correct [NeZero (2 : ZMod p)]
    (version : Version) (encoding : DimensionEncoding) (xs : Complexity.BitString) :
    decideEquivalence p version encoding xs=true ↔ xs ∈ equivalenceLanguage p version encoding := by
  rw [equivalenceLanguage_iff_parsed]
  cases he : readEquivalence p encoding xs with
  | none => simp [decideEquivalence,he]
  | some v =>
      rcases v with ⟨T,U,k⟩
      simp only [decideEquivalence,he,Option.some.injEq,Prod.mk.injEq,exists_eq_left',true_and]
      rw [FiniteWL.groupTest_correct,← equivalence_clamp T U version k]
      constructor
      · intro h; exact ⟨T,U,k,⟨rfl,rfl,rfl⟩,h⟩
      · rintro ⟨T',U',k',⟨rfl,rfl,rfl⟩,h⟩; exact h

end GroupWL.Statement
