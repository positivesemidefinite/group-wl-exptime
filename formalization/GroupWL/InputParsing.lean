import GroupWL.DimensionEncoding

/-! The actual input languages are exactly the outcomes of deterministic parsing. -/
namespace GroupWL.Statement
open Complexity Refinement

variable (p : ℕ) [Fact p.Prime]

def readIdentification (encoding : DimensionEncoding) (xs : BitString) :
    Option (TensorDescription p × ℕ) := do
  let (T, bits) ← readTensor p xs
  let k ← readDimension encoding bits
  pure (T, k)

def readEquivalence (encoding : DimensionEncoding) (xs : BitString) :
    Option (TensorDescription p × TensorDescription p × ℕ) := do
  let (T, rest) ← readTensor p xs
  let (U, bits) ← readTensor p rest
  let k ← readDimension encoding bits
  pure (T, U, k)

theorem readIdentification_eq_some_iff (encoding : DimensionEncoding) (xs : BitString)
    (T : TensorDescription p) (k : ℕ) :
    readIdentification p encoding xs = some (T, k) ↔
      ∃ bits, encoding.Represents bits k ∧ xs = T.denseWord p ++ bits := by
  constructor
  · intro h
    cases ht : readTensor p xs with
    | none => simp [readIdentification, ht] at h
    | some v =>
      rcases v with ⟨U, bits⟩
      cases hk : readDimension encoding bits with
      | none => simp [readIdentification, ht, hk] at h
      | some j =>
        simp only [readIdentification, ht, hk, Option.bind_eq_bind, Option.bind_some] at h
        cases h
        exact ⟨bits, (readDimension_eq_some_iff _ _ _).mp hk, readTensor_sound p ht⟩
  · rintro ⟨bits, hk, rfl⟩
    simp only [readIdentification, readTensor_denseWord, Option.bind_eq_bind,
      Option.bind_some, (readDimension_eq_some_iff _ _ _).mpr hk]
    rfl

theorem readEquivalence_eq_some_iff (encoding : DimensionEncoding) (xs : BitString)
    (T U : TensorDescription p) (k : ℕ) :
    readEquivalence p encoding xs = some (T, U, k) ↔
      ∃ bits, encoding.Represents bits k ∧ xs = T.denseWord p ++ U.denseWord p ++ bits := by
  constructor
  · intro h
    cases ht : readTensor p xs with
    | none => simp [readEquivalence, ht] at h
    | some v =>
      rcases v with ⟨V, rest⟩
      cases hu : readTensor p rest with
      | none => simp [readEquivalence, ht, hu] at h
      | some v' =>
        rcases v' with ⟨W, bits⟩
        cases hk : readDimension encoding bits with
        | none => simp [readEquivalence, ht, hu, hk] at h
        | some j =>
          simp only [readEquivalence, ht, hu, hk, Option.bind_eq_bind, Option.bind_some] at h
          cases h
          refine ⟨bits, (readDimension_eq_some_iff _ _ _).mp hk, ?_⟩
          rw [readTensor_sound p ht, readTensor_sound p hu, List.append_assoc]
  · rintro ⟨bits, hk, rfl⟩
    simp only [readEquivalence, List.append_assoc, readTensor_denseWord,
      Option.bind_eq_bind, Option.bind_some, (readDimension_eq_some_iff _ _ _).mpr hk]
    rfl

theorem identificationLanguage_iff_parsed (version : Version) (encoding : DimensionEncoding)
    (xs : BitString) : xs ∈ identificationLanguage p version encoding ↔
      ∃ T k, readIdentification p encoding xs = some (T, k) ∧ Identifies version k T.Carrier := by
  constructor
  · rintro ⟨T, bits, k, hk, hx, hT⟩
    exact ⟨T, k, (readIdentification_eq_some_iff p _ _ _ _).mpr ⟨bits, hk, hx⟩, hT⟩
  · rintro ⟨T, k, hp, hT⟩
    obtain ⟨bits, hk, hx⟩ := (readIdentification_eq_some_iff p _ _ _ _).mp hp
    exact ⟨T, bits, k, hk, hx, hT⟩

theorem equivalenceLanguage_iff_parsed (version : Version) (encoding : DimensionEncoding)
    (xs : BitString) : xs ∈ equivalenceLanguage p version encoding ↔
      ∃ T U k, readEquivalence p encoding xs = some (T, U, k) ∧
        GroupEquivalent version k T.Carrier U.Carrier := by
  constructor
  · rintro ⟨T, U, bits, k, hk, hx, hTU⟩
    exact ⟨T, U, k, (readEquivalence_eq_some_iff p _ _ _ _ _).mpr ⟨bits, hk, hx⟩, hTU⟩
  · rintro ⟨T, U, k, hp, hTU⟩
    obtain ⟨bits, hk, hx⟩ := (readEquivalence_eq_some_iff p _ _ _ _ _).mp hp
    exact ⟨T, U, bits, k, hk, hx, hTU⟩

def identificationWord (encoding : DimensionEncoding) (T : TensorDescription p) (k : ℕ) :
    BitString := T.denseWord p ++ dimensionWord encoding k

def equivalenceWord (encoding : DimensionEncoding) (T U : TensorDescription p) (k : ℕ) :
    BitString := T.denseWord p ++ U.denseWord p ++ dimensionWord encoding k

@[simp] theorem readIdentification_word (encoding : DimensionEncoding)
    (T : TensorDescription p) (k : ℕ) (hk : 0 < k) :
    readIdentification p encoding (identificationWord p encoding T k) = some (T, k) := by
  apply (readIdentification_eq_some_iff p _ _ _ _).mpr
  exact ⟨dimensionWord encoding k, dimensionWord_represents _ _ hk, rfl⟩

@[simp] theorem readEquivalence_word (encoding : DimensionEncoding)
    (T U : TensorDescription p) (k : ℕ) (hk : 0 < k) :
    readEquivalence p encoding (equivalenceWord p encoding T U k) = some (T, U, k) := by
  apply (readEquivalence_eq_some_iff p _ _ _ _ _).mpr
  exact ⟨dimensionWord encoding k, dimensionWord_represents _ _ hk, rfl⟩

@[simp] theorem identificationWord_mem_iff (version : Version) (encoding : DimensionEncoding)
    (T : TensorDescription p) (k : ℕ) (hk : 0 < k) :
    identificationWord p encoding T k ∈ identificationLanguage p version encoding ↔
      Identifies version k T.Carrier := by
  rw [identificationLanguage_iff_parsed]
  constructor
  · rintro ⟨U, j, hu, hU⟩
    rw [readIdentification_word p _ _ _ hk] at hu
    cases hu
    exact hU
  · exact fun h => ⟨T, k, readIdentification_word p _ _ _ hk, h⟩

@[simp] theorem equivalenceWord_mem_iff (version : Version) (encoding : DimensionEncoding)
    (T U : TensorDescription p) (k : ℕ) (hk : 0 < k) :
    equivalenceWord p encoding T U k ∈ equivalenceLanguage p version encoding ↔
      GroupEquivalent version k T.Carrier U.Carrier := by
  rw [equivalenceLanguage_iff_parsed]
  constructor
  · rintro ⟨V, W, j, hv, hVW⟩
    rw [readEquivalence_word p _ _ _ _ hk] at hv
    cases hv
    exact hVW
  · exact fun h => ⟨T, U, k, readEquivalence_word p _ _ _ _ hk, h⟩

theorem identificationWord_hard (encoding : DimensionEncoding)
    (T : TensorDescription p) (k : ℕ) (hk : 0 < k) (hT : HardGroup p T) :
    identificationWord p encoding T k ∈ hardIdentificationInputs p encoding :=
  ⟨T, dimensionWord encoding k, k, dimensionWord_represents _ _ hk, rfl, hT⟩

theorem equivalenceWord_nonisomorphic (encoding : DimensionEncoding)
    (T U : TensorDescription p) (k : ℕ) (hk : 0 < k)
    (hTU : ¬ Nonempty (T.Carrier ≃* U.Carrier)) :
    equivalenceWord p encoding T U k ∈ nonisomorphicPairInputs p encoding :=
  ⟨T, U, dimensionWord encoding k, k, dimensionWord_represents _ _ hk, rfl, hTU⟩

theorem identificationWord_length_le (encoding : DimensionEncoding)
    (T : TensorDescription p) (k : ℕ) :
    (identificationWord p encoding T k).length ≤
      T.inputDimension + T.outputDimension + 2 +
        T.inputDimension * (T.inputDimension * (T.outputDimension * p)) + k := by
  exact (List.length_append ..).le.trans
    (Nat.add_le_add (denseWord_length_le p T) (dimensionWord_length_le encoding k))

theorem equivalenceWord_length_le (encoding : DimensionEncoding)
    (T U : TensorDescription p) (k : ℕ) :
    (equivalenceWord p encoding T U k).length ≤
      (T.inputDimension + T.outputDimension + 2 +
        T.inputDimension * (T.inputDimension * (T.outputDimension * p))) +
      (U.inputDimension + U.outputDimension + 2 +
        U.inputDimension * (U.inputDimension * (U.outputDimension * p))) + k := by
  simp only [equivalenceWord, List.length_append]
  exact Nat.add_le_add (Nat.add_le_add (denseWord_length_le p T) (denseWord_length_le p U))
    (dimensionWord_length_le encoding k)

end GroupWL.Statement
