import GroupWL.DenseEncoding

/-! Soundness and size bounds for the actual dense input parser. -/
namespace GroupWL.Statement
open Complexity
open scoped BigOperators

theorem readUnary_sound {xs tail : BitString} {n : ℕ}
    (h : readUnary xs = some (n, tail)) : xs = unary n ++ tail := by
  induction xs generalizing n with
  | nil => simp [readUnary] at h
  | cons b xs ih =>
    cases b with
    | false =>
      simp only [readUnary, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      rfl
    | true =>
      cases hr : readUnary xs with
      | none => simp [readUnary, hr] at h
      | some a =>
        rcases a with ⟨k, rest⟩
        simp only [readUnary, hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        rw [ih hr]
        simp [unary, List.replicate_succ, List.append_assoc]

theorem readArray_sound {α : Type*} (read : BitString → Option (α × BitString))
    (encode : α → BitString)
    (hsound : ∀ {xs a tail}, read xs = some (a, tail) → xs = encode a ++ tail)
    {n : ℕ} {xs tail : BitString} {a : Fin n → α}
    (h : readArray read n xs = some (a, tail)) : xs = arrayWord encode a ++ tail := by
  induction n generalizing xs with
  | zero =>
    simp only [readArray, Option.some.injEq, Prod.mk.injEq] at h
    simpa [arrayWord] using h.2
  | succ n ih =>
    cases hf : read xs with
    | none => simp [readArray, hf] at h
    | some first =>
      rcases first with ⟨v, rest⟩
      cases hr : readArray read n rest with
      | none => simp [readArray, hf, hr] at h
      | some last =>
        rcases last with ⟨vs, last⟩
        simp only [readArray, hf, hr, Option.bind_eq_bind, Option.bind_some,
          Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        rw [hsound hf, ih hr]
        simp [arrayWord, List.ofFn_succ, List.append_assoc]

theorem arrayWord_length_le {α : Type*} (encode : α → BitString)
    {n B : ℕ} (a : Fin n → α) (h : ∀ i, (encode (a i)).length ≤ B) :
    (arrayWord encode a).length ≤ n * B := by
  induction n with
  | zero => simp [arrayWord]
  | succ n ih =>
    have ht := ih (Fin.tail a) (fun i => h i.succ)
    have hh := h 0
    simpa only [arrayWord, List.ofFn_succ, List.flatten_cons, List.length_append,
      Nat.succ_mul, Fin.tail, Nat.add_comm] using Nat.add_le_add hh ht

variable (p : ℕ) [Fact p.Prime]

theorem readField_sound {xs tail : BitString} {a : ZMod p}
    (h : readField p xs = some (a, tail)) : xs = unary a.val ++ tail := by
  cases hu : readUnary xs with
  | none => simp [readField, hu] at h
  | some v =>
    rcases v with ⟨n, rest⟩
    by_cases hn : n < p
    · simp only [readField, hu, Option.bind_eq_bind, Option.bind_some, hn, if_true,
        Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hn] using readUnary_sound hu
    · simp [readField, hu, hn] at h

theorem readCoefficients_sound {n m : ℕ} {xs tail : BitString}
    {c : Fin n → Fin n → Fin m → ZMod p}
    (h : readCoefficients p n m xs = some (c, tail)) :
    xs = coefficientsWord p c ++ tail := by
  apply readArray_sound _ _ _ h
  intro xs row tail hrow
  apply readArray_sound _ _ _ hrow
  intro xs cell tail hcell
  exact readArray_sound _ _ (readField_sound p) hcell

theorem readTensor_sound {xs tail : BitString} {T : TensorDescription p}
    (h : readTensor p xs = some (T, tail)) : xs = T.denseWord p ++ tail := by
  cases hn : readUnary xs with
  | none => simp [readTensor, hn] at h
  | some first =>
    rcases first with ⟨n, rest⟩
    cases hm : readUnary rest with
    | none => simp [readTensor, hn, hm] at h
    | some second =>
      rcases second with ⟨m, rest'⟩
      cases hc : readCoefficients p n m rest' with
      | none => simp [readTensor, hn, hm, hc] at h
      | some third =>
        rcases third with ⟨c, last⟩
        simp only [readTensor, hn, hm, hc, Option.bind_eq_bind, Option.bind_some] at h
        split at h
        · rename_i halt
          cases h
          rw [readUnary_sound hn, readUnary_sound hm, readCoefficients_sound p hc]
          simp only [denseWord_eq_coefficients, List.append_assoc]
          congr 3
          congr 1
          funext i j l
          simp [TensorDescription.coefficient]
        · contradiction

@[simp] theorem readTensor_eq_some_iff {xs tail : BitString} {T : TensorDescription p} :
    readTensor p xs = some (T, tail) ↔ xs = T.denseWord p ++ tail :=
  ⟨readTensor_sound p, fun h => h ▸ readTensor_denseWord p T tail⟩

theorem coefficientsWord_length_le {n m : ℕ}
    (c : Fin n → Fin n → Fin m → ZMod p) :
    (coefficientsWord p c).length ≤ n * (n * (m * p)) := by
  apply arrayWord_length_le
  intro i
  apply arrayWord_length_le
  intro j
  apply arrayWord_length_le
  intro l
  have h := ZMod.val_lt (c i j l)
  simpa [unary] using h

theorem denseWord_length_le (T : TensorDescription p) :
    (T.denseWord p).length ≤ T.inputDimension + T.outputDimension + 2 +
      T.inputDimension * (T.inputDimension * (T.outputDimension * p)) := by
  have h := coefficientsWord_length_le p (T.coefficient p)
  simp only [denseWord_eq_coefficients, List.length_append, unary,
    List.length_replicate, List.length_cons, List.length_nil] at *
  omega

end GroupWL.Statement
