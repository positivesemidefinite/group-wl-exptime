import GroupWL.Statement
import Mathlib.LinearAlgebra.Basis.Bilinear

/-! Executable parsing of the self-delimiting dense tensor coordinates. -/
namespace GroupWL.Statement
open Complexity

def readUnary : BitString → Option (ℕ × BitString)
  | [] => none
  | false :: xs => some (0, xs)
  | true :: xs => (readUnary xs).map (fun a => (a.1 + 1, a.2))

@[simp] theorem readUnary_unary (n : ℕ) (tail : BitString) :
    readUnary (unary n ++ tail) = some (n, tail) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (readUnary (unary n ++ tail)).map _ = _
      rw [ih]
      rfl

/-- Parse a fixed number of entries, retaining the remaining input word. -/
def readArray {α : Type*} (read : BitString → Option (α × BitString)) :
    (n : ℕ) → BitString → Option ((Fin n → α) × BitString)
  | 0, xs => some (Fin.elim0, xs)
  | n+1, xs => do
      let (a, xs') ← read xs
      let (as, rest) ← readArray read n xs'
      pure (Fin.cons a as, rest)

def arrayWord {α : Type*} (encode : α → BitString) {n : ℕ} (a : Fin n → α) : BitString :=
  (List.ofFn (fun i => encode (a i))).flatten

theorem readArray_arrayWord {α : Type*} (read : BitString → Option (α × BitString))
    (encode : α → BitString) (hread : ∀ a tail, read (encode a ++ tail) = some (a, tail))
    {n : ℕ} (a : Fin n → α) (tail : BitString) :
    readArray read n (arrayWord encode a ++ tail) = some (a, tail) := by
  induction n with
  | zero =>
      have ha : a = Fin.elim0 := by funext i; exact Fin.elim0 i
      subst a
      rfl
  | succ n ih =>
      rw [arrayWord, List.ofFn_succ, List.flatten_cons, List.append_assoc]
      change (do
        let (b, rest) ← read (encode (a 0) ++ (arrayWord encode (Fin.tail a) ++ tail))
        let (bs, last) ← readArray read n rest
        pure ((Fin.cons b bs : Fin (n+1) → α), last)) = _
      rw [hread]
      change (readArray read n (arrayWord encode (Fin.tail a) ++ tail)).bind
        (fun bs => some ((Fin.cons (a 0) bs.1 : Fin (n+1) → α), bs.2)) = some (a, tail)
      rw [ih]
      change some (Fin.cons (a 0) (Fin.tail a), tail) = some (a, tail)
      rw [Fin.cons_self_tail]

variable (p : ℕ) [Fact p.Prime]

def readField (xs : BitString) : Option (ZMod p × BitString) := do
  let (a, rest) ← readUnary xs
  if a < p then pure (a, rest) else none

@[simp] theorem readField_unary (a : ZMod p) (tail : BitString) :
    readField p (unary a.val ++ tail) = some (a, tail) := by
  simp [readField, ZMod.val_lt]

def readCoefficients (n m : ℕ) :=
  readArray (readArray (readArray (readField p) m) n) n

def coefficientsWord {n m : ℕ} (c : Fin n → Fin n → Fin m → ZMod p) : BitString :=
  arrayWord (arrayWord (arrayWord (fun a : ZMod p => unary a.val))) c

@[simp] theorem readCoefficients_word {n m : ℕ}
    (c : Fin n → Fin n → Fin m → ZMod p) (tail : BitString) :
    readCoefficients p n m (coefficientsWord p c ++ tail) = some (c, tail) := by
  apply readArray_arrayWord
  intro row rest
  apply readArray_arrayWord
  intro cell rest'
  exact readArray_arrayWord (readField p) (fun a : ZMod p => unary a.val)
    (readField_unary p) cell rest'

@[simp] theorem denseWord_eq_coefficients (T : TensorDescription p) :
    T.denseWord p = unary T.inputDimension ++ unary T.outputDimension ++
      coefficientsWord p (T.coefficient p) := rfl

open scoped BigOperators

/-- The displayed finite coefficient array reconstructs the bilinear map. -/
def coefficientBilinear {n m : ℕ} (c : Fin n → Fin n → Fin m → ZMod p) :
    (Fin n → ZMod p) →ₗ[ZMod p] (Fin n → ZMod p) →ₗ[ZMod p] (Fin m → ZMod p) :=
  LinearMap.mk₂ (ZMod p) (fun x y => ∑ i, x i • ∑ j, y j • c i j)
    (by intros; simp [add_smul, Finset.sum_add_distrib])
    (by intros; simp [mul_smul, Finset.smul_sum])
    (by intros; simp [add_smul, Finset.sum_add_distrib, smul_add])
    (by
      intro a x y
      simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact smul_comm (x i) a (y j • c i j))

@[simp] theorem coefficientBilinear_basis {n m : ℕ}
    (c : Fin n → Fin n → Fin m → ZMod p) (i j : Fin n) :
    coefficientBilinear p c (Pi.single i 1) (Pi.single j 1) = c i j := by
  simp [coefficientBilinear, Pi.single_apply]

@[simp] theorem coefficientBilinear_coefficient (T : TensorDescription p) :
    coefficientBilinear p (T.coefficient p) = T.tensor.toLinearMap := by
  apply LinearMap.ext_basis (Pi.basisFun (ZMod p) (Fin T.inputDimension))
    (Pi.basisFun (ZMod p) (Fin T.inputDimension))
  intro i j
  simp only [Pi.basisFun_apply, coefficientBilinear_basis]
  rfl

/-- Malformed dimensions, field entries and nonalternating tensors are rejected.
The unconsumed suffix is the parameter or the next tensor description. -/
def readTensor (xs : BitString) : Option (TensorDescription p × BitString) := do
  let (n, xs') ← readUnary xs
  let (m, xs'') ← readUnary xs'
  let (c, rest) ← readCoefficients p n m xs''
  let b := coefficientBilinear p c
  if h : ∀ x, b x x = 0 then
    pure (⟨n, m, ⟨b, h⟩⟩, rest)
  else none

@[simp] theorem readTensor_denseWord (T : TensorDescription p) (tail : BitString) :
    readTensor p (T.denseWord p ++ tail) = some (T, tail) := by
  simp only [denseWord_eq_coefficients, List.append_assoc, readTensor, readUnary_unary,
    Option.bind_eq_bind, Option.bind_some]
  change (do
    let (c, rest) ← readCoefficients p T.inputDimension T.outputDimension
      (coefficientsWord p (T.coefficient p) ++ tail)
    let b := coefficientBilinear p c
    if h : ∀ x, b x x = 0 then pure (⟨T.inputDimension,T.outputDimension,⟨b,h⟩⟩,rest)
      else none) = some (T,tail)
  rw [readCoefficients_word]
  have ht : ∀ x, T.tensor.toLinearMap x x = 0 := T.tensor.map_self_eq_zero
  simp [ht]

theorem denseWord_prefix_injective (T U : TensorDescription p) (tail tail' : BitString)
    (h : T.denseWord p ++ tail = U.denseWord p ++ tail') : T = U ∧ tail = tail' := by
  have he := congrArg (readTensor p) h
  simpa only [readTensor_denseWord, Option.some.injEq, Prod.mk.injEq] using he

theorem denseWord_injective : Function.Injective (TensorDescription.denseWord p) := by
  intro T U h
  exact (denseWord_prefix_injective p T U [] [] (by simpa using h)).1

end GroupWL.Statement
