import GroupWL.MachinePrograms.NatArrayLanguage
import GroupWL.MachinePrograms.ArrayPrograms
import GroupWL.MachinePrograms.StructuredComplexity

/-! Fixed register layout and semantic interfaces for concrete atom lowering.
Scratch registers are independent of the input size. -/
namespace GroupWL.MachinePrograms.NatArrayLowering

open NatArrayLanguage
open scoped BigOperators

variable {Reg Arr : Type*}

abbrev StackIndex (Reg Arr : Type*) := (Reg ⊕ Arr) ⊕ Fin 16

def scalarSlot (r : Reg) : StackIndex Reg Arr := .inl (.inl r)
def arraySlot (a : Arr) : StackIndex Reg Arr := .inl (.inr a)
def scratchSlot (i : Fin 16) : StackIndex Reg Arr := .inr i

def scratchEmbedding : Fin 16 ↪ StackIndex Reg Arr := ⟨scratchSlot, Sum.inr_injective⟩

def encodeStore (S : Store Reg Arr) : Structured.Store (StackIndex Reg Arr)
  | .inl (.inl r) => List.replicate (S.scalar r) true
  | .inl (.inr a) => Structured.arrayWord (S.array a)
  | .inr _ => []

@[simp] theorem encodeStore_scalar (S : Store Reg Arr) (r : Reg) :
    encodeStore S (scalarSlot r) = List.replicate (S.scalar r) true := rfl
@[simp] theorem encodeStore_array (S : Store Reg Arr) (a : Arr) :
    encodeStore S (arraySlot a) = Structured.arrayWord (S.array a) := rfl
@[simp] theorem encodeStore_scratch (S : Store Reg Arr) (i : Fin 16) :
    encodeStore S (scratchSlot i) = [] := rfl

/-- Only the materialized user registers are specified here. A concrete atom
body may leave work values in the fixed scratch area; cleanup removes them. -/
def DataEncoded (S : Store Reg Arr) (T : Structured.Store (StackIndex Reg Arr)) : Prop :=
  (∀ r, T (scalarSlot r) = List.replicate (S.scalar r) true) ∧
  (∀ a, T (arraySlot a) = Structured.arrayWord (S.array a))

@[simp] theorem dataEncoded_encodeStore (S : Store Reg Arr) : DataEncoded S (encodeStore S) :=
  ⟨fun _ => rfl, fun _ => rfl⟩

def resetScratch (T : Structured.Store (StackIndex Reg Arr)) : Structured.Store (StackIndex Reg Arr)
  | .inl x => T (.inl x)
  | .inr _ => []

theorem DataEncoded.reset {S : Store Reg Arr} {T : Structured.Store (StackIndex Reg Arr)}
    (h : DataEncoded S T) : resetScratch T = encodeStore S := by
  funext k
  rcases k with (r | a) | i
  · exact h.1 r
  · exact h.2 a
  · rfl

variable [DecidableEq Reg] [DecidableEq Arr]

@[simp] theorem scalarSlot_eq (r s : Reg) :
    (scalarSlot (Arr := Arr) r = scalarSlot s) ↔ r = s := by simp [scalarSlot]
@[simp] theorem arraySlot_eq (a b : Arr) :
    (arraySlot (Reg := Reg) a = arraySlot b) ↔ a = b := by simp [arraySlot]
@[simp] theorem scratchSlot_eq (i j : Fin 16) :
    (scratchSlot (Reg := Reg) (Arr := Arr) i = scratchSlot j) ↔ i = j := by simp [scratchSlot]
@[simp] theorem scalar_ne_array (r : Reg) (a : Arr) : scalarSlot r ≠ arraySlot a := by
  simp [scalarSlot, arraySlot]
@[simp] theorem array_ne_scalar (a : Arr) (r : Reg) : arraySlot a ≠ scalarSlot r := by
  simp [scalarSlot, arraySlot]
@[simp] theorem scalar_ne_scratch (r : Reg) (i : Fin 16) : scalarSlot r ≠ scratchSlot (Arr := Arr) i := by
  simp [scalarSlot, scratchSlot]
@[simp] theorem scratch_ne_scalar (i : Fin 16) (r : Reg) : scratchSlot (Arr := Arr) i ≠ scalarSlot r := by
  simp [scalarSlot, scratchSlot]
@[simp] theorem array_ne_scratch (a : Arr) (i : Fin 16) : arraySlot a ≠ scratchSlot (Reg := Reg) i := by
  simp [arraySlot, scratchSlot]
@[simp] theorem scratch_ne_array (i : Fin 16) (a : Arr) : scratchSlot (Reg := Reg) i ≠ arraySlot a := by
  simp [arraySlot, scratchSlot]

theorem DataEncoded.update_scratch {S : Store Reg Arr} {T : Structured.Store (StackIndex Reg Arr)}
    (h : DataEncoded S T) (i : Fin 16) (xs : List Bool) :
    DataEncoded S (Function.update T (scratchSlot i) xs) := by
  constructor
  · intro r; simpa using h.1 r
  · intro a; simpa using h.2 a

theorem DataEncoded.update_scalar {S : Store Reg Arr} {T : Structured.Store (StackIndex Reg Arr)}
    (h : DataEncoded S T) (r : Reg) (n : ℕ) :
    DataEncoded (S.setScalar r n) (Function.update T (scalarSlot r) (List.replicate n true)) := by
  constructor
  · intro s
    by_cases hs : s = r
    · subst s; simp [Store.setScalar]
    · simpa [Store.setScalar, Function.update_apply, hs] using h.1 s
  · intro a; simpa [Store.setScalar] using h.2 a

theorem DataEncoded.update_array {S : Store Reg Arr} {T : Structured.Store (StackIndex Reg Arr)}
    (h : DataEncoded S T) (a : Arr) (xs : List ℕ) :
    DataEncoded (S.setArray a xs) (Function.update T (arraySlot a) (Structured.arrayWord xs)) := by
  constructor
  · intro r; simpa [Store.setArray] using h.1 r
  · intro b
    by_cases hb : b = a
    · subst b; simp [Store.setArray]
    · simpa [Store.setArray, Function.update_apply, hb] using h.2 b

variable [Fintype Reg] [Fintype Arr]

def wordSize (T : Structured.Store (StackIndex Reg Arr)) : ℕ := ∑ k, (T k).length

theorem encodeStore_size_le (S : Store Reg Arr) : wordSize (encodeStore S) ≤ S.size := by
  simp only [wordSize, Fintype.sum_sum_type, encodeStore, List.length_replicate,
    Structured.arrayWord_length, List.length_nil, Finset.sum_const_zero, Nat.add_zero, Store.size]
  apply Nat.add_le_add
  · apply Finset.sum_le_sum
    intro r hr
    omega
  · apply Finset.sum_le_sum
    intro a ha
    omega

/-- A proved implementation of one explicit arithmetic/array instruction.
The low-level body uses only fixed-control Boolean-stack operations. -/
structure BodyCode (a : Atom Reg Arr) where
  body : Structured.Program (StackIndex Reg Arr)
  correct : ∀ (S : Store Reg Arr) (B : ℕ), a.Valid S → S.size ≤ B → (a.apply S).size ≤ B →
    ∃ t ≤ 1000*(B+1)^3, ∃ T,
      Structured.Runs body (encodeStore S) t T ∧ DataEncoded (a.apply S) T

/-- Scratch-cleaned atom implementations compose directly along source traces. -/
structure AtomCode (a : Atom Reg Arr) where
  program : Structured.Program (StackIndex Reg Arr)
  correct : ∀ (S : Store Reg Arr) (B : ℕ), a.Valid S → S.size ≤ B → (a.apply S).size ≤ B →
    ∃ t ≤ 10000*(B+1)^4,
      Structured.Runs program (encodeStore S) t (encodeStore (a.apply S))

theorem bodyBudget_ge_linear (B : ℕ) : 100*(B+1) ≤ 1000*(B+1)^3 :=
  Nat.mul_le_mul (by decide) (le_self_pow (by omega) (by decide))

end GroupWL.MachinePrograms.NatArrayLowering
