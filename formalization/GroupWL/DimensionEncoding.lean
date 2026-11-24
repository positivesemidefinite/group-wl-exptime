import GroupWL.DenseParsing
import Mathlib.Data.Nat.Bits

/-! Canonical positive dimensions in the two encodings used by the target. -/
namespace GroupWL.Statement
open Complexity

theorem binary_fold_ge (bits : BitString) (a : ℕ) :
    a ≤ bits.foldl (fun n b => 2 * n + if b then 1 else 0) a := by
  induction bits generalizing a with
  | nil => rfl
  | cons b bits ih =>
    apply le_trans (b := 2 * a + if b then 1 else 0) _ (ih _)
    cases b <;> simp <;> omega

theorem binaryValue_positive (bits : BitString) : 0 < binaryValue (true :: bits) := by
  have h := binary_fold_ge bits 1
  change 0 < bits.foldl _ 1
  omega

def readDimension : DimensionEncoding → BitString → Option ℕ
  | .binary, [] => none
  | .binary, false :: _ => none
  | .binary, true :: tail => some (binaryValue (true :: tail))
  | .unary, bits => if bits ≠ [] ∧ ∀ b ∈ bits, b = true then some bits.length else none

theorem readDimension_eq_some_iff (e : DimensionEncoding) (bits : BitString) (k : ℕ) :
    readDimension e bits = some k ↔ e.Represents bits k := by
  cases e with
  | binary =>
    cases bits with
    | nil => simp [readDimension, DimensionEncoding.Represents]
    | cons b bits =>
      cases b with
      | false => simp [readDimension, DimensionEncoding.Represents]
      | true =>
        have hp := binaryValue_positive bits
        simp [readDimension, DimensionEncoding.Represents]
        exact fun h => h ▸ hp
  | unary =>
    simp only [readDimension, DimensionEncoding.Represents]
    constructor
    · intro h
      split at h
      · rename_i hb
        have hk : bits.length = k := Option.some.inj h
        refine ⟨List.eq_replicate_iff.mpr ⟨hk, hb.2⟩, ?_⟩
        have hn : 0 < bits.length := List.length_pos_iff.mpr hb.1
        omega
      · contradiction
    · rintro ⟨rfl, hk⟩
      simp [Nat.ne_of_gt hk]

theorem DimensionEncoding.represents_unique {e : DimensionEncoding}
    {bits : BitString} {j k : ℕ} (hj : e.Represents bits j) (hk : e.Represents bits k) : j = k := by
  have h := (readDimension_eq_some_iff e bits j).mpr hj
  rw [(readDimension_eq_some_iff e bits k).mpr hk] at h
  exact (Option.some.inj h).symm

theorem binaryValue_append_single (bits : BitString) (b : Bool) :
    binaryValue (bits ++ [b]) = 2 * binaryValue bits + if b then 1 else 0 := by
  simp [binaryValue, List.foldl_append]

@[simp] theorem binaryValue_reverse_bits (n : ℕ) : binaryValue n.bits.reverse = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [binaryValue]
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn, List.reverse_cons, binaryValue_append_single, ih]
    cases b <;> rfl

theorem reverse_bits_head (n : ℕ) : n ≠ 0 → ∃ tail, n.bits.reverse = true :: tail := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n hn ih =>
    intro hne
    rw [Nat.bits_append_bit n b hn, List.reverse_cons]
    by_cases hz : n = 0
    · subst n
      have hb := hn rfl
      subst b
      exact ⟨[], rfl⟩
    · obtain ⟨tail, ht⟩ := ih hz
      rw [ht]
      exact ⟨tail ++ [b], rfl⟩

theorem bits_length_le (n : ℕ) : n.bits.length ≤ n := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn, List.length_cons]
    by_cases hz : n = 0
    · subst n
      have hb := hn rfl
      subst b
      decide
    · cases b <;> simp [Nat.bit] <;> omega

def dimensionWord : DimensionEncoding → ℕ → BitString
  | .binary, n => n.bits.reverse
  | .unary, n => List.replicate n true

theorem dimensionWord_represents (e : DimensionEncoding) (n : ℕ) (hn : 0 < n) :
    e.Represents (dimensionWord e n) n := by
  cases e with
  | binary => exact ⟨reverse_bits_head n (Nat.ne_of_gt hn), binaryValue_reverse_bits n, hn⟩
  | unary => exact ⟨rfl, hn⟩

theorem dimensionWord_length_le (e : DimensionEncoding) (n : ℕ) :
    (dimensionWord e n).length ≤ n := by
  cases e with
  | binary => simpa [dimensionWord] using bits_length_le n
  | unary => simp [dimensionWord]

end GroupWL.Statement
