import GroupWL.CoordinateNames
import Mathlib.Data.ZMod.Basic

/-! # Every vector has a finite Horner coordinate name -/
namespace GroupWL.CoordinateNames

open Module
open scoped BigOperators

theorem hornerValue_ofFn {F X : Type*} [Field F] [AddCommGroup X] [Module F X]
    (A : X →ₗ[F] X) (seed : X) (n : ℕ) (c : Fin n → ℕ) :
    hornerValue A seed (List.ofFn c) = ∑ i : Fin n, c i • (A ^ i.val) seed := by
  induction n with
  | zero => simp [hornerValue]
  | succ n ih =>
      rw [List.ofFn_succ, hornerValue, ih, map_sum, Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, Module.End.one_apply, Fin.val_succ,
        pow_succ', Module.End.mul_apply, map_nsmul]
      exact add_comm _ _

noncomputable def shiftBasis {F X : Type*} [Field F] [AddCommGroup X] [Module F X]
    {n : ℕ} (basis : Basis (Fin n) F X) : X →ₗ[F] X :=
  basis.constr F (fun i => if hi : i.val + 1 < n then basis ⟨i.val + 1, hi⟩ else 0)

theorem shiftBasis_apply {F X : Type*} [Field F] [AddCommGroup X] [Module F X]
    {n : ℕ} (basis : Basis (Fin n) F X) (i : Fin n) :
    shiftBasis basis (basis i) = if hi : i.val + 1 < n then basis ⟨i.val + 1, hi⟩ else 0 := by
  exact basis.constr_basis F _ i

theorem shiftBasis_pow {F X : Type*} [Field F] [AddCommGroup X] [Module F X]
    {n : ℕ} (hn : 0 < n) (basis : Basis (Fin n) F X) (j : ℕ) (hj : j < n) :
    (shiftBasis basis ^ j) (basis ⟨0, hn⟩) = basis ⟨j, hj⟩ := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, ih (by omega), shiftBasis_apply]
      simp [hj]

/-- Field representatives are used only in the formula's power words. -/
noncomputable def coordinateCode {p : ℕ} [Fact p.Prime] {X : Type*}
    [AddCommGroup X] [Module (ZMod p) X] {n : ℕ}
    (basis : Basis (Fin n) (ZMod p) X) (x : X) : List ℕ :=
  List.ofFn (fun i => (basis.repr x i).val)

theorem hornerValue_coordinateCode {p : ℕ} [Fact p.Prime] {X : Type*}
    [AddCommGroup X] [Module (ZMod p) X] {n : ℕ} (hn : 0 < n)
    (basis : Basis (Fin n) (ZMod p) X) (x : X) :
    hornerValue (shiftBasis basis) (basis ⟨0, hn⟩) (coordinateCode basis x) = x := by
  rw [coordinateCode, hornerValue_ofFn]
  have hp (i : Fin n) : (shiftBasis basis ^ i.val) (basis ⟨0, hn⟩) = basis i :=
    shiftBasis_pow hn basis i.val i.isLt
  simp_rw [hp, ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
  exact basis.sum_repr x

noncomputable def basisSeed {F X : Type*} [Field F] [AddCommGroup X] [Module F X]
    {n : ℕ} (basis : Basis (Fin n) F X) : X :=
  if hn : 0 < n then basis ⟨0, hn⟩ else 0

/-- The zero-dimensional case is included without choosing a nonexistent basis vector. -/
theorem hornerValue_coordinateCode_all {p : ℕ} [Fact p.Prime] {X : Type*}
    [AddCommGroup X] [Module (ZMod p) X] {n : ℕ}
    (basis : Basis (Fin n) (ZMod p) X) (x : X) :
    hornerValue (shiftBasis basis) (basisSeed basis) (coordinateCode basis x) = x := by
  by_cases hn : 0 < n
  · simpa [basisSeed, hn] using hornerValue_coordinateCode hn basis x
  · have hn0 : n = 0 := by omega
    subst n
    have hx : x = 0 := by simpa using (basis.sum_repr x).symm
    simp [coordinateCode, hornerValue, hx]

end GroupWL.CoordinateNames
