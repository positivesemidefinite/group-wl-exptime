import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# Cyclic lifting of row functions

The index set is finite. Coordinate domains may be arbitrary nonempty subsets
of a common type; no finiteness or algebraic structure on the labels is needed.
The coefficient group is any abelian group, so these lemmas apply in odd
characteristic without changing signs.
-/

namespace GroupWL
namespace CyclicLifting

open scoped BigOperators

variable {I A K : Type*} [Fintype I] [DecidableEq I] [AddCommGroup K]

def rowSum (s : Equiv.Perm I) (g : I → A → A → K) (x : I → A) : K :=
  ∑ i, g i (x i) (x (s i))

/-- Updating one coordinate changes exactly its outgoing and incoming terms. -/
theorem rowSum_update (s : Equiv.Perm I) (g : I → A → A → K)
    (x : I → A) (i : I) (u : A) (hi : s i ≠ i) :
    rowSum s g (Function.update x i u) - rowSum s g x =
      (g i u (x (s i)) - g i (x i) (x (s i))) +
      (g (s.symm i) (x (s.symm i)) u - g (s.symm i) (x (s.symm i)) (x i)) := by
  have hip : i ≠ s.symm i := by
    intro h
    exact hi ((congrArg s h).trans (s.apply_symm_apply i))
  have hterm (j : I) :
      g j (Function.update x i u j) (Function.update x i u (s j)) -
          g j (x j) (x (s j)) =
        (if j = i then g i u (x (s i)) - g i (x i) (x (s i)) else 0) +
        (if j = s.symm i then
          g (s.symm i) (x (s.symm i)) u - g (s.symm i) (x (s.symm i)) (x i)
         else 0) := by
    by_cases hji : j = i
    · subst j
      simp [Function.update_of_ne hi, hip]
    · by_cases hjp : j = s.symm i
      · subst j
        rw [s.apply_symm_apply]
        simp [hip.symm]
      · have hsji : s j ≠ i := by
          intro h
          exact hjp (s.apply_eq_iff_eq_symm_apply.mp h)
        simp [Function.update_of_ne hsji, hji, hjp]
  unfold rowSum
  rw [← Finset.sum_sub_distrib]
  simp_rw [hterm, Finset.sum_add_distrib]
  simp

omit [Fintype I] in
theorem update_mem_domains (D : I → Set A) (x : I → A)
    (hx : ∀ i, x i ∈ D i) (i : I) (u : A) (hu : u ∈ D i) :
    ∀ j, Function.update x i u j ∈ D j := by
  intro j
  by_cases h : j = i
  · subst j
    simpa using hu
  · simpa [Function.update_of_ne h] using hx j

/-- The one-coordinate potential extracted from the incoming row. -/
def variation (s : Equiv.Perm I) (g : I → A → A → K) (a : I → A)
    (i : I) (u : A) : K :=
  g (s.symm i) (a (s.symm i)) u - g (s.symm i) (a (s.symm i)) (a i)

/-- Vanishing row sums imply additive separation of each two-coordinate row.
The no-one-cycle and no-two-cycle hypotheses ensure that the two queried
coordinates have distinct other neighbours. -/
theorem row_decomposition (s : Equiv.Perm I) (g : I → A → A → K)
    (D : I → Set A) (a : I → A) (ha : ∀ i, a i ∈ D i)
    (hzero : ∀ x : I → A, (∀ i, x i ∈ D i) → rowSum s g x = 0)
    (hfixed : ∀ i, s i ≠ i) (htwo : ∀ i, s (s i) ≠ i)
    (i : I) (u v : A) (hu : u ∈ D i) (hv : v ∈ D (s i)) :
    g i u v = g i (a i) (a (s i)) + variation s g a (s i) v - variation s g a i u := by
  let x := Function.update a (s i) v
  have hx : ∀ j, x j ∈ D j := update_mem_domains D a ha (s i) v hv
  have hx' : ∀ j, Function.update x i u j ∈ D j := update_mem_domains D x hx i u hu
  have hprev : s.symm i ≠ s i := by
    intro h
    have h' := congrArg s h
    simp only [Equiv.apply_symm_apply] at h'
    exact htwo i h'.symm
  have hidiff : i ≠ s i := (hfixed i).symm
  have h := rowSum_update s g x i u (hfixed i)
  rw [hzero _ hx', hzero _ hx] at h
  dsimp [x] at h
  simp only [Function.update_self, Function.update_of_ne hidiff,
    Function.update_of_ne hprev, sub_self] at h
  simp only [variation, Equiv.symm_apply_apply]
  apply sub_eq_zero.mp
  convert h.symm using 1; abel

/-- A zero-sum cyclic list is the difference of consecutive prefix sums. -/
theorem exists_constant_potential (n : ℕ) (c : Fin (n + 1) → K)
    (hc : ∑ i, c i = 0) :
    ∃ C : Fin (n + 1) → K, ∀ i, C (finRotate (n + 1) i) - C i = c i := by
  let f : ℕ → K := fun j => if hj : j < n + 1 then c ⟨j, hj⟩ else 0
  let C : Fin (n + 1) → K := fun i => ∑ j ∈ Finset.range i.val, f j
  have hf (i : Fin (n + 1)) : f i.val = c i := by simp only [f, dif_pos i.isLt]
  have htotal : ∑ j ∈ Finset.range (n + 1), f j = 0 := by
    rw [← Fin.sum_univ_eq_sum_range]
    simpa only [hf] using hc
  refine ⟨C, ?_⟩
  intro i
  by_cases hi : i = Fin.last n
  · subst i
    simp only [finRotate_last, C, Fin.val_zero, Fin.val_last,
      Finset.sum_range_zero, zero_sub]
    have hlast : (∑ j ∈ Finset.range n, f j) + c (Fin.last n) = 0 := by
      rw [Finset.sum_range_succ] at htotal
      have hlastval : f n = c (Fin.last n) := hf (Fin.last n)
      simpa only [hlastval] using htotal
    exact neg_eq_iff_add_eq_zero.mpr hlast
  · change (∑ j ∈ Finset.range (finRotate (n + 1) i).val, f j) -
        (∑ j ∈ Finset.range i.val, f j) = c i
    rw [coe_finRotate_of_ne_last hi, Finset.sum_range_succ, hf]
    abel

theorem finRotate_no_fixed (n : ℕ) (i : Fin (n + 3)) :
    finRotate (n + 3) i ≠ i := by
  rw [finRotate_apply]
  intro h
  have hsum : i + 1 = i + 0 := by simpa only [add_zero] using h
  have h10 : (1 : Fin (n + 3)) = 0 := add_left_cancel hsum
  have hval := congrArg Fin.val h10
  norm_num at hval

theorem finRotate_no_two_cycle (n : ℕ) (i : Fin (n + 3)) :
    finRotate (n + 3) (finRotate (n + 3) i) ≠ i := by
  simp only [finRotate_apply]
  intro h
  have hsum : i + 2 = i + 0 := by simpa only [add_assoc, one_add_one_eq_two, add_zero] using h
  have h20 : (2 : Fin (n + 3)) = 0 := add_left_cancel hsum
  have hval := congrArg Fin.val h20
  norm_num at hval
  rw [Nat.mod_eq_of_lt (by omega)] at hval
  contradiction

/-- Global lifting on a cyclic row of length at least three: if the sum of
two-coordinate row functions vanishes on every product address, the rows are
differences of one-coordinate potentials. -/
theorem exists_potentials (n : ℕ) (g : Fin (n + 3) → A → A → K)
    (D : Fin (n + 3) → Set A) (a : Fin (n + 3) → A)
    (ha : ∀ i, a i ∈ D i)
    (hzero : ∀ x : Fin (n + 3) → A, (∀ i, x i ∈ D i) →
      rowSum (finRotate (n + 3)) g x = 0) :
    ∃ Y : Fin (n + 3) → A → K, ∀ i u v,
      u ∈ D i → v ∈ D (finRotate (n + 3) i) →
        g i u v = Y (finRotate (n + 3) i) v - Y i u := by
  let s := finRotate (n + 3)
  let c : Fin (n + 3) → K := fun i => g i (a i) (a (s i))
  have hc : ∑ i, c i = 0 := hzero a ha
  obtain ⟨C, hC⟩ := exists_constant_potential (n + 2) c hc
  refine ⟨fun i u => variation s g a i u + C i, ?_⟩
  intro i u v hu hv
  have hd := row_decomposition s g D a ha hzero
    (finRotate_no_fixed n) (finRotate_no_two_cycle n) i u v hu hv
  have hi := hC i
  change C (s i) - C i = g i (a i) (a (s i)) at hi
  rw [hd, ← hi]
  dsimp only [s]
  abel

omit [DecidableEq I] in
/-- Consecutive differences always telescope, for any index permutation. -/
theorem potential_rowSum_zero (s : Equiv.Perm I) (Y : I → A → K) (x : I → A) :
    rowSum s (fun i u v => Y (s i) v - Y i u) x = 0 := by
  unfold rowSum
  rw [Finset.sum_sub_distrib, Equiv.sum_comp s (fun i => Y i (x i)), sub_self]

/-- The global lifting criterion without an externally selected base address. -/
theorem exists_potentials_iff (n : ℕ) (g : Fin (n + 3) → A → A → K)
    (D : Fin (n + 3) → Set A) (hD : ∀ i, (D i).Nonempty) :
    (∀ x : Fin (n + 3) → A, (∀ i, x i ∈ D i) →
      rowSum (finRotate (n + 3)) g x = 0) ↔
    ∃ Y : Fin (n + 3) → A → K, ∀ i u v,
      u ∈ D i → v ∈ D (finRotate (n + 3) i) →
        g i u v = Y (finRotate (n + 3) i) v - Y i u := by
  classical
  constructor
  · intro hzero
    choose a ha using hD
    exact exists_potentials n g D a ha hzero
  · rintro ⟨Y, hY⟩ x hx
    calc
      rowSum (finRotate (n + 3)) g x =
          rowSum (finRotate (n + 3)) (fun i u v => Y (finRotate (n + 3) i) v - Y i u) x := by
        apply Finset.sum_congr rfl
        intro i _
        exact hY i (x i) (x (finRotate (n + 3) i)) (hx i) (hx _)
      _ = 0 := potential_rowSum_zero _ Y x

/-- The square-equation form of global lifting used in Section 2. Horizontal
row sums matching the shifts have one-coordinate vertical readouts that
satisfy every individual square. -/
theorem lift_square_equations (n : ℕ)
    (left right beta : Fin (n + 3) → A → A → K)
    (D : Fin (n + 3) → Set A) (hD : ∀ i, (D i).Nonempty)
    (hrows : ∀ x : Fin (n + 3) → A, (∀ i, x i ∈ D i) →
      (∑ i : Fin (n + 3), (left i (x i) (x (finRotate (n + 3) i)) -
        right i (x i) (x (finRotate (n + 3) i)))) =
      ∑ i : Fin (n + 3), beta i (x i) (x (finRotate (n + 3) i))) :
    ∃ Y : Fin (n + 3) → A → K, ∀ i u v,
      u ∈ D i → v ∈ D (finRotate (n + 3) i) →
        left i u v - right i u v + Y (finRotate (n + 3) i) v - Y i u = beta i u v := by
  let g : Fin (n + 3) → A → A → K := fun i u v => beta i u v - left i u v + right i u v
  have hzero : ∀ x : Fin (n + 3) → A, (∀ i, x i ∈ D i) →
      rowSum (finRotate (n + 3)) g x = 0 := by
    intro x hx
    have h := hrows x hx
    rw [Finset.sum_sub_distrib] at h
    dsimp only [rowSum, g]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← h]
    abel
  obtain ⟨Y, hY⟩ := (exists_potentials_iff n g D hD).mp hzero
  refine ⟨Y, ?_⟩
  intro i u v hu hv
  have h := hY i u v hu hv
  dsimp only [g] at h
  calc
    left i u v - right i u v + Y (finRotate (n + 3) i) v - Y i u =
        left i u v - right i u v + (Y (finRotate (n + 3) i) v - Y i u) := by abel
    _ = beta i u v := by rw [← h]; abel

end CyclicLifting
end GroupWL
