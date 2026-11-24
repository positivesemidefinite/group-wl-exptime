import GroupWL.MachinePrograms.FilterRanks
import Mathlib.Algebra.BigOperators.Fin

/-! Algebraic prefix-sum semantics of the operational rank scan. -/
namespace GroupWL.MachinePrograms.FilterRanks
open scoped BigOperators

theorem count_eq_sum (xs : List ℕ) (i : ℕ) : count xs i=∑j∈Finset.range i,xs[j]?.getD 0 := by
  induction i with
  | zero => simp [count]
  | succ i ih => simp only [count,Finset.sum_range_succ,ih]

theorem count_congr {xs ys : List ℕ} {i : ℕ}
    (h : ∀ j < i,xs[j]?.getD 0=ys[j]?.getD 0) : count xs i=count ys i := by
  simp only [count_eq_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact h j (Finset.mem_range.mp hj)

theorem count_ofFn {N : ℕ} (f : Fin N → ℕ) (i : ℕ) (hi : i≤N) :
    count (List.ofFn f) i=∑j : Fin i,f ⟨j.val,j.isLt.trans_le hi⟩ := by
  induction i with
  | zero => simp [count]
  | succ i ih =>
      rw [count,ih (by omega),Fin.sum_univ_castSucc]
      simp only [List.getElem?_ofFn,dif_pos (show i<N by omega),Option.getD_some]
      rfl

theorem sum_range_blocks (f : ℕ → ℕ) (n m : ℕ) :
    (∑i∈Finset.range (n*m),f i)=∑a∈Finset.range n,∑b∈Finset.range m,f (a*m+b) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.succ_mul,Finset.sum_range_add,Finset.sum_range_succ,ih]

theorem count_blocks (xs : List ℕ) (n m k : ℕ) :
    count xs (n*m+k)=(∑a∈Finset.range n,∑b∈Finset.range m,xs[a*m+b]?.getD 0)+
      ∑b∈Finset.range k,xs[n*m+b]?.getD 0 := by
  rw [count_eq_sum,Finset.sum_range_add,sum_range_blocks]

end GroupWL.MachinePrograms.FilterRanks
