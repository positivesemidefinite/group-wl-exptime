import GroupWL.MachinePrograms.NatArrayLanguage

/-! Exact trace lemmas for the finite-register loop language. -/
namespace GroupWL.MachinePrograms.NatArrayLanguage

open scoped BigOperators
variable {Reg Arr : Type*} [DecidableEq Reg] [DecidableEq Arr] [Fintype Reg] [Fintype Arr]

/-- A finite instruction sequence, ending in the cost-zero skip. -/
def sequence : List (Program Reg Arr) → Program Reg Arr
  | [] => .skip
  | p::ps => .seq p (sequence ps)

/-- Count the actual body executions and each loop guard. The trace is data
for the proof; it is not an instruction supplied to the executable program. -/
theorem while_runs_of_trace (bound : ℕ) (flag : Reg) (body : Program Reg Arr)
    (states : ℕ → Store Reg Arr) (cost : ℕ → ℕ) (n : ℕ)
    (hbody : ∀ i<n,Runs bound body (states i) (cost i) (states (i+1)))
    (hflag : ∀ i<n,(states i).scalar flag ≠ 0)
    (hstop : (states n).scalar flag=0) (hsmall : (states n).size ≤ bound) :
    Runs bound (.while flag body) (states 0)
      ((∑ i ∈ Finset.range n,cost i)+n+1) (states n) := by
  induction n generalizing states cost with
  | zero => simpa using Runs.while_zero hstop hsmall
  | succ n ih =>
      have ht := ih (fun i => states (i+1)) (fun i => cost (i+1))
        (fun i hi => hbody (i+1) (by omega))
        (fun i hi => hflag (i+1) (by omega)) hstop hsmall
      have hr := Runs.while_nonzero (hflag 0 (by omega)) (hbody 0 (by omega)) ht
      convert hr using 1 <;> simp only [Finset.sum_range_succ'] <;> omega

theorem while_runs_bound (bound : ℕ) (flag : Reg) (body : Program Reg Arr)
    (states : ℕ → Store Reg Arr) (cost : ℕ → ℕ) (n perBody : ℕ)
    (hbody : ∀ i<n,Runs bound body (states i) (cost i) (states (i+1)))
    (hflag : ∀ i<n,(states i).scalar flag ≠ 0)
    (hstop : (states n).scalar flag=0) (hsmall : (states n).size ≤ bound)
    (hcost : ∀ i<n,cost i ≤ perBody) :
    ∃ t≤n*(perBody+1)+1,Runs bound (.while flag body) (states 0) t (states n) := by
  refine ⟨(∑ i ∈ Finset.range n,cost i)+n+1,?_,
    while_runs_of_trace bound flag body states cost n hbody hflag hstop hsmall⟩
  have hsum : (∑ i ∈ Finset.range n,cost i) ≤ n*perBody := by
    calc
      _ ≤ ∑ _i ∈ Finset.range n,perBody :=
        Finset.sum_le_sum (fun i hi => hcost i (Finset.mem_range.mp hi))
      _ = _ := by simp
  nlinarith

namespace Store

def Bounded (S : Store Reg Arr) (m : ℕ) : Prop :=
  (∀ r,S.scalar r≤m) ∧ (∀ a,(S.array a).length≤m) ∧ ∀ a x,x ∈ S.array a → x≤m

theorem size_le_of_bounded {S : Store Reg Arr} {m : ℕ} (h : S.Bounded m) :
    S.size ≤ (Fintype.card Reg+3*Fintype.card Arr)*(m+1)^2 := by
  have hs : (∑ r,(S.scalar r+1)) ≤ Fintype.card Reg*(m+1) := by
    calc
      _ ≤ ∑ _r : Reg,(m+1) := Finset.sum_le_sum (fun r _ => by have := h.1 r; omega)
      _ = _ := by simp
  have ha (a : Arr) : (S.array a).sum ≤ m*m := by
    have hh : (S.array a).sum ≤ (S.array a).length*m := by
      exact List.sum_le_card_nsmul (S.array a) m (h.2.2 a)
    exact hh.trans (Nat.mul_le_mul_right _ (h.2.1 a))
  have ht : (∑ a,((S.array a).length+(S.array a).sum+1)) ≤
      Fintype.card Arr*(m+m*m+1) := by
    calc
      _ ≤ ∑ _a : Arr,(m+m*m+1) := Finset.sum_le_sum (fun a _ => by have := ha a; have := h.2.1 a; omega)
      _ = _ := by simp
  unfold size
  nlinarith

end Store
end GroupWL.MachinePrograms.NatArrayLanguage
