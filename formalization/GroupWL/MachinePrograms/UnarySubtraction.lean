import GroupWL.MachinePrograms.UnaryArithmetic

/-! Saturating unary subtraction with an explicitly counted stack loop. -/
namespace GroupWL.MachinePrograms.Structured

variable {K : Type*} [DecidableEq K]

def subtractConsume (source target : K) : Program K :=
  .while source Option.isSome (.seq (discard source) (discard target))

theorem subtractConsume_runs (source target : K) (hne : source ≠ target)
    (m n : ℕ) (S : Store K) (hm : S source = unary m) (hn : S target = unary n) :
    Runs (subtractConsume source target) S (3*m+1)
      (Function.update (Function.update S source []) target (unary (n-m))) := by
  induction m generalizing n S with
  | zero =>
      have hm0 : S source = [] := by simpa [unary] using hm
      have he : Function.update (Function.update S source []) target (unary n) = S := by
        rw [← hm0,Function.update_eq_self,← hn,Function.update_eq_self]
      simpa only [Nat.mul_zero,Nat.zero_add,Nat.sub_zero,he] using
        (Runs.while_false (k := source) (test := Option.isSome)
          (body := .seq (discard source) (discard target))
          (by simp [hm0]) : Runs (subtractConsume source target) S 1 S)
  | succ m ih =>
      let S' := Function.update (Function.update S source (unary m)) target (unary (n-1))
      have h₁ : Runs (discard source) S 1 (Function.update S source (unary m)) := by
        simpa [hm,unary] using discard_runs S source
      have h₂ : Runs (discard target) (Function.update S source (unary m)) 1 S' := by
        simpa [S',Ne.symm hne,hn,unary] using
          discard_runs (Function.update S source (unary m)) target
      have rest := ih (n-1) S' (by simp [S',hne]) (by simp [S'])
      have run := Runs.while_true (S := S) (test := Option.isSome)
        (by simp [hm,unary]) (Runs.seq h₁ h₂) rest
      have he : Function.update (Function.update S' source []) target (unary (n-1-m)) =
          Function.update (Function.update S source []) target (unary (n-(m+1))) := by
        have hnsub : n-1-m = n-(m+1) := by omega
        funext k
        by_cases hk : k=target
        · subst k
          simp [hnsub]
        · by_cases hk' : k=source
          · subst k
            simp [hne]
          · simp [S',Function.update_of_ne hk,Function.update_of_ne hk']
      rw [he] at run
      convert run using 1 <;> omega

/-- Copy the divisor to a temporary counter, then subtract it. The precise
postcondition changes only the remainder register. -/
def subtractCopy (divisor remainder counter temp : K) : Program K :=
  .seq (copy divisor counter temp) (subtractConsume counter remainder)

theorem subtractCopy_runs (S : Store K) (divisor remainder counter temp : K)
    (hdc : divisor ≠ counter) (hdt : divisor ≠ temp) (hct : counter ≠ temp)
    (hcr : counter ≠ remainder) (m n : ℕ)
    (hm : S divisor = unary m) (hn : S remainder = unary n)
    (hc : S counter = []) (ht : S temp = []) :
    Runs (subtractCopy divisor remainder counter temp) S (10*m+3)
      (Function.update S remainder (unary (n-m))) := by
  let S' := Function.update S counter (unary m)
  have first : Runs (copy divisor counter temp) S (7*m+2) S' := by
    simpa [S',hm,hc] using copy_runs S divisor counter temp hdc hdt hct ht
  have last := subtractConsume_runs counter remainder hcr m n S'
    (by simp [S']) (by simp [S',Ne.symm hcr,hn])
  have he : Function.update (Function.update S' counter []) remainder (unary (n-m)) =
      Function.update S remainder (unary (n-m)) := by
    simp only [S',Function.update_idem]
    rw [← hc,Function.update_eq_self]
  rw [he] at last
  have run := Runs.seq first last
  convert run using 1 <;> omega

end GroupWL.MachinePrograms.Structured
