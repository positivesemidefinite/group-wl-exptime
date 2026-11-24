import GroupWL.MachinePrograms.ArrayPrograms
import GroupWL.MachinePrograms.UnaryArithmetic

/-! Materialized-array length, allocation and copying by fixed stack programs. -/
namespace GroupWL.MachinePrograms.Structured

variable {K : Type*} [DecidableEq K]

def arrayLengthScan (source saved result : K) : Program K :=
  .while source Option.isSome (.seq (moveOnes source saved)
    (.seq (discard source) (.seq (.push saved false) (.push result true))))

theorem arrayLengthScan_runs (source saved result : K)
    (hss : source ≠ saved) (hsr : source ≠ result) (htr : saved ≠ result)
    (xs : List ℕ) (S : Store K) (hs : S source = arrayWord xs) :
    Runs (arrayLengthScan source saved result) S (3*xs.sum+5*xs.length+1)
      (Function.update (Function.update (Function.update S source [])
        saved ((arrayWord xs).reverse ++ S saved)) result (unary xs.length ++ S result)) := by
  induction xs generalizing S with
  | nil =>
      have h0 : Function.update S source [] = S := by
        have hs0 : S source = [] := hs
        rw [← hs0,Function.update_eq_self]
      simp only [List.sum_nil,List.length_nil,Nat.mul_zero,Nat.zero_add,arrayWord_nil,
        List.reverse_nil,List.nil_append,unary,List.replicate_zero,h0,Function.update_eq_self]
      exact Runs.while_false (by simp [hs])
  | cons n xs ih =>
      let S₀ := Function.update (Function.update S source (false::arrayWord xs))
        saved (unary n ++ S saved)
      have h₀ : Runs (moveOnes source saved) S (3*n+1) S₀ := by
        simpa [S₀,unary] using moveOnes_runs source saved hss n (false::arrayWord xs)
          rfl S hs
      let S₁ := Function.update S₀ source (arrayWord xs)
      have h₁ : Runs (discard source) S₀ 1 S₁ := by
        simpa [S₁,S₀,hss] using discard_runs S₀ source
      let S₂ := Function.update S₁ saved (false::(unary n ++ S saved))
      have h₂ : Runs (.push saved false) S₁ 1 S₂ := by
        simpa [S₂,S₁,S₀,Ne.symm hss] using Runs.push S₁ saved false
      let S' := Function.update S₂ result (true::S result)
      have h₃ : Runs (.push result true) S₂ 1 S' := by
        simpa [S',S₂,S₁,S₀,Ne.symm hsr,Ne.symm htr] using Runs.push S₂ result true
      have hsource : S' source = arrayWord xs := by simp [S',S₂,S₁,S₀,hss,hsr]
      have hsaved : S' saved = false::(unary n ++ S saved) := by simp [S',S₂,htr]
      have hresult : S' result = true::S result := by simp [S']
      have body := Runs.seq h₀ (Runs.seq h₁ (Runs.seq h₂ h₃))
      have run := Runs.while_true (S := S) (test := Option.isSome)
        (by cases n <;> simp [hs,arrayWord,List.replicate_succ]) body (ih S' hsource)
      have he : Function.update (Function.update (Function.update S' source [])
          saved ((arrayWord xs).reverse ++ S' saved)) result (unary xs.length ++ S' result) =
          Function.update (Function.update (Function.update S source [])
          saved ((arrayWord (n::xs)).reverse ++ S saved)) result
            (unary (n::xs).length ++ S result) := by
        funext k
        by_cases hk : k=result
        · subst k
          simp [hresult,unary,List.replicate_add,List.append_assoc]
        · by_cases hk' : k=saved
          · subst k
            simp [hsaved,htr,arrayWord,List.reverse_append,unary,List.append_assoc]
          · by_cases hk'' : k=source
            · subst k
              simp [hsr,hss]
            · simp [S',S₂,S₁,S₀,Function.update_of_ne hk,
                Function.update_of_ne hk',Function.update_of_ne hk'']
      rw [he] at run
      convert run using 1 <;> simp only [List.sum_cons,List.length_cons] <;> omega

/-- Registers 0/1/2 hold the array, empty result and empty temporary stack. -/
def arrayLength (reg : Fin 3 ↪ K) : Program K :=
  .seq (arrayLengthScan (reg 0) (reg 2) (reg 1)) (transfer (reg 2) (reg 0))

theorem arrayLength_runs (reg : Fin 3 ↪ K) (xs : List ℕ) (S : Store K)
    (hs : S (reg 0) = arrayWord xs) (hr : S (reg 1) = []) (ht : S (reg 2) = []) :
    Runs (arrayLength reg) S (6*xs.sum+8*xs.length+2)
      (Function.update S (reg 1) (unary xs.length)) := by
  have ne (i j : Fin 3) (h : i≠j) : reg i ≠ reg j := fun he => h (reg.injective he)
  let S' := Function.update (Function.update (Function.update S (reg 0) [])
    (reg 2) (arrayWord xs).reverse) (reg 1) (unary xs.length)
  have first : Runs (arrayLengthScan (reg 0) (reg 2) (reg 1)) S
      (3*xs.sum+5*xs.length+1) S' := by
    simpa [S',hr,ht] using arrayLengthScan_runs (reg 0) (reg 2) (reg 1)
      (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide)) xs S hs
  have last := transfer_runs S' (reg 2) (reg 0) (ne _ _ (by decide))
  have h2 : S' (reg 2) = (arrayWord xs).reverse := by simp [S',reg.injective.eq_iff]
  have h0 : S' (reg 0) = [] := by simp [S',reg.injective.eq_iff]
  rw [h2,List.length_reverse,arrayWord_length,h0,List.reverse_reverse,List.append_nil] at last
  have he : Function.update (Function.update S' (reg 2) []) (reg 0) (arrayWord xs) =
      Function.update S (reg 1) (unary xs.length) := by
    funext k
    by_cases hk : k=reg 0
    · subst k
      simp [reg.injective.eq_iff,hs]
    · by_cases hk' : k=reg 2
      · subst k
        simp [reg.injective.eq_iff,ht]
      · by_cases hk'' : k=reg 1
        · subst k
          simp [S',reg.injective.eq_iff]
        · simp [S',Function.update_of_ne hk,Function.update_of_ne hk',Function.update_of_ne hk'']
  rw [he] at last
  have run := Runs.seq first last
  convert run using 1 <;> omega

def copyArray (source target temp : K) : Program K := copy source target temp
def clearArray (target : K) : Program K := clear target

theorem copyArray_runs (S : Store K) (source target temp : K)
    (hst : source ≠ target) (hsu : source ≠ temp) (htu : target ≠ temp)
    (xs : List ℕ) (hs : S source = arrayWord xs) (ht : S target = []) (hu : S temp = []) :
    Runs (copyArray source target temp) S (7*(xs.sum+xs.length)+2)
      (Function.update S target (arrayWord xs)) := by
  simpa [copyArray,hs,ht] using copy_runs S source target temp hst hsu htu hu

theorem clearArray_runs (S : Store K) (target : K) (xs : List ℕ)
    (hs : S target = arrayWord xs) :
    Runs (clearArray target) S (2*(xs.sum+xs.length)+1) (Function.update S target []) := by
  simpa [clearArray,hs] using clear_runs S target

def allocateLoop (counter value target temp : K) : Program K :=
  .while counter Option.isSome (.seq (discard counter)
    (.seq (.push target false) (copy value target temp)))

theorem allocateLoop_runs (counter value target temp : K)
    (hcv : counter ≠ value) (hco : counter ≠ target) (hct : counter ≠ temp)
    (hvo : value ≠ target) (hvt : value ≠ temp) (hot : target ≠ temp)
    (m v : ℕ) (S : Store K) (hc : S counter = unary m) (hv : S value = unary v)
    (ht : S temp = []) :
    Runs (allocateLoop counter value target temp) S (m*(7*v+5)+1)
      (Function.update (Function.update S counter []) target
        (arrayWord (List.replicate m v) ++ S target)) := by
  induction m generalizing S with
  | zero =>
      have hc0 : S counter = [] := hc
      have h0 : Function.update S counter [] = S := by rw [← hc0,Function.update_eq_self]
      simp only [Nat.zero_mul,Nat.zero_add,List.replicate_zero,arrayWord_nil,List.nil_append,
        h0,Function.update_eq_self]
      exact Runs.while_false (by simp [hc0])
  | succ m ih =>
      let S₀ := Function.update S counter (unary m)
      let S₁ := Function.update S₀ target (false::S target)
      let S' := Function.update S₀ target (unary v ++ false::S target)
      have h₀ : Runs (discard counter) S 1 S₀ := by
        simpa [S₀,hc,unary] using discard_runs S counter
      have h₁ : Runs (.push target false) S₀ 1 S₁ := by
        simpa [S₁,S₀,Ne.symm hco] using Runs.push S₀ target false
      have hvalue : S₁ value = unary v := by simp [S₁,S₀,hvo,Ne.symm hcv,hv]
      have htemp : S₁ temp = [] := by simp [S₁,S₀,Ne.symm hot,Ne.symm hct,ht]
      have h₂ : Runs (copy value target temp) S₁ (7*v+2) S' := by
        simpa [hvalue,S',S₁,Function.update_idem] using
          copy_runs S₁ value target temp hvo hvt hot htemp
      have hcounter : S' counter = unary m := by simp [S',S₀,hco]
      have hvalue' : S' value = unary v := by simp [S',S₀,hvo,Ne.symm hcv,hv]
      have htemp' : S' temp = [] := by simp [S',S₀,Ne.symm hot,Ne.symm hct,ht]
      have run := Runs.while_true (S := S) (test := Option.isSome)
        (by simp [hc,unary]) (Runs.seq h₀ (Runs.seq h₁ h₂))
        (ih S' hcounter hvalue' htemp')
      have he : Function.update (Function.update S' counter []) target
          (arrayWord (List.replicate m v) ++ S' target) =
          Function.update (Function.update S counter []) target
          (arrayWord (List.replicate (m+1) v) ++ S target) := by
        funext k
        by_cases hk : k=target
        · subst k
          simp [S',List.replicate_add,unary,List.append_assoc]
        · by_cases hk' : k=counter
          · subst k
            simp [hco]
          · simp [S',S₀,Function.update_of_ne hk,Function.update_of_ne hk']
      rw [he] at run
      convert run using 1 <;> ring

/-- Count and fixed entry are preserved in registers 0 and 1; register 2
is initially empty output; registers 3 and 4 are restored empty scratch. -/
def allocateArray (reg : Fin 5 ↪ K) : Program K :=
  .seq (copy (reg 0) (reg 3) (reg 4))
    (allocateLoop (reg 3) (reg 1) (reg 2) (reg 4))

theorem allocateArray_runs (reg : Fin 5 ↪ K) (m v : ℕ) (S : Store K)
    (hm : S (reg 0) = unary m) (hv : S (reg 1) = unary v)
    (ho : S (reg 2) = []) (hc : S (reg 3) = []) (ht : S (reg 4) = []) :
    Runs (allocateArray reg) S (7*m*v+12*m+3)
      (Function.update S (reg 2) (arrayWord (List.replicate m v))) := by
  have ne (i j : Fin 5) (h : i≠j) : reg i ≠ reg j := fun he => h (reg.injective he)
  let S' := Function.update S (reg 3) (unary m)
  have first : Runs (copy (reg 0) (reg 3) (reg 4)) S (7*m+2) S' := by
    simpa [S',hm,hc] using copy_runs S (reg 0) (reg 3) (reg 4)
      (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide)) ht
  have last := allocateLoop_runs (reg 3) (reg 1) (reg 2) (reg 4)
    (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide))
    (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide)) m v S'
    (by simp [S']) (by simp [S',reg.injective.eq_iff,hv])
    (by simp [S',reg.injective.eq_iff,ht])
  have he : Function.update (Function.update S' (reg 3) []) (reg 2)
      (arrayWord (List.replicate m v) ++ S' (reg 2)) =
      Function.update S (reg 2) (arrayWord (List.replicate m v)) := by
    simp only [S',Function.update_idem]
    rw [Function.update_of_ne (ne _ _ (by decide)),ho,List.append_nil,
      ← hc,Function.update_eq_self]
  rw [he] at last
  have run := Runs.seq first last
  convert run using 1 <;> ring

theorem allocateZeros_runs (reg : Fin 5 ↪ K) (m : ℕ) (S : Store K)
    (hm : S (reg 0) = unary m) (hv : S (reg 1) = [])
    (ho : S (reg 2) = []) (hc : S (reg 3) = []) (ht : S (reg 4) = []) :
    Runs (allocateArray reg) S (12*m+3)
      (Function.update S (reg 2) (arrayWord (List.replicate m 0))) := by
  simpa using allocateArray_runs reg m 0 S hm hv ho hc ht

end GroupWL.MachinePrograms.Structured
