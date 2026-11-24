import GroupWL.MachinePrograms.StackLibrary

/-! Non-destructive list indexing using explicit unary counters and Boolean stacks. -/
namespace GroupWL.MachinePrograms.Structured

variable {K : Type*} [DecidableEq K]

def scanPrefix (counter data saved : K) : Program K :=
  .while counter Option.isSome
    (.seq (discard counter) (.pop data .skip (.push saved false) (.push saved true)))

theorem scanPrefix_runs_aux (counter data saved : K)
    (hcd : counter ≠ data) (hcp : counter ≠ saved) (hdp : data ≠ saved)
    (n : ℕ) (xs : List Bool) :
    ∀ S : Store K, S counter = List.replicate n true → S data = xs →
      Runs (scanPrefix counter data saved) S (3*n+min n xs.length+1)
        (Function.update (Function.update (Function.update S counter [])
          data (xs.drop n)) saved ((xs.take n).reverse++S saved)) := by
  induction n generalizing xs with
  | zero =>
    intro S hc hd
    have hc₀ : S counter = [] := hc
    have he : Function.update (Function.update (Function.update S counter [])
        data (xs.drop 0)) saved ((xs.take 0).reverse++S saved) = S := by
      simp only [List.drop_zero,List.take_zero,List.reverse_nil,List.nil_append]
      rw [← hc₀,Function.update_eq_self,← hd,Function.update_eq_self,Function.update_eq_self]
    rw [he]
    exact Runs.while_false (by simp [hc])
  | succ n ih =>
    intro S hc hd
    cases xs with
    | nil =>
      let S' := Function.update S counter (List.replicate n true)
      have hc' : S' counter = List.replicate n true := by simp [S']
      have hd' : S' data = [] := by simp [S',Ne.symm hcd,hd]
      have hupdate : Function.update (Function.update S counter (List.replicate n true)) data [] = S' := by
        change Function.update S' data [] = S'
        rw [← hd',Function.update_eq_self]
      have first : Runs (.seq (discard counter)
          (.pop data .skip (.push saved false) (.push saved true))) S 2 S' := by
        apply Runs.seq (t := 1) (u := 1)
        · simpa [S',hc,List.replicate_succ] using discard_runs S counter
        · apply Runs.pop (t := 0)
          simpa only [S',Function.update_of_ne (Ne.symm hcd),hd,List.head?_nil,
            List.tail_nil,select,hupdate] using Runs.skip S'
      have rest := ih [] S' hc' hd'
      have hr := Runs.while_true (test := Option.isSome) (by simp [hc,List.replicate_succ]) first rest
      have he : Function.update (Function.update (Function.update S' counter [])
          data ([].drop n)) saved (([].take n).reverse++S' saved) =
          Function.update (Function.update (Function.update S counter [])
            data ([].drop (n+1))) saved (([].take (n+1)).reverse++S saved) := by
        simp [S',Function.update_idem,Ne.symm hcp]
      rw [he] at hr
      convert hr using 1
      simp
      omega
    | cons b xs =>
      let S₀ := Function.update S counter (List.replicate n true)
      let S' := Function.update (Function.update S₀ data xs) saved (b::S saved)
      have hc' : S' counter = List.replicate n true := by simp [S',S₀,hcd,hcp]
      have hd' : S' data = xs := by simp [S',hdp]
      have hp' : S' saved = b::S saved := by simp [S']
      have hd₀ : S₀ data = b::xs := by simp [S₀,Ne.symm hcd,hd]
      have hp₀ : S₀ saved = S saved := by simp [S₀,Ne.symm hcp]
      have first : Runs (.seq (discard counter)
          (.pop data .skip (.push saved false) (.push saved true))) S 3 S' := by
        apply Runs.seq (t := 1) (u := 2)
        · simpa [S₀,hc,List.replicate_succ] using discard_runs S counter
        · apply Runs.pop (t := 1)
          have push := Runs.push (Function.update S₀ data xs) saved b
          cases b <;>
            simpa [select,S₀,Ne.symm hcd,hd,S',Ne.symm hcp,Ne.symm hdp] using push
      have rest := ih xs S' hc' hd'
      have hr := Runs.while_true (test := Option.isSome) (by simp [hc,List.replicate_succ]) first rest
      have he : Function.update (Function.update (Function.update S' counter [])
          data (xs.drop n)) saved ((xs.take n).reverse++S' saved) =
          Function.update (Function.update (Function.update S counter [])
            data ((b::xs).drop (n+1))) saved (((b::xs).take (n+1)).reverse++S saved) := by
        funext k
        by_cases hk : k = saved
        · subst k
          simp [hp',List.reverse_cons,List.append_assoc]
        · by_cases hk' : k = data
          · subst k
            simp [hdp]
          · by_cases hk'' : k = counter
            · subst k
              simp [hcd,hcp]
            · simp [S',S₀,Function.update_of_ne hk,Function.update_of_ne hk',Function.update_of_ne hk'']
      rw [he] at hr
      convert hr using 1
      simp [List.length_cons,min_add_add_right]
      omega

theorem scanPrefix_runs (S : Store K) (counter data saved : K)
    (hcd : counter ≠ data) (hcp : counter ≠ saved) (hdp : data ≠ saved)
    (n : ℕ) (hc : S counter = List.replicate n true) :
    Runs (scanPrefix counter data saved) S (3*n+min n (S data).length+1)
      (Function.update (Function.update (Function.update S counter [])
        data ((S data).drop n)) saved (((S data).take n).reverse++S saved)) :=
  scanPrefix_runs_aux counter data saved hcd hcp hdp n (S data) S hc rfl

def peekInto (data result : K) : Program K :=
  .peek data .skip (.push result false) (.push result true)

theorem peekInto_runs (S : Store K) (data result : K) :
    Runs (peekInto data result) S (1+(S data).head?.toList.length)
      (Function.update S result ((S data).head?.toList++S result)) := by
  cases hd : (S data).head? with
  | none =>
    simp only [Option.toList_none,List.nil_append,Function.update_eq_self]
    apply Runs.peek (t := 0)
    simpa [select,hd] using Runs.skip S
  | some b =>
    apply Runs.peek (t := 1)
    cases b <;> simpa [select,hd] using Runs.push S result _

/-- Registers: data, unary index, counter, saved prefix, scratch, result.
The optional result is encoded as the empty list or a singleton bit. -/
def indexLookup (reg : Fin 6 ↪ K) : Program K :=
  .seq (clear (reg 5))
    (.seq (copy (reg 1) (reg 2) (reg 4))
      (.seq (scanPrefix (reg 2) (reg 0) (reg 3))
        (.seq (peekInto (reg 0) (reg 5)) (transfer (reg 3) (reg 0)))))

theorem indexLookup_runs (S : Store K) (reg : Fin 6 ↪ K) (n : ℕ)
    (hindex : S (reg 1) = List.replicate n true)
    (hcounter : S (reg 2) = []) (hsaved : S (reg 3) = []) (htemp : S (reg 4) = []) :
    Runs (indexLookup reg) S
      (10*n+4*min n (S (reg 0)).length+2*(S (reg 5)).length+6+
        ((S (reg 0))[n]?).toList.length)
      (Function.update S (reg 5) ((S (reg 0))[n]?).toList) := by
  have hne {i j : Fin 6} (h : i ≠ j) : reg i ≠ reg j := fun he => h (reg.injective he)
  have heq (i j : Fin 6) : reg i = reg j ↔ i = j := reg.injective.eq_iff
  let S₀ := Function.update S (reg 5) []
  let S₁ := Function.update S₀ (reg 2) (List.replicate n true)
  let S₂ := Function.update (Function.update (Function.update S₁ (reg 2) [])
    (reg 0) ((S (reg 0)).drop n)) (reg 3) ((S (reg 0)).take n).reverse
  let S₃ := Function.update S₂ (reg 5) ((S (reg 0))[n]?).toList
  have first : Runs (clear (reg 5)) S (2*(S (reg 5)).length+1) S₀ := clear_runs S _
  have second : Runs (copy (reg 1) (reg 2) (reg 4)) S₀ (7*n+2) S₁ := by
    have h := copy_runs S₀ (reg 1) (reg 2) (reg 4)
      (hne (by decide)) (hne (by decide)) (hne (by decide)) (by simp [S₀,heq,htemp])
    simpa [S₁,S₀,heq,hindex,hcounter] using h
  have third : Runs (scanPrefix (reg 2) (reg 0) (reg 3)) S₁
      (3*n+min n (S (reg 0)).length+1) S₂ := by
    have h := scanPrefix_runs S₁ (reg 2) (reg 0) (reg 3)
      (hne (by decide)) (hne (by decide)) (hne (by decide)) n (by simp [S₁])
    simpa [S₂,S₁,S₀,heq,hsaved] using h
  have fourth : Runs (peekInto (reg 0) (reg 5)) S₂
      (1+((S (reg 0))[n]?).toList.length) S₃ := by
    simpa [S₃,S₂,S₁,S₀,heq,List.head?_drop] using peekInto_runs S₂ (reg 0) (reg 5)
  have hs₃ : S₃ (reg 3) = ((S (reg 0)).take n).reverse := by simp [S₃,S₂,heq]
  have hd₃ : S₃ (reg 0) = (S (reg 0)).drop n := by simp [S₃,S₂,heq]
  have fifth : Runs (transfer (reg 3) (reg 0)) S₃
      (3*min n (S (reg 0)).length+1)
      (Function.update S (reg 5) ((S (reg 0))[n]?).toList) := by
    have h := transfer_runs S₃ (reg 3) (reg 0) (hne (by decide))
    have he : Function.update (Function.update S₃ (reg 3) []) (reg 0)
        ((S₃ (reg 3)).reverse++S₃ (reg 0)) =
        Function.update S (reg 5) ((S (reg 0))[n]?).toList := by
      rw [hs₃,hd₃,List.reverse_reverse,List.take_append_drop]
      funext k
      by_cases hk : k = reg 0
      · subst k; simp [heq]
      · by_cases hk' : k = reg 3
        · subst k; simp [heq,hsaved]
        · by_cases hk'' : k = reg 2
          · subst k; simp [S₃,S₂,S₁,S₀,heq,hcounter]
          · by_cases hk''' : k = reg 5
            · subst k; simp [S₃,heq]
            · simp [S₃,S₂,S₁,S₀,Function.update_of_ne hk,Function.update_of_ne hk',
                Function.update_of_ne hk'',Function.update_of_ne hk''']
    rw [he,hs₃,List.length_reverse,List.length_take] at h
    exact h
  have run := Runs.seq first (Runs.seq second (Runs.seq third (Runs.seq fourth fifth)))
  convert run using 1
  omega

theorem indexLookup_runs_bound (S : Store K) (reg : Fin 6 ↪ K) (n : ℕ)
    (hindex : S (reg 1) = List.replicate n true)
    (hcounter : S (reg 2) = []) (hsaved : S (reg 3) = []) (htemp : S (reg 4) = []) :
    ∃ time ≤ 14*n+2*(S (reg 5)).length+7,
      Runs (indexLookup reg) S time (Function.update S (reg 5) ((S (reg 0))[n]?).toList) := by
  refine ⟨_,?_,indexLookup_runs S reg n hindex hcounter hsaved htemp⟩
  have hm := Nat.min_le_left n (S (reg 0)).length
  have ho : ((S (reg 0))[n]?).toList.length ≤ 1 := by
    cases (S (reg 0))[n]? <;> simp
  omega

end GroupWL.MachinePrograms.Structured
