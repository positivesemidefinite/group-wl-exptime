import GroupWL.MachinePrograms.StackLibrary

/-! Materialized natural-number arrays on Boolean stacks. An entry n is n true
bits followed by false. Every operation below is a fixed structured program. -/
namespace GroupWL.MachinePrograms.Structured

variable {K : Type*} [DecidableEq K]

def arrayWord : List ℕ → List Bool
  | [] => []
  | n::xs => List.replicate n true ++ false :: arrayWord xs

@[simp] theorem arrayWord_nil : arrayWord [] = [] := rfl

@[simp] theorem arrayWord_cons (n : ℕ) (xs : List ℕ) :
    arrayWord (n::xs) = List.replicate n true ++ false :: arrayWord xs := rfl

@[simp] theorem arrayWord_append (xs ys : List ℕ) :
    arrayWord (xs++ys) = arrayWord xs ++ arrayWord ys := by
  induction xs with
  | nil => rfl
  | cons n xs ih => simp [ih, List.append_assoc]

@[simp] theorem arrayWord_length (xs : List ℕ) :
    (arrayWord xs).length = xs.sum + xs.length := by
  induction xs with
  | nil => rfl
  | cons n xs ih => simp [ih]; omega

def topTrue : Option Bool → Bool
  | some true => true
  | _ => false

def moveOnes (data saved : K) : Program K :=
  .while data topTrue (.seq (discard data) (.push saved true))

theorem moveOnes_runs (data saved : K) (hne : data ≠ saved) (n : ℕ) (tail : List Bool)
    (hstop : topTrue tail.head? = false) :
    ∀ S : Store K, S data = List.replicate n true ++ tail →
      Runs (moveOnes data saved) S (3*n+1)
        (Function.update (Function.update S data tail) saved (List.replicate n true ++ S saved)) := by
  induction n with
  | zero =>
    intro S hs
    have hd : S data = tail := by simpa using hs
    have he : Function.update (Function.update S data tail) saved
        (List.replicate 0 true ++ S saved) = S := by
      rw [← hd, Function.update_eq_self]
      simp
    rw [he]
    exact Runs.while_false (by simpa [hd] using hstop)
  | succ n ih =>
    intro S hs
    let S' := Function.update (Function.update S data (List.replicate n true ++ tail))
      saved (true :: S saved)
    have hd : S data = true :: (List.replicate n true ++ tail) := by
      simpa [List.replicate_succ] using hs
    have hd' : S' data = List.replicate n true ++ tail := by simp [S', hne]
    have hp' : S' saved = true :: S saved := by simp [S']
    have first : Runs (.seq (discard data) (.push saved true)) S 2 S' := by
      have h1 := discard_runs S data
      have h2 := Runs.push (Function.update S data (S data).tail) saved true
      simpa [S', hd, Ne.symm hne] using Runs.seq h1 h2
    have rest := ih S' hd'
    have run := Runs.while_true (test := topTrue) (by simp [hd, topTrue]) first rest
    have he : Function.update (Function.update S' data tail) saved
        (List.replicate n true ++ S' saved) =
        Function.update (Function.update S data tail) saved
          (List.replicate (n+1) true ++ S saved) := by
      funext k
      by_cases hp : k = saved
      · subst k
        simp [hp', List.replicate_add, List.append_assoc]
      · by_cases hd : k = data
        · subst k
          simp [hne]
        · simp [S', Function.update_of_ne hp, Function.update_of_ne hd]
    rw [he] at run
    convert run using 1 <;> simp [moveOnes] <;> omega

def moveEntry (data saved : K) : Program K :=
  .seq (moveOnes data saved) (.pop data .skip (.push saved false) (.push saved true))

theorem moveEntry_runs (S : Store K) (data saved : K) (hne : data ≠ saved)
    (n : ℕ) (tail : List Bool) (hd : S data = List.replicate n true ++ false :: tail) :
    Runs (moveEntry data saved) S (3*n+3)
      (Function.update (Function.update S data tail) saved
        (false :: (List.replicate n true ++ S saved))) := by
  let S' := Function.update (Function.update S data (false::tail))
    saved (List.replicate n true ++ S saved)
  have first : Runs (moveOnes data saved) S (3*n+1) S' :=
    moveOnes_runs data saved hne n (false::tail) rfl S hd
  have hd' : S' data = false::tail := by simp [S', hne]
  have hp' : S' saved = List.replicate n true ++ S saved := by simp [S']
  have rest : Runs (.pop data .skip (.push saved false) (.push saved true)) S' 2
      (Function.update (Function.update S' data tail) saved (false::S' saved)) := by
    apply Runs.pop (t := 1)
    simpa [select, hd', Ne.symm hne] using
      Runs.push (Function.update S' data tail) saved false
  have he : Function.update (Function.update S' data tail) saved (false::S' saved) =
      Function.update (Function.update S data tail) saved
        (false::(List.replicate n true ++ S saved)) := by
    funext k
    by_cases hp : k = saved
    · subst k; simp [hp']
    · by_cases hd : k = data
      · subst k; simp [hne]
      · simp [S', Function.update_of_ne hp, Function.update_of_ne hd]
  rw [he] at rest
  convert Runs.seq first rest using 1 <;> simp [moveEntry] <;> omega

def skipEntries (counter data saved : K) : Program K :=
  .while counter Option.isSome (.seq (discard counter) (moveEntry data saved))

theorem skipEntries_runs (counter data saved : K)
    (hcd : counter ≠ data) (hcs : counter ≠ saved) (hds : data ≠ saved)
    (pre suffix : List ℕ) :
    ∀ S : Store K, S counter = List.replicate pre.length true →
      S data = arrayWord (pre++suffix) →
      Runs (skipEntries counter data saved) S (3*pre.sum+5*pre.length+1)
        (Function.update (Function.update (Function.update S counter [])
          data (arrayWord suffix)) saved ((arrayWord pre).reverse ++ S saved)) := by
  induction pre with
  | nil =>
    intro S hc hd
    have hc' : S counter = [] := by simpa using hc
    have hd' : S data = arrayWord suffix := by simpa using hd
    have he : Function.update (Function.update (Function.update S counter [])
        data (arrayWord suffix)) saved ((arrayWord []).reverse ++ S saved) = S := by
      rw [← hc', Function.update_eq_self, ← hd', Function.update_eq_self]
      simp
    rw [he]
    exact Runs.while_false (by simp [hc'])
  | cons n pre ih =>
    intro S hc hd
    let S₀ := Function.update S counter (List.replicate pre.length true)
    let S' := Function.update (Function.update S₀ data (arrayWord (pre++suffix)))
      saved (false :: (List.replicate n true ++ S saved))
    have hc' : S' counter = List.replicate pre.length true := by simp [S', S₀, hcd, hcs]
    have hd' : S' data = arrayWord (pre++suffix) := by simp [S', hds]
    have hs' : S' saved = false :: (List.replicate n true ++ S saved) := by simp [S']
    have hd₀ : S₀ data = List.replicate n true ++ false :: arrayWord (pre++suffix) := by
      simpa [S₀, Ne.symm hcd] using hd
    have first : Runs (.seq (discard counter) (moveEntry data saved)) S (3*n+4) S' := by
      have h1 : Runs (discard counter) S 1 S₀ := by
        simpa [S₀, hc, List.replicate_succ] using discard_runs S counter
      have h2 := moveEntry_runs S₀ data saved hds n (arrayWord (pre++suffix)) hd₀
      convert Runs.seq h1 h2 using 1 <;> (try simp [S', S₀, Ne.symm hcs]) <;> omega
    have rest := ih S' hc' hd'
    have run := Runs.while_true (test := Option.isSome)
      (by simp [hc, List.replicate_succ]) first rest
    have he : Function.update (Function.update (Function.update S' counter [])
        data (arrayWord suffix)) saved ((arrayWord pre).reverse ++ S' saved) =
        Function.update (Function.update (Function.update S counter [])
          data (arrayWord suffix)) saved ((arrayWord (n::pre)).reverse ++ S saved) := by
      funext k
      by_cases hs : k = saved
      · subst k
        simp [hs', List.reverse_append, List.append_assoc]
      · by_cases hd : k = data
        · subst k; simp [hds]
        · by_cases hc : k = counter
          · subst k; simp [hcd, hcs]
          · simp [S', S₀, Function.update_of_ne hs, Function.update_of_ne hd,
              Function.update_of_ne hc]
    rw [he] at run
    convert run using 1 <;> simp [skipEntries] <;> omega

def arrayRead (r : Fin 5 ↪ K) : Program K :=
  .seq (skipEntries (r 0) (r 1) (r 3))
    (.seq (moveOnes (r 1) (r 2))
      (.seq (copy (r 2) (r 1) (r 4)) (transfer (r 3) (r 1))))

theorem arrayRead_runs (r : Fin 5 ↪ K) (S : Store K) (pre : List ℕ) (v : ℕ) (suf : List ℕ)
    (hc : S (r 0) = List.replicate pre.length true)
    (hd : S (r 1) = arrayWord (pre ++ v::suf))
    (hv : S (r 2) = []) (hs : S (r 3) = []) (ht : S (r 4) = []) :
    Runs (arrayRead r) S (6*pre.sum+8*pre.length+10*v+5)
      (Function.update (Function.update S (r 0) []) (r 2) (List.replicate v true)) := by
  have heq (i j : Fin 5) : r i = r j ↔ i = j := r.injective.eq_iff
  have hne (i j : Fin 5) (h : i ≠ j) : r i ≠ r j := r.injective.ne h
  let S₁ := Function.update (Function.update (Function.update S (r 0) [])
    (r 1) (arrayWord (v::suf))) (r 3) (arrayWord pre).reverse
  let S₂ := Function.update (Function.update S₁ (r 1) (false::arrayWord suf))
    (r 2) (List.replicate v true)
  let S₃ := Function.update S₂ (r 1) (arrayWord (v::suf))
  have h1 : Runs (skipEntries (r 0) (r 1) (r 3)) S
      (3*pre.sum+5*pre.length+1) S₁ := by
    simpa [S₁, hs] using skipEntries_runs (r 0) (r 1) (r 3)
      (hne 0 1 (by decide)) (hne 0 3 (by decide)) (hne 1 3 (by decide)) pre (v::suf) S hc hd
  have hd1 : S₁ (r 1) = List.replicate v true ++ false::arrayWord suf := by simp [S₁, heq]
  have hv1 : S₁ (r 2) = [] := by simp [S₁, heq, hv]
  have h2 : Runs (moveOnes (r 1) (r 2)) S₁ (3*v+1) S₂ := by
    simpa [S₂, hv1] using moveOnes_runs (r 1) (r 2) (hne 1 2 (by decide))
      v (false::arrayWord suf) rfl S₁ hd1
  have ht2 : S₂ (r 4) = [] := by simp [S₂, S₁, heq, ht]
  have hv2 : S₂ (r 2) = List.replicate v true := by simp [S₂]
  have hd2 : S₂ (r 1) = false::arrayWord suf := by simp [S₂, heq]
  have h3 : Runs (copy (r 2) (r 1) (r 4)) S₂ (7*v+2) S₃ := by
    simpa [S₃, hv2, hd2] using copy_runs S₂ (r 2) (r 1) (r 4)
      (hne 2 1 (by decide)) (hne 2 4 (by decide)) (hne 1 4 (by decide)) ht2
  have hs3 : S₃ (r 3) = (arrayWord pre).reverse := by simp [S₃, S₂, S₁, heq]
  have hd3 : S₃ (r 1) = arrayWord (v::suf) := by simp [S₃]
  have h4 := transfer_runs S₃ (r 3) (r 1) (hne 3 1 (by decide))
  have hend : Function.update (Function.update S₃ (r 3) [])
      (r 1) ((S₃ (r 3)).reverse ++ S₃ (r 1)) =
      Function.update (Function.update S (r 0) []) (r 2) (List.replicate v true) := by
    funext k
    by_cases h0 : k = r 0
    · subst k; simp [S₃, S₂, S₁, heq]
    · by_cases h1 : k = r 1
      · subst k; simp [hs3, hd3, heq, hd]
      · by_cases h2 : k = r 2
        · subst k; simp [S₃, S₂, S₁, heq]
        · by_cases h3 : k = r 3
          · subst k; simp [heq, hs]
          · simp [S₃, S₂, S₁, Function.update_of_ne h0, Function.update_of_ne h1,
              Function.update_of_ne h2, Function.update_of_ne h3]
  rw [hend, hs3, List.length_reverse, arrayWord_length] at h4
  have hrun := Runs.seq h1 (Runs.seq h2 (Runs.seq h3 h4))
  convert hrun using 1 <;> (try simp [arrayRead]) <;> omega

theorem arrayRead_cost (pre : List ℕ) (v : ℕ) (suf : List ℕ) :
    6*pre.sum+8*pre.length+10*v+5 ≤ 10*((arrayWord (pre++v::suf)).length+1) := by
  simp
  omega

def arrayWrite (r : Fin 5 ↪ K) : Program K :=
  .seq (skipEntries (r 0) (r 1) (r 3))
    (.seq (moveOnes (r 1) (r 4))
      (.seq (clear (r 4))
        (.seq (copy (r 2) (r 1) (r 4)) (transfer (r 3) (r 1)))))

theorem arrayWrite_runs (r : Fin 5 ↪ K) (S : Store K) (pre : List ℕ)
    (old value : ℕ) (suf : List ℕ)
    (hc : S (r 0) = List.replicate pre.length true)
    (hd : S (r 1) = arrayWord (pre ++ old::suf))
    (hv : S (r 2) = List.replicate value true) (hs : S (r 3) = []) (ht : S (r 4) = []) :
    Runs (arrayWrite r) S (6*pre.sum+8*pre.length+5*old+7*value+6)
      (Function.update (Function.update S (r 0) []) (r 1) (arrayWord (pre++value::suf))) := by
  have heq (i j : Fin 5) : r i = r j ↔ i = j := r.injective.eq_iff
  have hne (i j : Fin 5) (h : i ≠ j) : r i ≠ r j := r.injective.ne h
  let S₁ := Function.update (Function.update (Function.update S (r 0) [])
    (r 1) (arrayWord (old::suf))) (r 3) (arrayWord pre).reverse
  let S₂ := Function.update (Function.update S₁ (r 1) (false::arrayWord suf))
    (r 4) (List.replicate old true)
  let S₃ := Function.update S₂ (r 4) []
  let S₄ := Function.update S₃ (r 1) (arrayWord (value::suf))
  have h1 : Runs (skipEntries (r 0) (r 1) (r 3)) S
      (3*pre.sum+5*pre.length+1) S₁ := by
    simpa [S₁, hs] using skipEntries_runs (r 0) (r 1) (r 3)
      (hne 0 1 (by decide)) (hne 0 3 (by decide)) (hne 1 3 (by decide)) pre (old::suf) S hc hd
  have hd1 : S₁ (r 1) = List.replicate old true ++ false::arrayWord suf := by simp [S₁, heq]
  have ht1 : S₁ (r 4) = [] := by simp [S₁, heq, ht]
  have h2 : Runs (moveOnes (r 1) (r 4)) S₁ (3*old+1) S₂ := by
    simpa [S₂, ht1] using moveOnes_runs (r 1) (r 4) (hne 1 4 (by decide))
      old (false::arrayWord suf) rfl S₁ hd1
  have ht2 : S₂ (r 4) = List.replicate old true := by simp [S₂]
  have h3 : Runs (clear (r 4)) S₂ (2*old+1) S₃ := by
    simpa [S₃, ht2] using clear_runs S₂ (r 4)
  have ht3 : S₃ (r 4) = [] := by simp [S₃]
  have hv3 : S₃ (r 2) = List.replicate value true := by simp [S₃, S₂, S₁, heq, hv]
  have hd3 : S₃ (r 1) = false::arrayWord suf := by simp [S₃, S₂, heq]
  have h4 : Runs (copy (r 2) (r 1) (r 4)) S₃ (7*value+2) S₄ := by
    simpa [S₄, hv3, hd3] using copy_runs S₃ (r 2) (r 1) (r 4)
      (hne 2 1 (by decide)) (hne 2 4 (by decide)) (hne 1 4 (by decide)) ht3
  have hs4 : S₄ (r 3) = (arrayWord pre).reverse := by simp [S₄, S₃, S₂, S₁, heq]
  have hd4 : S₄ (r 1) = arrayWord (value::suf) := by simp [S₄]
  have h5 := transfer_runs S₄ (r 3) (r 1) (hne 3 1 (by decide))
  have hend : Function.update (Function.update S₄ (r 3) [])
      (r 1) ((S₄ (r 3)).reverse ++ S₄ (r 1)) =
      Function.update (Function.update S (r 0) []) (r 1) (arrayWord (pre++value::suf)) := by
    funext k
    by_cases h0 : k = r 0
    · subst k; simp [S₄, S₃, S₂, S₁, heq]
    · by_cases h1 : k = r 1
      · subst k; simp [hs4, hd4]
      · by_cases h3 : k = r 3
        · subst k; simp [heq, hs]
        · by_cases h4 : k = r 4
          · subst k; simp [S₄, S₃, heq, ht]
          · simp [S₄, S₃, S₂, S₁, Function.update_of_ne h0, Function.update_of_ne h1,
              Function.update_of_ne h3, Function.update_of_ne h4]
  rw [hend, hs4, List.length_reverse, arrayWord_length] at h5
  have hrun := Runs.seq h1 (Runs.seq h2 (Runs.seq h3 (Runs.seq h4 h5)))
  convert hrun using 1 <;> (try simp [arrayWrite]) <;> omega

theorem arrayWrite_cost (pre : List ℕ) (old value : ℕ) (suf : List ℕ) :
    6*pre.sum+8*pre.length+5*old+7*value+6 ≤
      10*((arrayWord (pre++old::suf)).length+value+1) := by
  simp
  omega

theorem arrayRead_index (r : Fin 5 ↪ K) (S : Store K) (xs : List ℕ) (i : ℕ)
    (hi : i < xs.length) (hc : S (r 0) = List.replicate i true)
    (hd : S (r 1) = arrayWord xs) (hv : S (r 2) = [])
    (hs : S (r 3) = []) (ht : S (r 4) = []) :
    ∃ t ≤ 10*((arrayWord xs).length+1), Runs (arrayRead r) S t
      (Function.update (Function.update S (r 0) []) (r 2)
        (List.replicate (xs[i]?.getD 0) true)) := by
  have hsplit : xs = xs.take i ++ xs[i] :: xs.drop (i+1) := by
    simpa only [List.set_getElem_self hi, if_pos hi] using
      (List.set_eq_take_append_cons_drop (l := xs) (i := i) (a := xs[i]))
  have hlen : (xs.take i).length = i := by simp [List.length_take, Nat.min_eq_left hi.le]
  have hr := arrayRead_runs r S (xs.take i) xs[i] (xs.drop (i+1))
    (by simpa only [hlen] using hc) (by simpa only [← hsplit] using hd) hv hs ht
  refine ⟨6*(xs.take i).sum+8*(xs.take i).length+10*xs[i]+5, ?_, ?_⟩
  · simpa only [← hsplit] using arrayRead_cost (xs.take i) xs[i] (xs.drop (i+1))
  · simpa only [List.getElem?_eq_getElem hi, Option.getD_some] using hr

theorem arrayWrite_index (r : Fin 5 ↪ K) (S : Store K) (xs : List ℕ) (i value : ℕ)
    (hi : i < xs.length) (hc : S (r 0) = List.replicate i true)
    (hd : S (r 1) = arrayWord xs) (hv : S (r 2) = List.replicate value true)
    (hs : S (r 3) = []) (ht : S (r 4) = []) :
    ∃ t ≤ 10*((arrayWord xs).length+value+1), Runs (arrayWrite r) S t
      (Function.update (Function.update S (r 0) []) (r 1) (arrayWord (xs.set i value))) := by
  have hsplit : xs = xs.take i ++ xs[i] :: xs.drop (i+1) := by
    simpa only [List.set_getElem_self hi, if_pos hi] using
      (List.set_eq_take_append_cons_drop (l := xs) (i := i) (a := xs[i]))
  have hlen : (xs.take i).length = i := by simp [List.length_take, Nat.min_eq_left hi.le]
  have hset : xs.set i value = xs.take i ++ value :: xs.drop (i+1) := by
    rw [List.set_eq_take_append_cons_drop, if_pos hi]
  have hr := arrayWrite_runs r S (xs.take i) xs[i] value (xs.drop (i+1))
    (by simpa only [hlen] using hc) (by simpa only [← hsplit] using hd) hv hs ht
  refine ⟨6*(xs.take i).sum+8*(xs.take i).length+5*xs[i]+7*value+6, ?_, ?_⟩
  · simpa only [← hsplit] using arrayWrite_cost (xs.take i) xs[i] value (xs.drop (i+1))
  · simpa only [hset] using hr

end GroupWL.MachinePrograms.Structured
