import GroupWL.MachinePrograms.Structured

/-! Verified Boolean-list routines with explicit primitive-operation counts. -/
namespace GroupWL.MachinePrograms.Structured

variable {K : Type*} [DecidableEq K]

def discard (k : K) : Program K := .pop k .skip .skip .skip

theorem discard_runs (S : Store K) (k : K) :
    Runs (discard k) S 1 (Function.update S k (S k).tail) := by
  apply Runs.pop
  cases h : (S k).head? with
  | none => exact Runs.skip _
  | some b => cases b <;> exact Runs.skip _

def clear (k : K) : Program K := .while k Option.isSome (discard k)

theorem clear_runs_aux (k : K) (xs : List Bool) :
    ∀ S : Store K, S k = xs →
      Runs (clear k) S (2 * xs.length + 1) (Function.update S k []) := by
  induction xs with
  | nil =>
    intro S h
    have he : Function.update S k [] = S := by
      rw [← h, Function.update_eq_self]
    rw [he]
    exact Runs.while_false (by simp [h])
  | cons b xs ih =>
    intro S h
    have first := discard_runs S k
    have rest := ih (Function.update S k xs) (Function.update_self ..)
    have run := Runs.while_true (S := S) (S' := Function.update S k xs)
      (test := Option.isSome) (body := discard k)
      (by simp [h]) (by simpa [h] using first) rest
    simp only [Function.update_idem] at run
    convert run using 1 <;> simp only [List.length_cons] <;> omega

theorem clear_runs (S : Store K) (k : K) :
    Runs (clear k) S (2 * (S k).length + 1) (Function.update S k []) :=
  clear_runs_aux k (S k) S rfl

/-- Consume one stack and prepend its reversal to another stack. -/
def transfer (source target : K) : Program K :=
  .while source Option.isSome (.pop source .skip (.push target false) (.push target true))

theorem transfer_runs_aux (source target : K) (hne : source ≠ target) (xs : List Bool) :
    ∀ S : Store K, S source = xs →
      Runs (transfer source target) S (3 * xs.length + 1)
        (Function.update (Function.update S source []) target (xs.reverse ++ S target)) := by
  induction xs with
  | nil =>
    intro S hs
    have he : Function.update (Function.update S source []) target ([] ++ S target) = S := by
      have h0 : Function.update S source [] = S := by rw [← hs, Function.update_eq_self]
      simp [h0]
    rw [List.reverse_nil, he]
    exact Runs.while_false (by simp [hs])
  | cons b xs ih =>
    intro S hs
    let S' := Function.update (Function.update S source xs) target (b :: S target)
    have hs' : S' source = xs := by simp [S', hne]
    have ht' : S' target = b :: S target := by simp [S']
    have first : Runs (.pop source .skip (.push target false) (.push target true)) S 2 S' := by
      apply Runs.pop
      cases b <;>
        simpa [select, hs, S', Function.update_of_ne (Ne.symm hne)] using
          (Runs.push (Function.update S source xs) target _)
    have rest := ih S' hs'
    have run := Runs.while_true (test := Option.isSome)
      (by simp [hs]) first rest
    have he : Function.update (Function.update S' source []) target (xs.reverse ++ S' target) =
        Function.update (Function.update S source []) target ((b :: xs).reverse ++ S target) := by
      funext k
      by_cases hk : k = target
      · subst k
        simp [ht', List.reverse_cons, List.append_assoc]
      · by_cases hk' : k = source
        · subst k
          simp [S', hne]
        · simp [S', Function.update_of_ne hk, Function.update_of_ne hk']
    rw [he] at run
    convert run using 1 <;> simp [transfer, List.length_cons] <;> omega

theorem transfer_runs (S : Store K) (source target : K) (hne : source ≠ target) :
    Runs (transfer source target) S (3 * (S source).length + 1)
      (Function.update (Function.update S source []) target ((S source).reverse ++ S target)) :=
  transfer_runs_aux source target hne (S source) S rfl

/-- Consume one source and prepend its reversal to two distinct targets. -/
def splitTransfer (source left right : K) : Program K :=
  .while source Option.isSome (.pop source .skip
    (.seq (.push left false) (.push right false))
    (.seq (.push left true) (.push right true)))

theorem splitTransfer_runs_aux (source left right : K)
    (hsl : source ≠ left) (hsr : source ≠ right) (hlr : left ≠ right) (xs : List Bool) :
    ∀ S : Store K, S source = xs →
      Runs (splitTransfer source left right) S (4 * xs.length + 1)
        (Function.update (Function.update (Function.update S source [])
          left (xs.reverse ++ S left)) right (xs.reverse ++ S right)) := by
  induction xs with
  | nil =>
    intro S hs
    have h0 : Function.update S source [] = S := by rw [← hs, Function.update_eq_self]
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add, List.reverse_nil,
      List.nil_append, h0, Function.update_eq_self]
    exact Runs.while_false (by simp [hs])
  | cons b xs ih =>
    intro S hs
    let S' := Function.update (Function.update (Function.update S source xs)
      left (b :: S left)) right (b :: S right)
    have hs' : S' source = xs := by simp [S', hsl, hsr]
    have hl' : S' left = b :: S left := by simp [S', hlr]
    have hr' : S' right = b :: S right := by simp [S']
    have pushes : Runs (.seq (.push left b) (.push right b))
        (Function.update S source xs) 2 S' := by
      have run := Runs.seq (Runs.push (Function.update S source xs) left b)
        (Runs.push (Function.update (Function.update S source xs) left
          (b :: (Function.update S source xs) left)) right b)
      simpa [S', Ne.symm hsl, Ne.symm hsr, Ne.symm hlr] using run
    have first : Runs (.pop source .skip
        (.seq (.push left false) (.push right false))
        (.seq (.push left true) (.push right true))) S 3 S' := by
      apply Runs.pop
      cases b <;> simpa [select, hs] using pushes
    have rest := ih S' hs'
    have run := Runs.while_true (S := S) (test := Option.isSome)
      (by simp [hs]) first rest
    have he : Function.update (Function.update (Function.update S' source [])
          left (xs.reverse ++ S' left)) right (xs.reverse ++ S' right) =
        Function.update (Function.update (Function.update S source [])
          left ((b :: xs).reverse ++ S left)) right ((b :: xs).reverse ++ S right) := by
      funext k
      by_cases hk : k = right
      · subst k
        simp [hr', List.reverse_cons, List.append_assoc]
      · by_cases hk' : k = left
        · subst k
          simp [hl', hlr, List.reverse_cons, List.append_assoc]
        · by_cases hk'' : k = source
          · subst k
            simp [S', hsl, hsr]
          · simp [S', Function.update_of_ne hk, Function.update_of_ne hk',
              Function.update_of_ne hk'']
    rw [he] at run
    convert run using 1 <;> simp [List.length_cons] <;> omega

theorem splitTransfer_runs (S : Store K) (source left right : K)
    (hsl : source ≠ left) (hsr : source ≠ right) (hlr : left ≠ right) :
    Runs (splitTransfer source left right) S (4 * (S source).length + 1)
      (Function.update (Function.update (Function.update S source [])
        left ((S source).reverse ++ S left)) right ((S source).reverse ++ S right)) :=
  splitTransfer_runs_aux source left right hsl hsr hlr (S source) S rfl

/-- Copy a list, preserving its order and the source, using an empty temporary stack. -/
def copy (source target temp : K) : Program K :=
  .seq (transfer source temp) (splitTransfer temp source target)

theorem copy_runs (S : Store K) (source target temp : K)
    (hst : source ≠ target) (hsu : source ≠ temp) (htu : target ≠ temp)
    (hempty : S temp = []) :
    Runs (copy source target temp) S (7 * (S source).length + 2)
      (Function.update S target (S source ++ S target)) := by
  let S' := Function.update (Function.update S source []) temp (S source).reverse
  have first : Runs (transfer source temp) S (3 * (S source).length + 1) S' := by
    simpa [S', hempty] using transfer_runs S source temp hsu
  have rest := splitTransfer_runs S' temp source target (Ne.symm hsu) (Ne.symm htu) hst
  have hu : S' temp = (S source).reverse := by simp [S']
  have hs : S' source = [] := by simp [S', hsu]
  have ht : S' target = S target := by simp [S', htu, Ne.symm hst]
  have he : Function.update (Function.update (Function.update S' temp [])
        source ((S' temp).reverse ++ S' source)) target ((S' temp).reverse ++ S' target) =
      Function.update S target (S source ++ S target) := by
    funext k
    by_cases hk : k = target
    · subst k
      simp [hu, ht]
    · by_cases hk' : k = source
      · subst k
        simp [hu, hs, hst]
      · by_cases hk'' : k = temp
        · subst k
          simp [S', Ne.symm hsu, Ne.symm htu, hempty]
        · simp [S', Function.update_of_ne hk, Function.update_of_ne hk',
            Function.update_of_ne hk'']
  rw [he, hu, List.length_reverse] at rest
  have run := Runs.seq first rest
  convert run using 1 <;> omega

end GroupWL.MachinePrograms.Structured
