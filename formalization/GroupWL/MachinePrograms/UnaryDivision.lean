import GroupWL.MachinePrograms.UnaryArithmetic
import GroupWL.MachinePrograms.CountedLoops

/-! Quotient and remainder by scanning a unary dividend with a resettable
unary countdown. The instruction stream contains no arithmetic oracle. -/
namespace GroupWL.MachinePrograms.Structured

variable {K : Type*} [DecidableEq K]

/-- Registers: dividend, divisor, quotient, remainder, todo, countdown, temp. -/
def divisionBody (reg : Fin 7 ↪ K) : Program K :=
  .seq (discard (reg 4)) (.seq (discard (reg 5))
    (.peek (reg 5)
      (.seq (copy (reg 1) (reg 5) (reg 6))
        (.seq (clear (reg 3)) (.push (reg 2) true)))
      (.push (reg 3) true) (.push (reg 3) true)))

def divisionLoop (reg : Fin 7 ↪ K) : Program K :=
  .while (reg 4) Option.isSome (divisionBody reg)

def divisionState (S : Store K) (reg : Fin 7 ↪ K) (m b i : ℕ) : Store K :=
  Function.update (Function.update (Function.update (Function.update S
    (reg 2) (unary (i/b))) (reg 3) (unary (i%b)))
    (reg 4) (unary (m-i))) (reg 5) (unary (b-i%b))

private theorem division_next_wrap (i b : ℕ) (hb : 0 < b) (hr : i%b+1 = b) :
    (i+1)/b = i/b+1 ∧ (i+1)%b = 0 := by
  have he : i+1 = b*(i/b)+(i%b+1) := by have := Nat.div_add_mod i b; omega
  rw [he, Nat.mul_add_div hb, Nat.mul_add_mod, hr]
  simp [Nat.div_self hb]

private theorem division_next_no_wrap (i b : ℕ) (hb : 0 < b) (hr : i%b+1 ≠ b) :
    (i+1)/b = i/b ∧ (i+1)%b = i%b+1 := by
  have hlt : i%b+1 < b := by have := Nat.mod_lt i hb; omega
  have he : i+1 = b*(i/b)+(i%b+1) := by have := Nat.div_add_mod i b; omega
  rw [he, Nat.mul_add_div hb, Nat.mul_add_mod]
  simp [Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt]

def divisionBodySteps (i b : ℕ) : ℕ := if i%b+1 = b then 7*b+2*(i%b)+7 else 4

theorem divisionBody_runs (S : Store K) (reg : Fin 7 ↪ K) (m b i : ℕ)
    (hb : 0 < b) (_hi : i < m) (hdivisor : S (reg 1) = unary b) (htemp : S (reg 6) = []) :
    Runs (divisionBody reg) (divisionState S reg m b i) (divisionBodySteps i b)
      (divisionState S reg m b (i+1)) := by
  let A := divisionState S reg m b i
  let B := Function.update A (reg 4) (unary (m-(i+1)))
  let D := Function.update B (reg 5) (unary (b-i%b-1))
  have htodo : Runs (discard (reg 4)) A 1 B := by
    have he : m-i-1 = m-(i+1) := by omega
    simpa [A, B, divisionState, Function.update_apply, reg.apply_eq_iff_eq,
      unary, List.tail_replicate, he] using discard_runs A (reg 4)
  have hdown : Runs (discard (reg 5)) B 1 D := by
    simpa [D, B, A, divisionState, Function.update_apply, reg.apply_eq_iff_eq,
      unary, List.tail_replicate] using discard_runs B (reg 5)
  by_cases hwrap : i%b+1 = b
  · have hn := division_next_wrap i b hb hwrap
    have hzero : b-i%b-1 = 0 := by omega
    have hc : D (reg 5) = [] := by simp [D, hzero, unary]
    have hd : D (reg 1) = unary b := by
      simp [D, B, A, divisionState, Function.update_apply, reg.apply_eq_iff_eq, hdivisor]
    have ht : D (reg 6) = [] := by
      simp [D, B, A, divisionState, Function.update_apply, reg.apply_eq_iff_eq, htemp]
    let E := Function.update D (reg 5) (unary b)
    let G := Function.update E (reg 3) []
    have hcopy : Runs (copy (reg 1) (reg 5) (reg 6)) D (7*b+2) E := by
      simpa [E, hd, hc] using copy_runs D (reg 1) (reg 5) (reg 6)
        (reg.injective.ne (by decide)) (reg.injective.ne (by decide))
        (reg.injective.ne (by decide)) ht
    have hclear : Runs (clear (reg 3)) E (2*(i%b)+1) G := by
      simpa [G, E, D, B, A, divisionState, Function.update_apply, reg.apply_eq_iff_eq]
        using clear_runs E (reg 3)
    have hpush : Runs (.push (reg 2) true) G 1 (divisionState S reg m b (i+1)) := by
      have run := Runs.push G (reg 2) true
      have he : Function.update G (reg 2) (true :: G (reg 2)) = divisionState S reg m b (i+1) := by
        funext k
        by_cases hk2 : k = reg 2
        · subst k
          simp [G, E, D, B, A, divisionState, Function.update_apply,
            reg.apply_eq_iff_eq, hn.1, unary, List.replicate_succ]
        · by_cases hk3 : k = reg 3
          · subst k
            simp [G, divisionState, Function.update_apply, reg.apply_eq_iff_eq, hn.2, unary]
          · by_cases hk4 : k = reg 4
            · subst k
              simp [G, E, D, B, divisionState, Function.update_apply, reg.apply_eq_iff_eq]
            · by_cases hk5 : k = reg 5
              · subst k
                simp [G, E, divisionState, Function.update_apply, reg.apply_eq_iff_eq, hn.2]
              · simp [G, E, D, B, A, divisionState, Function.update_of_ne hk2,
                  Function.update_of_ne hk3, Function.update_of_ne hk4, Function.update_of_ne hk5]
      rwa [he] at run
    have hpeek := Runs.peek (k := reg 5) (S := D)
      (pn := .seq (copy (reg 1) (reg 5) (reg 6)) (.seq (clear (reg 3)) (.push (reg 2) true)))
      (pf := .push (reg 3) true) (pt := .push (reg 3) true)
      (by simpa [hc, select] using Runs.seq hcopy (Runs.seq hclear hpush))
    have run := Runs.seq htodo (Runs.seq hdown hpeek)
    convert run using 1 <;> simp only [divisionBodySteps, if_pos hwrap] <;> omega
  · have hn := division_next_no_wrap i b hb hwrap
    have hr : i%b+1 < b := by have := Nat.mod_lt i hb; omega
    have hp : 0 < b-i%b-1 := by omega
    have hc : (D (reg 5)).head? = some true := by
      simp only [D, Function.update_self, unary]
      have he : b-i%b-1 = (b-i%b-2)+1 := by omega
      rw [he, List.replicate_succ]
      rfl
    have hpush : Runs (.push (reg 3) true) D 1 (divisionState S reg m b (i+1)) := by
      have run := Runs.push D (reg 3) true
      have he : Function.update D (reg 3) (true :: D (reg 3)) = divisionState S reg m b (i+1) := by
        funext k
        by_cases hk3 : k = reg 3
        · subst k
          simp [D, B, A, divisionState, Function.update_apply, reg.apply_eq_iff_eq,
            hn.2, unary, List.replicate_succ]
        · by_cases hk2 : k = reg 2
          · subst k
            simp [D, B, A, divisionState, Function.update_apply, reg.apply_eq_iff_eq, hn.1]
          · by_cases hk4 : k = reg 4
            · subst k
              simp [D, B, divisionState, Function.update_apply, reg.apply_eq_iff_eq]
            · by_cases hk5 : k = reg 5
              · subst k
                simp only [D, Function.update_self, divisionState,
                  Function.update_of_ne (reg.injective.ne (by decide : (5 : Fin 7) ≠ 3)), hn.2]
                congr 1
              · simp [D, B, A, divisionState, Function.update_of_ne hk2,
                  Function.update_of_ne hk3, Function.update_of_ne hk4, Function.update_of_ne hk5]
      rwa [he] at run
    have hpeek := Runs.peek (k := reg 5) (S := D)
      (pn := .seq (copy (reg 1) (reg 5) (reg 6)) (.seq (clear (reg 3)) (.push (reg 2) true)))
      (pf := .push (reg 3) true) (pt := .push (reg 3) true)
      (by simpa [hc, select] using hpush)
    have run := Runs.seq htodo (Runs.seq hdown hpeek)
    simpa only [divisionBody, divisionBodySteps, if_neg hwrap] using run

theorem divisionLoop_runs (S : Store K) (reg : Fin 7 ↪ K) (m b : ℕ)
    (hb : 0 < b) (hdivisor : S (reg 1) = unary b) (htemp : S (reg 6) = []) :
    ∃ t ≤ m*(9*b+8)+1,
      Runs (divisionLoop reg) (divisionState S reg m b 0) t (divisionState S reg m b m) := by
  have htodo (i : ℕ) : divisionState S reg m b i (reg 4) = unary (m-i) := by
    simp [divisionState, Function.update_apply, reg.apply_eq_iff_eq]
  apply while_runs_bound (reg 4) Option.isSome (divisionBody reg) m (9*b+7)
    (divisionState S reg m b) (fun i => divisionBodySteps i b)
  · intro i hi
    rw [htodo]
    have he : m-i = (m-i-1)+1 := by omega
    rw [unary, he, List.replicate_succ]
    rfl
  · rw [htodo]
    simp [unary]
  · intro i hi
    exact divisionBody_runs S reg m b i hb hi hdivisor htemp
  · intro i _
    have := Nat.mod_lt i hb
    unfold divisionBodySteps
    split <;> omega

/-- Quotient and remainder of two unary inputs, preserving them and restoring
all three scratch stacks. This program is fixed independently of the inputs. -/
def divideUnary (reg : Fin 7 ↪ K) : Program K :=
  .seq (copy (reg 0) (reg 4) (reg 6))
    (.seq (copy (reg 1) (reg 5) (reg 6))
      (.seq (divisionLoop reg) (clear (reg 5))))

theorem divideUnary_runs (S : Store K) (reg : Fin 7 ↪ K) (m b : ℕ)
    (hb : 0 < b) (hdividend : S (reg 0) = unary m) (hdivisor : S (reg 1) = unary b)
    (hempty : ∀ i : Fin 7, 2 ≤ i.val → S (reg i) = []) :
    ∃ t ≤ 20*(m+1)*(b+1), Runs (divideUnary reg) S t
      (Function.update (Function.update S (reg 2) (unary (m/b))) (reg 3) (unary (m%b))) := by
  let A := Function.update S (reg 4) (unary m)
  let B := Function.update A (reg 5) (unary b)
  have first : Runs (copy (reg 0) (reg 4) (reg 6)) S (7*m+2) A := by
    simpa [A, hdividend, hempty 4 (by decide)] using copy_runs S (reg 0) (reg 4) (reg 6)
      (reg.injective.ne (by decide)) (reg.injective.ne (by decide))
      (reg.injective.ne (by decide)) (hempty 6 (by decide))
  have second : Runs (copy (reg 1) (reg 5) (reg 6)) A (7*b+2) B := by
    have run := copy_runs A (reg 1) (reg 5) (reg 6)
      (reg.injective.ne (by decide)) (reg.injective.ne (by decide))
      (reg.injective.ne (by decide))
      (by simp [A, Function.update_apply, reg.apply_eq_iff_eq, hempty 6 (by decide)])
    simpa [B, A, Function.update_apply, reg.apply_eq_iff_eq, hdivisor,
      hempty 5 (by decide)] using run
  have hstart : B = divisionState S reg m b 0 := by
    funext k
    by_cases hk5 : k = reg 5
    · subst k
      simp [B, divisionState]
    · by_cases hk4 : k = reg 4
      · subst k
        simp [B, A, divisionState, Function.update_apply, reg.apply_eq_iff_eq]
      · by_cases hk3 : k = reg 3
        · subst k
          simp [B, A, divisionState, Function.update_apply, reg.apply_eq_iff_eq,
            hempty 3 (by decide), unary]
        · by_cases hk2 : k = reg 2
          · subst k
            simp [B, A, divisionState, Function.update_apply, reg.apply_eq_iff_eq,
              hempty 2 (by decide), unary]
          · simp [B, A, divisionState, Function.update_of_ne hk2,
              Function.update_of_ne hk3, Function.update_of_ne hk4, Function.update_of_ne hk5]
  obtain ⟨t, ht, hloop⟩ := divisionLoop_runs S reg m b hb hdivisor (hempty 6 (by decide))
  rw [← hstart] at hloop
  have last : Runs (clear (reg 5)) (divisionState S reg m b m) (2*(b-m%b)+1)
      (Function.update (Function.update S (reg 2) (unary (m/b))) (reg 3) (unary (m%b))) := by
    have run := clear_runs (divisionState S reg m b m) (reg 5)
    have he : Function.update (divisionState S reg m b m) (reg 5) [] =
        Function.update (Function.update S (reg 2) (unary (m/b))) (reg 3) (unary (m%b)) := by
      funext k
      by_cases hk5 : k = reg 5
      · subst k
        simp [Function.update_apply, reg.apply_eq_iff_eq, hempty 5 (by decide)]
      · by_cases hk4 : k = reg 4
        · subst k
          simp [divisionState, Function.update_apply, reg.apply_eq_iff_eq, hempty 4 (by decide), unary]
        · simp [divisionState, Function.update_of_ne hk4, Function.update_of_ne hk5]
    rw [he] at run
    simpa [divisionState] using run
  have run := Runs.seq first (Runs.seq second (Runs.seq hloop last))
  refine ⟨(7*m+2)+((7*b+2)+(t+(2*(b-m%b)+1))), ?_, run⟩
  have hsub : b-m%b ≤ b := Nat.sub_le _ _
  nlinarith

end GroupWL.MachinePrograms.Structured
