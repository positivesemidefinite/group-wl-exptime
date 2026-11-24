import GroupWL.MachinePrograms.UnaryDivision
import GroupWL.BinaryAddress

/-! Fixed-width little-endian binary emission by repeated unary division.
The emitted word is pushed onto the output stack in reverse order. -/
namespace GroupWL.MachinePrograms.Structured

variable {K : Type*} [DecidableEq K]

def binaryWord (d n : ℕ) : List Bool := List.ofFn (BinaryAddress.ofNat d n)

@[simp] theorem binaryWord_zero (n : ℕ) : binaryWord 0 n = [] := rfl
@[simp] theorem binaryWord_length (d n : ℕ) : (binaryWord d n).length = d := by simp [binaryWord]
theorem binaryWord_succ (d n : ℕ) :
    binaryWord (d+1) n = decide (n%2=1) :: binaryWord d (n/2) := by
  simp [binaryWord, BinaryAddress.ofNat, List.ofFn_succ]

def binaryDivisionRegisters (reg : Fin 12 ↪ K) : Fin 7 ↪ K where
  toFun i := reg ⟨i.val+3, by omega⟩
  inj' := by
    intro i j h
    have hv := congrArg Fin.val (reg.injective h)
    apply Fin.ext
    dsimp at hv
    omega

/-- Registers 0,1,2 are input value, width, output; 3=current value, 4=two,
5/6=quotient/remainder, 7/8/9=division scratch, 10=width counter, 11=copy scratch. -/
def binaryBody (reg : Fin 12 ↪ K) : Program K :=
  .seq (divideUnary (binaryDivisionRegisters reg))
    (.seq (.peek (reg 6) (.push (reg 2) false) (.push (reg 2) true) (.push (reg 2) true))
      (.seq (clear (reg 3))
        (.seq (transfer (reg 5) (reg 3)) (.seq (clear (reg 6)) (discard (reg 10))))))

def binaryLoop (reg : Fin 12 ↪ K) : Program K :=
  .while (reg 10) Option.isSome (binaryBody reg)

theorem binaryBody_runs (S : Store K) (reg : Fin 12 ↪ K) (n d : ℕ)
    (hn : S (reg 3) = unary n) (hwidth : S (reg 10) = unary (d+1))
    (htwo : S (reg 4) = unary 2)
    (hempty : ∀ i : Fin 12, 5 ≤ i.val → i.val ≤ 9 → S (reg i) = []) :
    ∃ t ≤ 70*(n+1), Runs (binaryBody reg) S t
      (Function.update (Function.update (Function.update S (reg 3) (unary (n/2)))
        (reg 10) (unary d)) (reg 2) (decide (n%2=1) :: S (reg 2))) := by
  let D := Function.update (Function.update S (reg 5) (unary (n/2))) (reg 6) (unary (n%2))
  obtain ⟨t, ht, hdiv⟩ := divideUnary_runs S (binaryDivisionRegisters reg) n 2 (by decide)
    hn htwo (fun i hi => hempty ⟨i.val+3, by omega⟩
      (by change 5 ≤ i.val+3; omega) (by change i.val+3 ≤ 9; omega))
  change Runs (divideUnary (binaryDivisionRegisters reg)) S t D at hdiv
  let E := Function.update D (reg 2) (decide (n%2=1) :: S (reg 2))
  let F := Function.update E (reg 3) []
  let G := Function.update (Function.update F (reg 5) []) (reg 3) (unary (n/2))
  let H := Function.update G (reg 6) []
  have hemit : Runs (.peek (reg 6) (.push (reg 2) false) (.push (reg 2) true) (.push (reg 2) true))
      D 2 E := by
    apply Runs.peek
    by_cases hr : n%2 = 0
    · simpa [select, E, D, Function.update_apply, reg.apply_eq_iff_eq, hr, unary] using
        Runs.push D (reg 2) false
    · have hr' : n%2 = 1 := by have := Nat.mod_lt n (by decide : 0 < 2); omega
      simpa [select, E, D, Function.update_apply, reg.apply_eq_iff_eq, hr', unary] using
        Runs.push D (reg 2) true
  have hclear : Runs (clear (reg 3)) E (2*n+1) F := by
    simpa [F, E, D, Function.update_apply, reg.apply_eq_iff_eq, hn] using clear_runs E (reg 3)
  have htransfer : Runs (transfer (reg 5) (reg 3)) F (3*(n/2)+1) G := by
    simpa [G, F, E, D, Function.update_apply, reg.apply_eq_iff_eq] using
      transfer_runs F (reg 5) (reg 3) (reg.injective.ne (by decide))
  have hrem : Runs (clear (reg 6)) G (2*(n%2)+1) H := by
    simpa [H, G, F, E, D, Function.update_apply, reg.apply_eq_iff_eq] using clear_runs G (reg 6)
  have hdiscard : Runs (discard (reg 10)) H 1
      (Function.update H (reg 10) (unary d)) := by
    simpa [H, G, F, E, D, Function.update_apply, reg.apply_eq_iff_eq,
      hwidth, unary, List.replicate_succ] using discard_runs H (reg 10)
  have he : Function.update H (reg 10) (unary d) =
      Function.update (Function.update (Function.update S (reg 3) (unary (n/2)))
        (reg 10) (unary d)) (reg 2) (decide (n%2=1) :: S (reg 2)) := by
    funext k
    by_cases hk2 : k = reg 2
    · subst k
      simp [H, G, F, E, Function.update_apply, reg.apply_eq_iff_eq]
    · by_cases hk3 : k = reg 3
      · subst k
        simp [H, G, Function.update_apply, reg.apply_eq_iff_eq]
      · by_cases hk5 : k = reg 5
        · subst k
          simp [H, G, Function.update_apply, reg.apply_eq_iff_eq, hempty 5 (by decide) (by decide)]
        · by_cases hk6 : k = reg 6
          · subst k
            simp [H, Function.update_apply, reg.apply_eq_iff_eq, hempty 6 (by decide) (by decide)]
          · by_cases hk10 : k = reg 10
            · subst k
              simp [Function.update_apply, reg.apply_eq_iff_eq]
            · simp [H, G, F, E, D, Function.update_of_ne hk2, Function.update_of_ne hk3,
                Function.update_of_ne hk5, Function.update_of_ne hk6, Function.update_of_ne hk10]
  rw [he] at hdiscard
  have run := Runs.seq hdiv (Runs.seq hemit (Runs.seq hclear
    (Runs.seq htransfer (Runs.seq hrem hdiscard))))
  refine ⟨t+(2+((2*n+1)+((3*(n/2)+1)+((2*(n%2)+1)+1)))), ?_, run⟩
  have hq : n/2 ≤ n := Nat.div_le_self _ _
  have hr := Nat.mod_lt n (by decide : 0 < 2)
  nlinarith

theorem binaryLoop_runs (reg : Fin 12 ↪ K) (d : ℕ) : ∀ (S : Store K) (n : ℕ),
    S (reg 3) = unary n → S (reg 10) = unary d → S (reg 4) = unary 2 →
    (∀ i : Fin 12, 5 ≤ i.val → i.val ≤ 9 → S (reg i) = []) →
    ∃ t ≤ 71*d*(n+1)+1, Runs (binaryLoop reg) S t
      (Function.update (Function.update (Function.update S (reg 3) (unary (n/2^d)))
        (reg 10) []) (reg 2) ((binaryWord d n).reverse ++ S (reg 2))) := by
  induction d with
  | zero =>
    intro S n hn hw ht he
    have hfinal : Function.update (Function.update (Function.update S (reg 3) (unary (n/2^0)))
        (reg 10) []) (reg 2) ((binaryWord 0 n).reverse ++ S (reg 2)) = S := by
      simp only [pow_zero, Nat.div_one, ← hn, Function.update_eq_self, binaryWord_zero,
        List.reverse_nil, List.nil_append]
      have hz : S (reg 10) = [] := by simpa [unary] using hw
      rw [← hz, Function.update_eq_self, Function.update_eq_self]
    rw [hfinal]
    refine ⟨1, by omega, Runs.while_false ?_⟩
    simp [hw, unary]
  | succ d ih =>
    intro S n hn hw ht he
    let A := Function.update (Function.update (Function.update S (reg 3) (unary (n/2)))
      (reg 10) (unary d)) (reg 2) (decide (n%2=1) :: S (reg 2))
    obtain ⟨u, hu, hbody⟩ := binaryBody_runs S reg n d hn hw ht he
    change Runs (binaryBody reg) S u A at hbody
    have ha3 : A (reg 3) = unary (n/2) := by simp [A, Function.update_apply, reg.apply_eq_iff_eq]
    have ha10 : A (reg 10) = unary d := by simp [A, Function.update_apply, reg.apply_eq_iff_eq]
    have ha4 : A (reg 4) = unary 2 := by simp [A, Function.update_apply, reg.apply_eq_iff_eq, ht]
    have hae : ∀ i : Fin 12, 5 ≤ i.val → i.val ≤ 9 → A (reg i) = [] := by
      intro i hi hj
      have hi2 : i ≠ (2 : Fin 12) := by intro h; subst i; norm_num at hi
      have hi3 : i ≠ (3 : Fin 12) := by intro h; subst i; norm_num at hi
      have hi10 : i ≠ (10 : Fin 12) := by intro h; subst i; norm_num at hj
      simp [A, Function.update_apply, reg.apply_eq_iff_eq, hi2, hi3, hi10, he i hi hj]
    obtain ⟨t, htime, hrest⟩ := ih A (n/2) ha3 ha10 ha4 hae
    have hf : Function.update (Function.update (Function.update A (reg 3) (unary ((n/2)/2^d)))
        (reg 10) []) (reg 2) ((binaryWord d (n/2)).reverse ++ A (reg 2)) =
        Function.update (Function.update (Function.update S (reg 3) (unary (n/2^(d+1))))
          (reg 10) []) (reg 2) ((binaryWord (d+1) n).reverse ++ S (reg 2)) := by
      funext k
      by_cases hk2 : k = reg 2
      · subst k
        simp [A, binaryWord_succ, List.reverse_cons, List.append_assoc]
      · by_cases hk3 : k = reg 3
        · subst k
          simp [Function.update_apply, reg.apply_eq_iff_eq, Nat.div_div_eq_div_mul,
            Nat.pow_succ']
        · by_cases hk10 : k = reg 10
          · subst k
            simp [Function.update_apply, reg.apply_eq_iff_eq]
          · simp [A, Function.update_of_ne hk2, Function.update_of_ne hk3, Function.update_of_ne hk10]
    rw [hf] at hrest
    have run := Runs.while_true (S := S) (test := Option.isSome)
      (by simp [hw, unary, List.replicate_succ]) hbody hrest
    refine ⟨u+t+1, ?_, run⟩
    have hq : n/2 ≤ n := Nat.div_le_self _ _
    have ht' : t ≤ 71*d*(n+1)+1 := htime.trans (by gcongr)
    nlinarith

/-- Emit exactly d low-to-high bits, including zero padding, while preserving
both unary inputs and restoring every scratch register. -/
def emitBinary (reg : Fin 12 ↪ K) : Program K :=
  .seq (copy (reg 0) (reg 3) (reg 11))
    (.seq (copy (reg 1) (reg 10) (reg 11))
      (.seq (pushUnary (reg 4) 2)
        (.seq (binaryLoop reg) (.seq (clear (reg 3)) (clear (reg 4))))))

theorem emitBinary_runs (S : Store K) (reg : Fin 12 ↪ K) (n d : ℕ)
    (hn : S (reg 0) = unary n) (hd : S (reg 1) = unary d)
    (hempty : ∀ i : Fin 12, 3 ≤ i.val → S (reg i) = []) :
    ∃ t ≤ 200*(n+d+1)^2, Runs (emitBinary reg) S t
      (Function.update S (reg 2) ((binaryWord d n).reverse ++ S (reg 2))) := by
  let A := Function.update S (reg 3) (unary n)
  let B := Function.update A (reg 10) (unary d)
  let C := Function.update B (reg 4) (unary 2)
  have hfirst : Runs (copy (reg 0) (reg 3) (reg 11)) S (7*n+2) A := by
    simpa [A, hn, hempty 3 (by decide)] using copy_runs S (reg 0) (reg 3) (reg 11)
      (reg.injective.ne (by decide)) (reg.injective.ne (by decide))
      (reg.injective.ne (by decide)) (hempty 11 (by decide))
  have hsecond : Runs (copy (reg 1) (reg 10) (reg 11)) A (7*d+2) B := by
    have run := copy_runs A (reg 1) (reg 10) (reg 11)
      (reg.injective.ne (by decide)) (reg.injective.ne (by decide))
      (reg.injective.ne (by decide))
      (by simp [A, Function.update_apply, reg.apply_eq_iff_eq, hempty 11 (by decide)])
    simpa [B, A, Function.update_apply, reg.apply_eq_iff_eq, hd, hempty 10 (by decide)] using run
  have htwo : Runs (pushUnary (reg 4) 2) B 2 C := by
    simpa [C, B, A, Function.update_apply, reg.apply_eq_iff_eq, hempty 4 (by decide)] using
      pushUnary_runs (reg 4) 2 B
  have hc3 : C (reg 3) = unary n := by simp [C, B, A, Function.update_apply, reg.apply_eq_iff_eq]
  have hc10 : C (reg 10) = unary d := by simp [C, B, Function.update_apply, reg.apply_eq_iff_eq]
  have hc4 : C (reg 4) = unary 2 := by simp [C]
  have hce : ∀ i : Fin 12, 5 ≤ i.val → i.val ≤ 9 → C (reg i) = [] := by
    intro i hi hj
    have hi3 : i ≠ (3 : Fin 12) := by intro h; subst i; norm_num at hi
    have hi4 : i ≠ (4 : Fin 12) := by intro h; subst i; norm_num at hi
    have hi10 : i ≠ (10 : Fin 12) := by intro h; subst i; norm_num at hj
    simp [C, B, A, Function.update_apply, reg.apply_eq_iff_eq, hi3, hi4, hi10,
      hempty i (by omega)]
  obtain ⟨t, ht, hloop⟩ := binaryLoop_runs reg d C n hc3 hc10 hc4 hce
  let D := Function.update (Function.update (Function.update C (reg 3) (unary (n/2^d)))
    (reg 10) []) (reg 2) ((binaryWord d n).reverse ++ C (reg 2))
  change Runs (binaryLoop reg) C t D at hloop
  let E := Function.update D (reg 3) []
  have hclear : Runs (clear (reg 3)) D (2*(n/2^d)+1) E := by
    simpa [E, D, Function.update_apply, reg.apply_eq_iff_eq] using clear_runs D (reg 3)
  have hfinish : Runs (clear (reg 4)) E 5
      (Function.update S (reg 2) ((binaryWord d n).reverse ++ S (reg 2))) := by
    have run := clear_runs E (reg 4)
    have he4 : E (reg 4) = unary 2 := by simp [E, D, C, Function.update_apply, reg.apply_eq_iff_eq]
    have hfinal : Function.update E (reg 4) [] =
        Function.update S (reg 2) ((binaryWord d n).reverse ++ S (reg 2)) := by
      funext k
      by_cases hk2 : k = reg 2
      · subst k
        simp [E, D, C, B, A, Function.update_apply, reg.apply_eq_iff_eq]
      · by_cases hk3 : k = reg 3
        · subst k
          simp [E, Function.update_apply, reg.apply_eq_iff_eq, hempty 3 (by decide)]
        · by_cases hk4 : k = reg 4
          · subst k
            simp [Function.update_apply, reg.apply_eq_iff_eq, hempty 4 (by decide)]
          · by_cases hk10 : k = reg 10
            · subst k
              simp [E, D, Function.update_apply, reg.apply_eq_iff_eq, hempty 10 (by decide)]
            · simp [E, D, C, B, A, Function.update_of_ne hk2, Function.update_of_ne hk3,
                Function.update_of_ne hk4, Function.update_of_ne hk10]
    rw [hfinal, he4, unary_length] at run
    exact run
  have run := Runs.seq hfirst (Runs.seq hsecond (Runs.seq htwo
    (Runs.seq hloop (Runs.seq hclear hfinish))))
  refine ⟨(7*n+2)+((7*d+2)+(2+(t+((2*(n/2^d)+1)+5)))), ?_, run⟩
  have hq : n/2^d ≤ n := Nat.div_le_self _ _
  nlinarith

/-- A natural-order bit list for preserved indexed lookup or singleton-domain
emission. With an initially empty output, register 11 receives the LSB-first
word and register 2 is restored empty. -/
def binaryNatural (reg : Fin 12 ↪ K) : Program K :=
  .seq (emitBinary reg) (transfer (reg 2) (reg 11))

theorem binaryNatural_runs (S : Store K) (reg : Fin 12 ↪ K) (n d : ℕ)
    (hn : S (reg 0) = unary n) (hd : S (reg 1) = unary d) (hout : S (reg 2) = [])
    (hempty : ∀ i : Fin 12, 3 ≤ i.val → S (reg i) = []) :
    ∃ t ≤ 210*(n+d+1)^2, Runs (binaryNatural reg) S t
      (Function.update S (reg 11) (binaryWord d n)) := by
  obtain ⟨t, ht, hr⟩ := emitBinary_runs S reg n d hn hd hempty
  let A := Function.update S (reg 2) (binaryWord d n).reverse
  have hr' : Runs (emitBinary reg) S t A := by simpa [A, hout] using hr
  have hs := transfer_runs A (reg 2) (reg 11) (reg.injective.ne (by decide))
  have ha : A (reg 2) = (binaryWord d n).reverse := by simp [A]
  have h11 : A (reg 11) = [] := by
    simp [A, Function.update_apply, reg.apply_eq_iff_eq, hempty 11 (by decide)]
  have he : Function.update (Function.update A (reg 2) []) (reg 11)
      ((A (reg 2)).reverse ++ A (reg 11)) = Function.update S (reg 11) (binaryWord d n) := by
    have hreset : Function.update A (reg 2) [] = S := by
      simp only [A, Function.update_idem]
      rw [← hout, Function.update_eq_self]
    rw [hreset, ha, h11, List.reverse_reverse, List.append_nil]
  rw [he, ha, List.length_reverse, binaryWord_length] at hs
  refine ⟨t+(3*d+1), ?_, Runs.seq hr' hs⟩
  have hbig : d+1 ≤ (n+d+1)^2 :=
    (by omega : d+1 ≤ n+d+1).trans (Nat.le_self_pow (by decide : 2 ≠ 0) _)
  omega

end GroupWL.MachinePrograms.Structured
