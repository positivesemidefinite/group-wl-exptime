import GroupWL.MachinePrograms.StackLibrary

/-! Unary arithmetic by actual structured Boolean-stack programs. -/
namespace GroupWL.MachinePrograms.Structured

variable {K : Type*} [DecidableEq K]

def unary (n : ℕ) : List Bool := List.replicate n true

@[simp] theorem unary_length (n : ℕ) : (unary n).length = n := by simp [unary]
@[simp] theorem unary_reverse (n : ℕ) : (unary n).reverse = unary n := by simp [unary]
theorem unary_add (m n : ℕ) : unary (m+n) = unary m ++ unary n := List.replicate_add ..

/-- A fixed compile-time constant; its construction does not inspect the input. -/
def pushUnary (k : K) : ℕ → Program K
  | 0 => .skip
  | n+1 => .seq (.push k true) (pushUnary k n)

theorem pushUnary_runs (k : K) (n : ℕ) (S : Store K) :
    Runs (pushUnary k n) S n (Function.update S k (unary n ++ S k)) := by
  induction n generalizing S with
  | zero => simpa [pushUnary, unary] using Runs.skip S
  | succ n ih =>
    have run := Runs.seq (Runs.push S k true) (ih (Function.update S k (true :: S k)))
    have he : Function.update (Function.update S k (true :: S k)) k
        (unary n ++ (Function.update S k (true :: S k)) k) =
        Function.update S k (unary (n+1) ++ S k) := by
      simp only [Function.update_self, Function.update_idem, unary,
        List.replicate_add, List.replicate_one, List.append_assoc, List.singleton_append]
    rw [he] at run
    simpa [pushUnary, Nat.add_comm] using run

/-- Consume one unary operand and add it to another. -/
theorem addConsume_runs (S : Store K) (source target : K) (hne : source ≠ target)
    (m n : ℕ) (hm : S source = unary m) (hn : S target = unary n) :
    Runs (transfer source target) S (3*m+1)
      (Function.update (Function.update S source []) target (unary (m+n))) := by
  simpa only [hm, hn, unary_length, unary_reverse, ← unary_add] using
    transfer_runs S source target hne

/-- Add a unary operand while preserving it, restoring the empty temporary stack. -/
theorem addCopy_runs (S : Store K) (source target temp : K)
    (hst : source ≠ target) (hsu : source ≠ temp) (htu : target ≠ temp)
    (m n : ℕ) (hm : S source = unary m) (hn : S target = unary n)
    (hempty : S temp = []) :
    Runs (copy source target temp) S (7*m+2)
      (Function.update S target (unary (m+n))) := by
  simpa only [hm, hn, unary_length, ← unary_add] using
    copy_runs S source target temp hst hsu htu hempty

/-- Transfer arbitrary bits to a temporary stack and add one unary symbol to
another stack for each bit. -/
def countTransfer (source temp target : K) : Program K :=
  .while source Option.isSome (.pop source .skip
    (.seq (.push temp false) (.push target true))
    (.seq (.push temp true) (.push target true)))

theorem countTransfer_runs_aux (source temp target : K)
    (hst : source ≠ temp) (hso : source ≠ target) (hto : temp ≠ target) (xs : List Bool) :
    ∀ S : Store K, S source = xs →
      Runs (countTransfer source temp target) S (4*xs.length+1)
        (Function.update (Function.update (Function.update S source [])
          temp (xs.reverse ++ S temp)) target (unary xs.length ++ S target)) := by
  induction xs with
  | nil =>
    intro S hs
    have h0 : Function.update S source [] = S := by rw [← hs, Function.update_eq_self]
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add, List.reverse_nil,
      List.nil_append, unary, List.replicate_zero, h0, Function.update_eq_self]
    exact Runs.while_false (by simp [hs])
  | cons b xs ih =>
    intro S hs
    let S' := Function.update (Function.update (Function.update S source xs)
      temp (b :: S temp)) target (true :: S target)
    have hs' : S' source = xs := by simp [S', hst, hso]
    have ht' : S' temp = b :: S temp := by simp [S', hto]
    have ho' : S' target = true :: S target := by simp [S']
    have pushes : Runs (.seq (.push temp b) (.push target true))
        (Function.update S source xs) 2 S' := by
      have run := Runs.seq (Runs.push (Function.update S source xs) temp b)
        (Runs.push (Function.update (Function.update S source xs) temp
          (b :: (Function.update S source xs) temp)) target true)
      simpa [S', Ne.symm hst, Ne.symm hso, Ne.symm hto] using run
    have first : Runs (.pop source .skip
        (.seq (.push temp false) (.push target true))
        (.seq (.push temp true) (.push target true))) S 3 S' := by
      apply Runs.pop
      cases b <;> simpa [select, hs] using pushes
    have run := Runs.while_true (S := S) (test := Option.isSome)
      (by simp [hs]) first (ih S' hs')
    have he : Function.update (Function.update (Function.update S' source [])
          temp (xs.reverse ++ S' temp)) target (unary xs.length ++ S' target) =
        Function.update (Function.update (Function.update S source [])
          temp ((b :: xs).reverse ++ S temp)) target (unary (b :: xs).length ++ S target) := by
      funext k
      by_cases hk : k = target
      · subst k
        simp only [Function.update_self, ho', List.length_cons, unary, List.replicate_add,
          List.replicate_one, List.append_assoc, List.singleton_append]
      · by_cases hk' : k = temp
        · subst k
          simp [ht', hto, List.reverse_cons, List.append_assoc]
        · by_cases hk'' : k = source
          · subst k
            simp [S', hst, hso]
          · simp [S', Function.update_of_ne hk, Function.update_of_ne hk',
              Function.update_of_ne hk'']
    rw [he] at run
    convert run using 1 <;> simp [List.length_cons] <;> omega

theorem countTransfer_runs (S : Store K) (source temp target : K)
    (hst : source ≠ temp) (hso : source ≠ target) (hto : temp ≠ target) :
    Runs (countTransfer source temp target) S (4*(S source).length+1)
      (Function.update (Function.update (Function.update S source [])
        temp ((S source).reverse ++ S temp)) target (unary (S source).length ++ S target)) :=
  countTransfer_runs_aux source temp target hst hso hto (S source) S rfl

/-- Count arbitrary input bits without changing the input, using an empty
scratch stack and incrementing the destination in unary. -/
def countLength (source target temp : K) : Program K :=
  .seq (countTransfer source temp target) (transfer temp source)

theorem countLength_runs (S : Store K) (source target temp : K)
    (hso : source ≠ target) (hst : source ≠ temp) (hto : target ≠ temp)
    (hempty : S temp = []) :
    Runs (countLength source target temp) S (7*(S source).length+2)
      (Function.update S target (unary (S source).length ++ S target)) := by
  let S' := Function.update (Function.update (Function.update S source [])
    temp (S source).reverse) target (unary (S source).length ++ S target)
  have first : Runs (countTransfer source temp target) S (4*(S source).length+1) S' := by
    simpa [S', hempty] using countTransfer_runs S source temp target hst hso (Ne.symm hto)
  have rest := transfer_runs S' temp source (Ne.symm hst)
  have ht : S' temp = (S source).reverse := by simp [S', Ne.symm hto]
  have hs : S' source = [] := by simp [S', hst, hso]
  have he : Function.update (Function.update S' temp []) source
      ((S' temp).reverse ++ S' source) =
      Function.update S target (unary (S source).length ++ S target) := by
    funext k
    by_cases hk : k = source
    · subst k
      simp [ht, hs, hso]
    · by_cases hk' : k = temp
      · subst k
        simp [S', Ne.symm hst, Ne.symm hto, hempty]
      · by_cases hk'' : k = target
        · subst k
          simp [S', Ne.symm hso, hto]
        · simp [S', Function.update_of_ne hk, Function.update_of_ne hk',
            Function.update_of_ne hk'']
  rw [he, ht, List.length_reverse] at rest
  have run := Runs.seq first rest
  convert run using 1 <;> omega

/-- Consume a unary counter, copying a unary summand once per iteration. -/
def multiplyLoop (counter source target temp : K) : Program K :=
  .while counter Option.isSome (.seq (discard counter) (copy source target temp))

theorem multiplyLoop_runs (counter source target temp : K)
    (hcs : counter ≠ source) (hco : counter ≠ target) (hct : counter ≠ temp)
    (hso : source ≠ target) (hst : source ≠ temp) (hot : target ≠ temp)
    (m n : ℕ) : ∀ S : Store K,
    S counter = unary m → S source = unary n → S temp = [] →
    Runs (multiplyLoop counter source target temp) S (m*(7*n+4)+1)
      (Function.update (Function.update S counter []) target (unary (m*n) ++ S target)) := by
  induction m with
  | zero =>
    intro S hc hs ht
    have he : Function.update S counter [] = S := by simpa only [hc, unary, List.replicate_zero] using
      (show Function.update S counter (S counter) = S from Function.update_eq_self ..)
    simp only [Nat.zero_mul, Nat.zero_add, unary, List.replicate_zero,
      List.nil_append, he, Function.update_eq_self]
    exact Runs.while_false (by simp [hc, unary])
  | succ m ih =>
    intro S hc hs ht
    let S₁ := Function.update S counter (unary m)
    let S₂ := Function.update S₁ target (unary n ++ S target)
    have h₁ : Runs (discard counter) S 1 S₁ := by
      simpa [S₁, hc, unary, List.replicate_succ] using discard_runs S counter
    have h₂ : Runs (copy source target temp) S₁ (7*n+2) S₂ := by
      simpa [S₁, S₂, Ne.symm hcs, Ne.symm hco, Ne.symm hct, hs, ht] using
        copy_runs S₁ source target temp hso hst hot (by simp [S₁, Ne.symm hct, ht])
    have hcs₂ : S₂ counter = unary m := by simp [S₂, S₁, hco]
    have hss₂ : S₂ source = unary n := by simp [S₂, S₁, hso, Ne.symm hcs, hs]
    have hts₂ : S₂ temp = [] := by simp [S₂, S₁, Ne.symm hot, Ne.symm hct, ht]
    have rest := ih S₂ hcs₂ hss₂ hts₂
    have run := Runs.while_true (S := S) (test := Option.isSome)
      (by simp [hc, unary, List.replicate_succ]) (Runs.seq h₁ h₂) rest
    have he : Function.update (Function.update S₂ counter []) target
        (unary (m*n) ++ S₂ target) =
        Function.update (Function.update S counter []) target (unary ((m+1)*n) ++ S target) := by
      funext k
      by_cases hk : k = target
      · subst k
        simp [S₂, Nat.succ_mul, unary_add, List.append_assoc]
      · by_cases hk' : k = counter
        · subst k
          simp [hco]
        · simp [S₂, S₁, Function.update_of_ne hk, Function.update_of_ne hk']
    rw [he] at run
    convert run using 1 <;> simp [Nat.succ_mul] <;> omega

/-- Add the product of two unary registers to a destination, preserving the
factors and restoring both initially empty scratch registers. -/
def multiply (left right target counter temp : K) : Program K :=
  .seq (copy left counter temp) (multiplyLoop counter right target temp)

theorem multiply_runs (S : Store K) (left right target counter temp : K)
    (hlc : left ≠ counter) (hlt : left ≠ temp) (hct : counter ≠ temp)
    (hcr : counter ≠ right) (hco : counter ≠ target)
    (hro : right ≠ target) (hrt : right ≠ temp) (hot : target ≠ temp)
    (m n : ℕ) (hl : S left = unary m) (hr : S right = unary n)
    (hc : S counter = []) (ht : S temp = []) :
    Runs (multiply left right target counter temp) S (7*m*n+11*m+3)
      (Function.update S target (unary (m*n) ++ S target)) := by
  let S' := Function.update S counter (unary m)
  have first : Runs (copy left counter temp) S (7*m+2) S' := by
    simpa [S', hl, hc] using copy_runs S left counter temp hlc hlt hct ht
  have rest := multiplyLoop_runs counter right target temp hcr hco hct hro hrt hot
    m n S' (by simp [S']) (by simp [S', Ne.symm hcr, hr])
    (by simp [S', Ne.symm hct, ht])
  have he : Function.update (Function.update S' counter []) target
      (unary (m*n) ++ S' target) =
      Function.update S target (unary (m*n) ++ S target) := by
    have hreset : Function.update S' counter [] = S := by
      simp only [S', Function.update_idem]
      rw [← hc, Function.update_eq_self]
    rw [hreset]
    simp [S', Ne.symm hco]
  rw [he] at rest
  have run := Runs.seq first rest
  convert run using 1 <;> ring

/-- Exponentiation by a fixed compile-time exponent. Registers 0 and 1 are
base and output; registers 2, 3 and 4 are scratch space. -/
def fixedPower (reg : Fin 5 ↪ K) : ℕ → Program K
  | 0 => .push (reg 1) true
  | e+1 => .seq (fixedPower reg e)
      (.seq (multiply (reg 0) (reg 1) (reg 2) (reg 3) (reg 4))
        (.seq (clear (reg 1)) (transfer (reg 2) (reg 1))))

def powerSteps (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | e+1 => powerSteps n e + (7*n*n^e+11*n+3) + (2*n^e+1) + (3*(n*n^e)+1)

theorem fixedPower_runs (S : Store K) (reg : Fin 5 ↪ K) (n e : ℕ)
    (hbase : S (reg 0) = unary n)
    (houtput : S (reg 1) = []) (hwork : S (reg 2) = [])
    (hcounter : S (reg 3) = []) (htemp : S (reg 4) = []) :
    Runs (fixedPower reg e) S (powerSteps n e)
      (Function.update S (reg 1) (unary (n^e))) := by
  have hne {i j : Fin 5} (h : i ≠ j) : reg i ≠ reg j := fun he => h (reg.injective he)
  induction e with
  | zero => simpa [fixedPower, powerSteps, unary, houtput] using Runs.push S (reg 1) true
  | succ e ih =>
    let S₁ := Function.update S (reg 1) (unary (n^e))
    let S₂ := Function.update S₁ (reg 2) (unary (n*n^e))
    let S₃ := Function.update S₂ (reg 1) []
    have first : Runs (multiply (reg 0) (reg 1) (reg 2) (reg 3) (reg 4)) S₁
        (7*n*n^e+11*n+3) S₂ := by
      have run := multiply_runs S₁ (reg 0) (reg 1) (reg 2) (reg 3) (reg 4)
        (hne (by decide)) (hne (by decide)) (hne (by decide))
        (hne (by decide)) (hne (by decide)) (hne (by decide))
        (hne (by decide)) (hne (by decide)) n (n^e)
        (by simp [S₁, hne (by decide : (0 : Fin 5) ≠ 1), hbase])
        (by simp [S₁])
        (by simp [S₁, hne (by decide : (3 : Fin 5) ≠ 1), hcounter])
        (by simp [S₁, hne (by decide : (4 : Fin 5) ≠ 1), htemp])
      simpa [S₂, S₁, hne (by decide : (2 : Fin 5) ≠ 1), hwork] using run
    have second : Runs (clear (reg 1)) S₂ (2*n^e+1) S₃ := by
      simpa [S₃, S₂, S₁, hne (by decide : (1 : Fin 5) ≠ 2)] using clear_runs S₂ (reg 1)
    have third : Runs (transfer (reg 2) (reg 1)) S₃ (3*(n*n^e)+1)
        (Function.update S (reg 1) (unary (n^(e+1)))) := by
      have run := transfer_runs S₃ (reg 2) (reg 1) (hne (by decide))
      have hw : S₃ (reg 2) = unary (n*n^e) := by
        simp [S₃, S₂, hne (by decide : (2 : Fin 5) ≠ 1)]
      have ho : S₃ (reg 1) = [] := by simp [S₃]
      have he : Function.update (Function.update S₃ (reg 2) []) (reg 1)
          ((S₃ (reg 2)).reverse ++ S₃ (reg 1)) =
          Function.update S (reg 1) (unary (n^(e+1))) := by
        funext k
        by_cases hk : k = reg 1
        · subst k
          simp [hw, ho, Nat.pow_succ']
        · by_cases hk' : k = reg 2
          · subst k
            simp [hne (by decide : (2 : Fin 5) ≠ 1), hwork]
          · simp [S₃, S₂, S₁, Function.update_of_ne hk, Function.update_of_ne hk']
      rw [he, hw, unary_length] at run
      exact run
    have run := Runs.seq ih (Runs.seq first (Runs.seq second third))
    convert run using 1 <;> simp only [powerSteps] <;> omega

/-- For every fixed exponent, primitive running time is polynomial in the
unary input value. The program itself is independent of that input value. -/
theorem powerSteps_le (n e : ℕ) : powerSteps n e ≤ (28*e+1)*(n+1)^(e+1) := by
  induction e with
  | zero => simp [powerSteps]
  | succ e ih =>
    have hpos : 0 < n+1 := by omega
    have hp : n^e ≤ (n+1)^(e+1) :=
      (Nat.pow_le_pow_left (by omega : n ≤ n+1) e).trans
        (Nat.pow_le_pow_right hpos (by omega))
    have hmul : n*n^e ≤ (n+1)^(e+1) := by
      rw [← Nat.pow_succ']
      exact Nat.pow_le_pow_left (by omega) (e+1)
    have hn : n ≤ (n+1)^(e+1) :=
      (by omega : n ≤ n+1).trans (Nat.le_pow (by omega))
    have hone : 1 ≤ (n+1)^(e+1) := Nat.one_le_pow _ _ hpos
    have hs : powerSteps n (e+1) ≤ (28*(e+1)+1)*(n+1)^(e+1) := by
      simp only [powerSteps]
      nlinarith
    exact hs.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hpos (by omega)))

/-- Multiplication by a fixed compile-time constant uses that many copy
fragments; no run-time arithmetic is assumed by the instruction semantics. -/
def fixedScale (source target temp : K) : ℕ → Program K
  | 0 => .skip
  | c+1 => .seq (copy source target temp) (fixedScale source target temp c)

theorem fixedScale_runs (source target temp : K)
    (hst : source ≠ target) (hsu : source ≠ temp) (htu : target ≠ temp)
    (n c : ℕ) : ∀ S : Store K, S source = unary n → S temp = [] →
    Runs (fixedScale source target temp c) S (c*(7*n+2))
      (Function.update S target (unary (c*n) ++ S target)) := by
  induction c with
  | zero =>
    intro S hs ht
    simpa [fixedScale, unary] using Runs.skip S
  | succ c ih =>
    intro S hs ht
    let S' := Function.update S target (unary n ++ S target)
    have first : Runs (copy source target temp) S (7*n+2) S' := by
      simpa [S', hs] using copy_runs S source target temp hst hsu htu ht
    have rest := ih S' (by simp [S', hst, hs]) (by simp [S', Ne.symm htu, ht])
    have he : Function.update S' target (unary (c*n) ++ S' target) =
        Function.update S target (unary ((c+1)*n) ++ S target) := by
      simp [S', Function.update_idem, Nat.succ_mul, unary_add, List.append_assoc]
    rw [he] at rest
    have run := Runs.seq first rest
    convert run using 1 <;> ring

def dimensionPowerRegisters (reg : Fin 7 ↪ K) : Fin 5 ↪ K where
  toFun i := reg ⟨i.val+2, by omega⟩
  inj' := by
    intro i j h
    have hv := congrArg Fin.val (reg.injective h)
    apply Fin.ext
    dsimp at hv
    omega

/-- Compute c*(input length+1)^e+input length+3. All seven registers and the
constants c,e are fixed independently of the input. The original bit string
is preserved on register 0; register 2 receives the unary dimension. -/
def dimensionParameter (reg : Fin 7 ↪ K) (c e : ℕ) : Program K :=
  .seq (countLength (reg 0) (reg 1) (reg 6))
    (.seq (copy (reg 1) (reg 2) (reg 6))
      (.seq (.push (reg 2) true)
        (.seq (fixedPower (dimensionPowerRegisters reg) e)
          (.seq (fixedScale (reg 3) (reg 2) (reg 6) c) (pushUnary (reg 2) 2)))))

def dimensionSteps (n c e : ℕ) : ℕ :=
  (7*n+2)+(7*n+2)+1+powerSteps (n+1) e+c*(7*(n+1)^e+2)+2

theorem dimensionParameter_runs (S : Store K) (reg : Fin 7 ↪ K) (n c e : ℕ)
    (hn : (S (reg 0)).length = n)
    (hempty : ∀ i : Fin 7, i ≠ 0 → S (reg i) = []) :
    Runs (dimensionParameter reg c e) S (dimensionSteps n c e)
      (Function.update (Function.update (Function.update S (reg 1) (unary n))
        (reg 3) (unary ((n+1)^e))) (reg 2) (unary (c*(n+1)^e+n+3))) := by
  have hne {i j : Fin 7} (h : i ≠ j) : reg i ≠ reg j := fun he => h (reg.injective he)
  let S₁ := Function.update S (reg 1) (unary n)
  let S₂ := Function.update S₁ (reg 2) (unary n)
  let S₃ := Function.update S₂ (reg 2) (unary (n+1))
  let S₄ := Function.update S₃ (reg 3) (unary ((n+1)^e))
  let S₅ := Function.update S₄ (reg 2) (unary (c*(n+1)^e+(n+1)))
  have hcount : Runs (countLength (reg 0) (reg 1) (reg 6)) S (7*n+2) S₁ := by
    simpa [S₁, hn, hempty 1 (by decide)] using countLength_runs S (reg 0) (reg 1) (reg 6)
      (hne (by decide)) (hne (by decide)) (hne (by decide)) (hempty 6 (by decide))
  have hcopy : Runs (copy (reg 1) (reg 2) (reg 6)) S₁ (7*n+2) S₂ := by
    have run := copy_runs S₁ (reg 1) (reg 2) (reg 6)
      (hne (by decide)) (hne (by decide)) (hne (by decide))
      (by simp [S₁, hne (by decide : (6 : Fin 7) ≠ 1), hempty 6 (by decide)])
    simpa [S₂, S₁, hne (by decide : (2 : Fin 7) ≠ 1), hempty 2 (by decide)] using run
  have hpush : Runs (.push (reg 2) true) S₂ 1 S₃ := by
    simpa [S₃, S₂, unary, List.replicate_succ] using Runs.push S₂ (reg 2) true
  have hpow : Runs (fixedPower (dimensionPowerRegisters reg) e) S₃ (powerSteps (n+1) e) S₄ := by
    apply fixedPower_runs
    · change S₃ (reg 2) = unary (n+1)
      simp [S₃]
    · change S₃ (reg 3) = []
      simp [S₃, S₂, S₁, hne (by decide : (3 : Fin 7) ≠ 2),
        hne (by decide : (3 : Fin 7) ≠ 1), hempty 3 (by decide)]
    · change S₃ (reg 4) = []
      simp [S₃, S₂, S₁, hne (by decide : (4 : Fin 7) ≠ 2),
        hne (by decide : (4 : Fin 7) ≠ 1), hempty 4 (by decide)]
    · change S₃ (reg 5) = []
      simp [S₃, S₂, S₁, hne (by decide : (5 : Fin 7) ≠ 2),
        hne (by decide : (5 : Fin 7) ≠ 1), hempty 5 (by decide)]
    · change S₃ (reg 6) = []
      simp [S₃, S₂, S₁, hne (by decide : (6 : Fin 7) ≠ 2),
        hne (by decide : (6 : Fin 7) ≠ 1), hempty 6 (by decide)]
  have hscale : Runs (fixedScale (reg 3) (reg 2) (reg 6) c) S₄
      (c*(7*(n+1)^e+2)) S₅ := by
    have run := fixedScale_runs (reg 3) (reg 2) (reg 6)
      (hne (by decide)) (hne (by decide)) (hne (by decide)) ((n+1)^e) c S₄
      (by simp [S₄])
      (by simp [S₄, S₃, S₂, S₁, hne (by decide : (6 : Fin 7) ≠ 3),
        hne (by decide : (6 : Fin 7) ≠ 2), hne (by decide : (6 : Fin 7) ≠ 1),
        hempty 6 (by decide)])
    simpa [S₅, S₄, S₃, hne (by decide : (2 : Fin 7) ≠ 3), ← unary_add] using run
  have hfinish : Runs (pushUnary (reg 2) 2) S₅ 2
      (Function.update (Function.update (Function.update S (reg 1) (unary n))
        (reg 3) (unary ((n+1)^e))) (reg 2) (unary (c*(n+1)^e+n+3))) := by
    have run := pushUnary_runs (reg 2) 2 S₅
    have he : Function.update S₅ (reg 2) (unary 2 ++ S₅ (reg 2)) =
        Function.update (Function.update (Function.update S (reg 1) (unary n))
          (reg 3) (unary ((n+1)^e))) (reg 2) (unary (c*(n+1)^e+n+3)) := by
      funext k
      by_cases hk : k = reg 2
      · subst k
        simp only [Function.update_self, S₅, ← unary_add]
        congr 1
        omega
      · by_cases hk' : k = reg 3
        · subst k
          simp [S₅, S₄, hne (by decide : (3 : Fin 7) ≠ 2)]
        · simp [S₅, S₄, S₃, S₂, S₁, Function.update_of_ne hk, Function.update_of_ne hk']
    rwa [he] at run
  have run := Runs.seq hcount (Runs.seq hcopy (Runs.seq hpush
    (Runs.seq hpow (Runs.seq hscale hfinish))))
  convert run using 1 <;> simp only [dimensionSteps] <;> omega

theorem dimensionSteps_le (n c e : ℕ) :
    dimensionSteps n c e ≤ (28*e+9*c+22)*(n+2)^(e+1) := by
  have hpow := powerSteps_le (n+1) e
  have hpos : 0 < n+2 := by omega
  have hp : (n+1)^e ≤ (n+2)^(e+1) :=
    (Nat.pow_le_pow_left (by omega : n+1 ≤ n+2) e).trans
      (Nat.pow_le_pow_right hpos (by omega))
  have hn : n ≤ (n+2)^(e+1) :=
    (by omega : n ≤ n+2).trans (Nat.le_pow (by omega))
  have hone : 1 ≤ (n+2)^(e+1) := Nat.one_le_pow _ _ hpos
  have hscale : c*(7*(n+1)^e+2) ≤ 9*c*(n+2)^(e+1) := by nlinarith
  simp only [dimensionSteps]
  have hnorm : n+1+1 = n+2 := by omega
  rw [hnorm] at hpow
  nlinarith

end GroupWL.MachinePrograms.Structured
