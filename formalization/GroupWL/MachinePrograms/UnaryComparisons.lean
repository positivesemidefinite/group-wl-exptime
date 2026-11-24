import GroupWL.MachinePrograms.UnaryArithmetic

/-! Unary comparisons by fixed Boolean-stack programs. No arithmetic test is
used as an instruction: the programs inspect only stack tops. -/
namespace GroupWL.MachinePrograms.Structured

variable {K : Type*} [DecidableEq K]

/-- Cancel the left operand against the right. Left underflow on the right
is counted in the third stack, allowing all three comparisons afterward. -/
def cancelUnary (left right excess : K) : Program K :=
  .while left Option.isSome
    (.seq (discard left) (.pop right (.push excess true) .skip .skip))

theorem cancelUnary_runs (left right excess : K)
    (hlr : left ≠ right) (hle : left ≠ excess) (hre : right ≠ excess)
    (m n z : ℕ) (S : Store K)
    (hm : S left = unary m) (hn : S right = unary n) (hz : S excess = unary z) :
    Runs (cancelUnary left right excess) S (3*m+(m-n)+1)
      (Function.update (Function.update (Function.update S left [])
        right (unary (n-m))) excess (unary (z+(m-n)))) := by
  induction m generalizing n z S with
  | zero =>
      have he : Function.update (Function.update (Function.update S left [])
          right (unary n)) excess (unary z) = S := by
        have hm0 : S left = [] := by simpa [unary] using hm
        rw [← hm0,Function.update_eq_self,← hn,Function.update_eq_self,
          ← hz,Function.update_eq_self]
      simpa only [Nat.mul_zero,Nat.zero_sub,Nat.zero_add,Nat.sub_zero,Nat.add_zero,he] using
        (Runs.while_false (k := left) (test := Option.isSome)
          (body := .seq (discard left) (.pop right (.push excess true) .skip .skip))
          (by simp [hm,unary]) : Runs (cancelUnary left right excess) S 1 S)
  | succ m ih =>
      have hd : Runs (discard left) S 1 (Function.update S left (unary m)) := by
        simpa [hm,unary] using discard_runs S left
      cases n with
      | zero =>
          let S' := Function.update (Function.update (Function.update S left (unary m))
            right []) excess (unary (z+1))
          have hp : Runs (.pop right (.push excess true) .skip .skip)
              (Function.update S left (unary m)) 2 S' := by
            apply Runs.pop
            simpa [select,hn,Ne.symm hlr,Ne.symm hle,Ne.symm hre,hz,unary,
              List.replicate_succ,S'] using
              (Runs.push (Function.update (Function.update S left (unary m)) right []) excess true)
          have rest := ih 0 (z+1) S' (by simp [S',hlr,hle])
            (by simp [S',hre,unary]) (by simp [S'])
          have run := Runs.while_true (S := S) (test := Option.isSome)
            (by simp [hm,unary]) (Runs.seq hd hp) rest
          have he : Function.update (Function.update (Function.update S' left [])
              right (unary (0-m))) excess (unary (z+1+(m-0))) =
              Function.update (Function.update (Function.update S left [])
              right (unary (0-(m+1)))) excess (unary (z+((m+1)-0))) := by
            funext k
            by_cases hk : k=excess
            · subst k
              simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
            · by_cases hk' : k=right
              · subst k
                simp [hre]
              · by_cases hk'' : k=left
                · subst k
                  simp [hlr,hle]
                · simp [S',Function.update_of_ne hk,Function.update_of_ne hk',
                    Function.update_of_ne hk'']
          rw [he] at run
          convert run using 1 <;> simp only [Nat.sub_zero] <;> omega
      | succ n =>
          let S' := Function.update (Function.update S left (unary m)) right (unary n)
          have hp : Runs (.pop right (.push excess true) .skip .skip)
              (Function.update S left (unary m)) 1 S' := by
            apply Runs.pop
            simpa [select,hn,Ne.symm hlr,unary,S'] using (Runs.skip S')
          have rest := ih n z S' (by simp [S',hlr]) (by simp [S'])
            (by simp [S',Ne.symm hle,Ne.symm hre,hz])
          have run := Runs.while_true (S := S) (test := Option.isSome)
            (by simp [hm,unary]) (Runs.seq hd hp) rest
          have he : Function.update (Function.update (Function.update S' left [])
              right (unary (n-m))) excess (unary (z+(m-n))) =
              Function.update (Function.update (Function.update S left [])
              right (unary ((n+1)-(m+1)))) excess (unary (z+((m+1)-(n+1)))) := by
            funext k
            by_cases hk : k=excess
            · subst k
              simp
            · by_cases hk' : k=right
              · subst k
                simp [hre]
              · by_cases hk'' : k=left
                · subst k
                  simp [hlr,hle]
                · simp [S',Function.update_of_ne hk,Function.update_of_ne hk',
                    Function.update_of_ne hk'']
          rw [he] at run
          convert run using 1 <;> simp only [Nat.add_sub_add_right] <;> omega

def writeBool (result : K) (b : Bool) : Program K := .seq (clear result) (.push result b)

theorem writeBool_runs (S : Store K) (result : K) (b : Bool) :
    Runs (writeBool result b) S (2*(S result).length+2) (Function.update S result [b]) := by
  have h := Runs.seq (clear_runs S result) (Runs.push (Function.update S result []) result b)
  simpa [writeBool,Function.update_idem,Nat.add_assoc] using h

def ifEmpty (k : K) (yes no : Program K) : Program K := .peek k yes no no

theorem ifEmpty_runs {S S' : Store K} {k : K} {yes no : Program K} {t : ℕ}
    (h : Runs (if S k = [] then yes else no) S t S') :
    Runs (ifEmpty k yes no) S (t+1) S' := by
  apply Runs.peek
  cases hs : S k with
  | nil => simpa [select,hs] using h
  | cons b xs => cases b <;> simpa [select,hs] using h

inductive UnaryComparison where
  | lt | le | eq
  deriving DecidableEq, Fintype

def UnaryComparison.result : UnaryComparison → ℕ → ℕ → Bool
  | .lt,m,n => decide (m<n)
  | .le,m,n => decide (m≤n)
  | .eq,m,n => decide (m=n)

def chooseResidual (mode : UnaryComparison) (right excess : K) : Program K :=
  match mode with
  | .lt => ifEmpty right (writeBool excess false) (writeBool excess true)
  | .le => ifEmpty excess (writeBool excess true) (writeBool excess false)
  | .eq => ifEmpty excess
      (ifEmpty right (writeBool excess true) (writeBool excess false)) (writeBool excess false)

theorem chooseResidual_runs (mode : UnaryComparison) (right excess : K)
    (m n : ℕ) (S : Store K) (hr : S right = unary (n-m))
    (he : S excess = unary (m-n)) :
    ∃ t ≤ 2*(m-n)+4, Runs (chooseResidual mode right excess) S t
      (Function.update S excess [mode.result m n]) := by
  have hw (b : Bool) : Runs (writeBool excess b) S (2*(m-n)+2)
      (Function.update S excess [b]) := by simpa [he] using writeBool_runs S excess b
  cases mode with
  | lt =>
      refine ⟨2*(m-n)+3,by omega,?_⟩
      apply ifEmpty_runs
      by_cases h : m<n
      · have hn : n-m ≠ 0 := by omega
        simpa [UnaryComparison.result,h,hr,unary,hn] using hw true
      · have hn : n-m = 0 := by omega
        simpa [UnaryComparison.result,h,hr,unary,hn] using hw false
  | le =>
      refine ⟨2*(m-n)+3,by omega,?_⟩
      apply ifEmpty_runs
      by_cases h : m≤n
      · have hn : m-n = 0 := by omega
        simpa [UnaryComparison.result,h,he,unary,hn] using hw true
      · have hn : m-n ≠ 0 := by omega
        simpa [UnaryComparison.result,h,he,unary,hn] using hw false
  | eq =>
      by_cases h : m≤n
      · have hn : m-n = 0 := by omega
        refine ⟨2*(m-n)+4,by omega,?_⟩
        apply ifEmpty_runs
        simp only [he,hn,unary,List.replicate_zero,if_pos rfl]
        apply ifEmpty_runs
        by_cases hmn : m=n
        · subst n
          simpa [UnaryComparison.result,hr,unary] using hw true
        · have hpos : n-m ≠ 0 := by omega
          simpa [UnaryComparison.result,hmn,hr,unary,hpos,hn] using hw false
      · have hn : m-n ≠ 0 := by omega
        have hmn : m≠n := by omega
        refine ⟨2*(m-n)+3,by omega,?_⟩
        apply ifEmpty_runs
        simpa [UnaryComparison.result,hmn,he,unary,hn] using hw false

/-- Destructive comparison clears both operands and leaves one Boolean. -/
def compareConsume (mode : UnaryComparison) (left right result : K) : Program K :=
  .seq (cancelUnary left right result) (.seq (chooseResidual mode right result) (clear right))

theorem compareConsume_runs (mode : UnaryComparison) (left right result : K)
    (hlr : left ≠ right) (hlo : left ≠ result) (hro : right ≠ result)
    (m n : ℕ) (S : Store K) (hm : S left = unary m) (hn : S right = unary n)
    (ho : S result = []) :
    ∃ t ≤ 8*(m+n+1), Runs (compareConsume mode left right result) S t
      (Function.update (Function.update (Function.update S left []) right [])
        result [mode.result m n]) := by
  let S₁ := Function.update (Function.update (Function.update S left [])
    right (unary (n-m))) result (unary (m-n))
  have hc : Runs (cancelUnary left right result) S (3*m+(m-n)+1) S₁ := by
    simpa [S₁] using cancelUnary_runs left right result hlr hlo hro m n 0 S hm hn ho
  obtain ⟨t,ht,hchoice⟩ := chooseResidual_runs mode right result m n S₁
    (by simp [S₁,hro]) (by simp [S₁])
  have hclear := clear_runs (Function.update S₁ result [mode.result m n]) right
  have hr : (Function.update S₁ result [mode.result m n]) right = unary (n-m) := by
    simp [S₁,hro]
  rw [hr,unary_length] at hclear
  have run := Runs.seq hc (Runs.seq hchoice hclear)
  have he : Function.update (Function.update S₁ result [mode.result m n]) right [] =
      Function.update (Function.update (Function.update S left []) right []) result
        [mode.result m n] := by
    funext k
    by_cases hk : k=result
    · subst k
      simp [Ne.symm hro]
    · by_cases hk' : k=right
      · subst k
        simp [hro]
      · simp [S₁,Function.update_of_ne hk,Function.update_of_ne hk']
  rw [he] at run
  refine ⟨3*m+(m-n)+1+(t+(2*(n-m)+1)),?_,run⟩
  omega

/-- Registers 0 and 1 are preserved operands; register 2 receives the result;
registers 3, 4 and 5 are initially empty scratch stacks, restored on exit. -/
def compareUnary (mode : UnaryComparison) (slot : Fin 6 ↪ K) : Program K :=
  .seq (copy (slot 0) (slot 3) (slot 5))
    (.seq (copy (slot 1) (slot 4) (slot 5))
      (compareConsume mode (slot 3) (slot 4) (slot 2)))

/-- Each of equality, strict comparison and weak comparison preserves both
unary inputs and costs at most a fixed linear number of stack operations. -/
theorem compareUnary_runs (mode : UnaryComparison) (slot : Fin 6 ↪ K)
    (m n : ℕ) (S : Store K) (hm : S (slot 0) = unary m) (hn : S (slot 1) = unary n)
    (ho : S (slot 2) = []) (hx : S (slot 3) = []) (hy : S (slot 4) = [])
    (ht : S (slot 5) = []) :
    ∃ t ≤ 16*(m+n+1), Runs (compareUnary mode slot) S t
      (Function.update S (slot 2) [mode.result m n]) := by
  have ne (i j : Fin 6) (h : i≠j) : slot i ≠ slot j := fun he => h (slot.injective he)
  let S₁ := Function.update S (slot 3) (unary m)
  have first : Runs (copy (slot 0) (slot 3) (slot 5)) S (7*m+2) S₁ := by
    simpa [S₁,hm,hx] using copy_runs S (slot 0) (slot 3) (slot 5)
      (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide)) ht
  let S₂ := Function.update S₁ (slot 4) (unary n)
  have second : Runs (copy (slot 1) (slot 4) (slot 5)) S₁ (7*n+2) S₂ := by
    have h1 : S₁ (slot 1) = unary n := by simp [S₁,slot.injective.eq_iff,hn]
    have h4 : S₁ (slot 4) = [] := by simp [S₁,slot.injective.eq_iff,hy]
    have h5 : S₁ (slot 5) = [] := by simp [S₁,slot.injective.eq_iff,ht]
    simpa [S₂,h1,h4] using copy_runs S₁ (slot 1) (slot 4) (slot 5)
      (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide)) h5
  obtain ⟨t,htime,last⟩ := compareConsume_runs mode (slot 3) (slot 4) (slot 2)
    (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide)) m n S₂
    (by simp [S₂,S₁,slot.injective.eq_iff]) (by simp [S₂])
    (by simp [S₂,S₁,slot.injective.eq_iff,ho])
  have run := Runs.seq first (Runs.seq second last)
  have he : Function.update (Function.update (Function.update S₂ (slot 3) []) (slot 4) [])
      (slot 2) [mode.result m n] = Function.update S (slot 2) [mode.result m n] := by
    funext k
    by_cases hk : k=slot 2
    · subst k
      simp
    · by_cases hk' : k=slot 4
      · subst k
        simp [slot.injective.eq_iff,hy]
      · by_cases hk'' : k=slot 3
        · subst k
          simp [slot.injective.eq_iff,hx]
        · simp [S₂,S₁,Function.update_of_ne hk,Function.update_of_ne hk',
            Function.update_of_ne hk'']
  rw [he] at run
  exact ⟨7*m+2+(7*n+2+t),by omega,run⟩

end GroupWL.MachinePrograms.Structured
