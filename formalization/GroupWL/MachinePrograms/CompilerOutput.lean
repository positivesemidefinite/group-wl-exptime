import GroupWL.MachinePrograms.StackLibrary
import GroupWL.CircuitDescription

/-! Counted output routines for the compact circuit description. -/
namespace GroupWL.MachinePrograms.Structured

variable {K : Type*} [DecidableEq K]

/-- Emit a compile-time word to a reversed output stack. -/
def emitFixed (output : K) : List Bool → Program K
  | [] => .skip
  | b::bs => .seq (.push output b) (emitFixed output bs)

theorem emitFixed_runs (S : Store K) (output : K) (word : List Bool) :
    Runs (emitFixed output word) S word.length
      (Function.update S output (word.reverse++S output)) := by
  induction word generalizing S with
  | nil => simpa [emitFixed] using Runs.skip S
  | cons b bs ih =>
    have hr := Runs.seq (Runs.push S output b) (ih (Function.update S output (b::S output)))
    simpa [emitFixed,List.reverse_cons,List.append_assoc,Function.update_idem,Nat.add_comm] using hr

def repeatWord (word : List Bool) (n : ℕ) : List Bool := (List.replicate n word).flatten

@[simp] theorem repeatWord_zero (word : List Bool) : repeatWord word 0 = [] := rfl
@[simp] theorem repeatWord_succ (word : List Bool) (n : ℕ) :
    repeatWord word (n+1) = word++repeatWord word n := by simp [repeatWord,List.replicate_succ]

def repeatEmitLoop (counter output : K) (word : List Bool) : Program K :=
  .while counter Option.isSome (.seq (discard counter) (emitFixed output word))

theorem repeatEmitLoop_runs (counter output : K) (hne : counter ≠ output)
    (word : List Bool) (n : ℕ) :
    ∀ S : Store K, S counter = List.replicate n true →
      Runs (repeatEmitLoop counter output word) S (n*(word.length+2)+1)
        (Function.update (Function.update S counter []) output
          ((repeatWord word n).reverse++S output)) := by
  induction n with
  | zero =>
    intro S hc
    have hc₀ : S counter = [] := hc
    have hreset : Function.update S counter [] = S := by
      rw [← hc₀,Function.update_eq_self]
    have he : Function.update (Function.update S counter []) output ([]++S output) = S := by
      rw [hreset,List.nil_append,Function.update_eq_self]
    simp only [repeatWord_zero,List.reverse_nil,he,Nat.zero_mul,Nat.zero_add]
    exact Runs.while_false (by simp [hc])
  | succ n ih =>
    intro S hc
    let S₀ := Function.update S counter (List.replicate n true)
    let S₁ := Function.update S₀ output (word.reverse++S output)
    have first : Runs (.seq (discard counter) (emitFixed output word)) S (1+word.length) S₁ := by
      apply Runs.seq (t := 1) (u := word.length)
      · simpa [S₀,hc,List.replicate_succ] using discard_runs S counter
      · simpa [S₁,S₀,Ne.symm hne] using emitFixed_runs S₀ output word
    have rest := ih S₁ (by simp [S₁,S₀,hne])
    have hr := Runs.while_true (test := Option.isSome) (by simp [hc,List.replicate_succ]) first rest
    have he : Function.update (Function.update S₁ counter []) output
        ((repeatWord word n).reverse++S₁ output) =
        Function.update (Function.update S counter []) output
          ((repeatWord word (n+1)).reverse++S output) := by
      funext k
      by_cases hk : k = output
      · subst k
        simp [S₁,repeatWord_succ,List.reverse_append,List.append_assoc]
      · by_cases hk' : k = counter
        · subst k
          simp [hne]
        · simp [S₁,S₀,Function.update_of_ne hk,Function.update_of_ne hk']
    rw [he] at hr
    convert hr using 1
    simp only [Nat.succ_mul]
    omega

/-- Registers are the preserved unary count, reversed output, loop counter,
and scratch. The program is independent of the runtime count. -/
def repeatEmit (reg : Fin 4 ↪ K) (word : List Bool) : Program K :=
  .seq (copy (reg 0) (reg 2) (reg 3)) (repeatEmitLoop (reg 2) (reg 1) word)

theorem repeatEmit_runs (S : Store K) (reg : Fin 4 ↪ K) (word : List Bool) (n : ℕ)
    (hn : S (reg 0) = List.replicate n true)
    (hc : S (reg 2) = []) (ht : S (reg 3) = []) :
    Runs (repeatEmit reg word) S (n*(word.length+9)+3)
      (Function.update S (reg 1) ((repeatWord word n).reverse++S (reg 1))) := by
  have hne {i j : Fin 4} (h : i ≠ j) : reg i ≠ reg j := fun he => h (reg.injective he)
  have heq (i j : Fin 4) : reg i = reg j ↔ i = j := reg.injective.eq_iff
  let S' := Function.update S (reg 2) (List.replicate n true)
  have first : Runs (copy (reg 0) (reg 2) (reg 3)) S (7*n+2) S' := by
    simpa [S',hn,hc] using copy_runs S (reg 0) (reg 2) (reg 3)
      (hne (by decide)) (hne (by decide)) (hne (by decide)) ht
  have rest := repeatEmitLoop_runs (reg 2) (reg 1) (hne (by decide)) word n S'
    (by simp [S'])
  have hreset : Function.update S' (reg 2) [] = S := by
    simp only [S',Function.update_idem]
    rw [← hc,Function.update_eq_self]
  rw [hreset] at rest
  have hr := Runs.seq first rest
  have hout : S' (reg 1) = S (reg 1) := by simp [S',heq]
  rw [hout] at hr
  convert hr using 1
  ring

def emitUnary (source output temp : K) : Program K :=
  .seq (copy source output temp) (.push output false)

theorem emitUnary_runs (S : Store K) (source output temp : K)
    (hso : source ≠ output) (hst : source ≠ temp) (hot : output ≠ temp)
    (n : ℕ) (hn : S source = List.replicate n true) (ht : S temp = []) :
    Runs (emitUnary source output temp) S (7*n+3)
      (Function.update S output ((CircuitDescription.natWord n).reverse++S output)) := by
  have first := copy_runs S source output temp hso hst hot ht
  have last := Runs.push (Function.update S output (S source++S output)) output false
  have hr := Runs.seq first last
  simpa [emitUnary,hn,CircuitDescription.natWord,List.reverse_append,
    Function.update_idem,List.append_assoc,Nat.add_assoc] using hr

/-- An output fragment with an exact store effect and a primitive time bound. -/
def Writes (output : K) (p : Program K) (S : Store K) (word : List Bool) (bound : ℕ) : Prop :=
  ∃ time ≤ bound, Runs p S time (Function.update S output (word.reverse++S output))

theorem Writes.seq {output : K} {p q : Program K} {S : Store K}
    {a b : List Bool} {A B : ℕ} (hp : Writes output p S a A)
    (hq : Writes output q (Function.update S output (a.reverse++S output)) b B) :
    Writes output (.seq p q) S (a++b) (A+B) := by
  obtain ⟨t,ht,hp⟩ := hp
  obtain ⟨u,hu,hq⟩ := hq
  refine ⟨t+u,Nat.add_le_add ht hu,?_⟩
  simpa only [Function.update_self,Function.update_idem,List.reverse_append,List.append_assoc] using
    Runs.seq hp hq

theorem Writes.mono {output : K} {p : Program K} {S : Store K}
    {word : List Bool} {A B : ℕ} (h : Writes output p S word A) (hle : A ≤ B) :
    Writes output p S word B := by
  obtain ⟨t,ht,hr⟩ := h
  exact ⟨t,ht.trans hle,hr⟩

theorem emitFixed_writes (S : Store K) (output : K) (word : List Bool) :
    Writes output (emitFixed output word) S word word.length :=
  ⟨word.length,le_rfl,emitFixed_runs S output word⟩

end GroupWL.MachinePrograms.Structured
