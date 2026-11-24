import GroupWL.MachinePrograms.BinaryEncoding
import GroupWL.DimensionEncoding

/-! A fixed program emits the canonical variable-width dimension word.
Its unary input is consumed; binary emission uses the verified division routine. -/
namespace GroupWL.MachinePrograms.DimensionSerialization

open Structured
variable {K : Type*} [DecidableEq K]

def step (reg : Fin 12 ↪ K) : Structured.Program K :=
  .seq (.push (reg 10) true) (binaryBody reg)
def loop (reg : Fin 12 ↪ K) : Structured.Program K := .while (reg 3) Option.isSome (step reg)

theorem bits_step (n : ℕ) (hn : 0<n) :
    n.bits=decide (n%2=1)::(n/2).bits := by
  have h := Nat.mod_add_div n 2
  have hm := Nat.mod_lt n (by decide : 0<2)
  by_cases he : n%2=0
  · have hq : n/2≠0 := by omega
    have hd : n=2*(n/2) := by omega
    conv_lhs => rw [hd,Nat.bit0_bits _ hq]
    simp [he]
  · have he' : n%2=1 := by omega
    have hd : n=2*(n/2)+1 := by omega
    conv_lhs => rw [hd,Nat.bit1_bits]
    simp [he']

theorem step_runs (S : Store K) (reg : Fin 12 ↪ K) (n : ℕ)
    (hn : S (reg 3)=unary n) (htwo : S (reg 4)=unary 2)
    (hempty : ∀i : Fin 12,5 ≤ i.val → i.val≤10 → S (reg i)=[]) :
    ∃t≤71*(n+1),Runs (step reg) S t
      (Function.update (Function.update S (reg 3) (unary (n/2))) (reg 2)
        (decide (n%2=1)::S (reg 2))) := by
  let T := Function.update S (reg 10) [true]
  have hp : Runs (.push (reg 10) true) S 1 T := by
    simpa [T,hempty 10 (by decide) (by decide)] using Runs.push S (reg 10) true
  obtain ⟨t,ht,hr⟩ := binaryBody_runs T reg n 0
    (by simp [T,reg.apply_eq_iff_eq,hn]) (by simp [T,unary])
    (by simp [T,reg.apply_eq_iff_eq,htwo]) (by
      intro i hi hj
      have hne : i≠(10 : Fin 12) := by intro he; subst i; norm_num at hj
      simp [T,reg.apply_eq_iff_eq,hne,hempty i hi (by omega)])
  have he : Function.update (Function.update (Function.update T (reg 3) (unary (n/2)))
      (reg 10) (unary 0)) (reg 2) (decide (n%2=1)::T (reg 2)) =
      Function.update (Function.update S (reg 3) (unary (n/2))) (reg 2)
        (decide (n%2=1)::S (reg 2)) := by
    funext k
    by_cases h2 : k=reg 2
    · subst k; simp [T,reg.apply_eq_iff_eq]
    · by_cases h3 : k=reg 3
      · subst k; simp [T,reg.apply_eq_iff_eq]
      · by_cases h10 : k=reg 10
        · subst k; simp [T,reg.apply_eq_iff_eq,unary,hempty 10 (by decide) (by decide)]
        · simp [T,Function.update_of_ne h2,Function.update_of_ne h3,Function.update_of_ne h10]
  rw [he] at hr
  exact ⟨1+t,by omega,.seq hp hr⟩

theorem loop_runs (reg : Fin 12 ↪ K) (n : ℕ) : ∀S : Store K,
    S (reg 3)=unary n → S (reg 4)=unary 2 →
    (∀i : Fin 12,5 ≤ i.val → i.val≤10 → S (reg i)=[]) →
    ∃t≤100*(n+1)^2,Runs (loop reg) S t
      (Function.update (Function.update S (reg 3) []) (reg 2) (n.bits.reverse++S (reg 2))) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S hn htwo hempty
    by_cases hz : n=0
    · subst n
      have he : Function.update (Function.update S (reg 3) []) (reg 2)
          ((Nat.bits 0).reverse ++ S (reg 2))=S := by
        have hn' : S (reg 3)=[] := hn
        simp only [Nat.zero_bits,List.reverse_nil,List.nil_append]
        rw [show Function.update S (reg 3) [] = S by rw [←hn',Function.update_eq_self], Function.update_eq_self]
      rw [he]
      exact ⟨1,by decide,.while_false (by simp [hn,unary])⟩
    · have hpos : 0<n := Nat.pos_of_ne_zero hz
      have hq : n/2<n := Nat.div_lt_self hpos (by decide)
      let T := Function.update (Function.update S (reg 3) (unary (n/2))) (reg 2)
        (decide (n%2=1)::S (reg 2))
      obtain ⟨u,hu,first⟩ := step_runs S reg n hn htwo hempty
      change Runs (step reg) S u T at first
      have hn' : T (reg 3)=unary (n/2) := by simp [T,reg.apply_eq_iff_eq]
      have ht' : T (reg 4)=unary 2 := by simp [T,reg.apply_eq_iff_eq,htwo]
      have hempty' : ∀i : Fin 12,5 ≤ i.val → i.val≤10 → T (reg i)=[] := by
        intro i hi hj
        have h2 : i≠(2 : Fin 12) := by intro he; subst i; norm_num at hi
        have h3 : i≠(3 : Fin 12) := by intro he; subst i; norm_num at hi
        simp [T,reg.apply_eq_iff_eq,h2,h3,hempty i hi hj]
      obtain ⟨t,ht,rest⟩ := ih (n/2) hq T hn' ht' hempty'
      have he : Function.update (Function.update T (reg 3) []) (reg 2)
          ((n/2).bits.reverse++T (reg 2)) =
          Function.update (Function.update S (reg 3) []) (reg 2) (n.bits.reverse++S (reg 2)) := by
        funext k
        by_cases h2 : k=reg 2
        · subst k; simp [T,bits_step n hpos,List.reverse_cons,List.append_assoc]
        · by_cases h3 : k=reg 3
          · subst k; simp [T,reg.apply_eq_iff_eq]
          · simp [T,Function.update_of_ne h2,Function.update_of_ne h3]
      rw [he] at rest
      refine ⟨u+t+1,?_,.while_true (by simp [hn,unary,hz]) first rest⟩
      have hs : (n/2+1)^2≤n^2 := Nat.pow_le_pow_left (by omega) 2
      nlinarith

def binaryProgram (reg : Fin 12 ↪ K) : Structured.Program K :=
  .seq (pushUnary (reg 4) 2) (.seq (loop reg)
    (.seq (clear (reg 4)) (transfer (reg 2) (reg 0))))

def program (e : Statement.DimensionEncoding) (reg : Fin 12 ↪ K) : Structured.Program K :=
  match e with
  | .unary => transfer (reg 3) (reg 0)
  | .binary => binaryProgram reg

theorem program_runs (e : Statement.DimensionEncoding) (reg : Fin 12 ↪ K) (S : Store K) (n : ℕ)
    (hn : S (reg 3)=unary n)
    (hempty : ∀i : Fin 12,i=2 ∨ (4 ≤ i.val ∧ i.val≤10) → S (reg i)=[]) :
    ∃t≤110*(n+1)^2,∃U,Runs (program e reg) S t U ∧
      U (reg 0)=(Statement.dimensionWord e n).reverse++S (reg 0) := by
  cases e with
  | unary =>
    have h := transfer_runs S (reg 3) (reg 0) (reg.injective.ne (by decide))
    refine ⟨3*n+1,by nlinarith,Function.update (Function.update S (reg 3) []) (reg 0) ((S (reg 3)).reverse ++ S (reg 0)),?_,?_⟩
    · simpa [program,hn,unary] using h
    · simp [Statement.dimensionWord,hn,unary]
  | binary =>
    let A := Function.update S (reg 4) (unary 2)
    let B := Function.update (Function.update A (reg 3) []) (reg 2) n.bits.reverse
    let C := Function.update B (reg 4) []
    have h4 : S (reg 4)=[] := hempty 4 (by decide)
    have h2 : S (reg 2)=[] := hempty 2 (by decide)
    have hp : Runs (pushUnary (reg 4) 2) S 2 A := by
      simpa [A,h4,unary] using pushUnary_runs (reg 4) 2 S
    obtain ⟨t,ht,hr⟩ := loop_runs reg n A
      (by simp [A,reg.apply_eq_iff_eq,hn]) (by simp [A]) (by
        intro i hi hj
        have hne : i≠(4 : Fin 12) := by intro he; subst i; norm_num at hi
        simp [A,reg.apply_eq_iff_eq,hne,hempty i (Or.inr ⟨by omega,hj⟩)])
    have hr' : Runs (loop reg) A t B := by
      simpa [B,A,reg.apply_eq_iff_eq,h2] using hr
    have hc : Runs (clear (reg 4)) B 5 C := by
      simpa [C,B,A,reg.apply_eq_iff_eq,unary] using clear_runs B (reg 4)
    have hd := transfer_runs C (reg 2) (reg 0) (reg.injective.ne (by decide))
    have hc2 : C (reg 2)=n.bits.reverse := by simp [C,B,reg.apply_eq_iff_eq]
    have hc0 : C (reg 0)=S (reg 0) := by simp [C,B,A,reg.apply_eq_iff_eq]
    have hlen := Statement.bits_length_le n
    refine ⟨2+(t+(5+(3*n.bits.length+1))),by nlinarith,Function.update (Function.update C (reg 2) []) (reg 0) ((C (reg 2)).reverse ++ C (reg 0)),?_,?_⟩
    · exact .seq hp (.seq hr' (.seq hc (by simpa [hc2] using hd)))
    · simp [hc2,hc0,Statement.dimensionWord]

end GroupWL.MachinePrograms.DimensionSerialization
