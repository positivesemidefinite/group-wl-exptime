import GroupWL.MachinePrograms.NatArrayEncoding
import GroupWL.DenseParsing

/-! The actual dense tensor serializer is a fixed Boolean-stack program.
Materialized coefficients are already represented by their unary array word. -/
namespace GroupWL.MachinePrograms.TensorSerialization

open Structured Statement

variable {K : Type*} [DecidableEq K]

def program (n m coefficients output : K) : Structured.Program K :=
  .seq (transfer n output) (.seq (.push output false)
    (.seq (transfer m output) (.seq (.push output false) (transfer coefficients output))))

theorem program_runs (n m coefficients output : K)
    (hnm : n ≠ m) (hnc : n ≠ coefficients) (hno : n ≠ output)
    (hmc : m ≠ coefficients) (hmo : m ≠ output) (hco : coefficients ≠ output)
    (S : Structured.Store K) (a b : ℕ) (w : List Bool)
    (hn : S n = List.replicate a true) (hm : S m = List.replicate b true)
    (hc : S coefficients = w) :
    Structured.Runs (program n m coefficients output) S (3*(a+b+w.length)+5)
      (Function.update (Function.update (Function.update (Function.update S n []) m []) coefficients [])
        output ((Statement.unary a ++ Statement.unary b ++ w).reverse ++ S output)) := by
  let S₁ := Function.update (Function.update S n []) output ((S n).reverse ++ S output)
  let S₂ := Function.update S₁ output (false :: S₁ output)
  let S₃ := Function.update (Function.update S₂ m []) output ((S₂ m).reverse ++ S₂ output)
  let S₄ := Function.update S₃ output (false :: S₃ output)
  let S₅ := Function.update (Function.update S₄ coefficients []) output
    ((S₄ coefficients).reverse ++ S₄ output)
  have h₁ : Structured.Runs (transfer n output) S (3*a+1) S₁ := by
    simpa only [S₁,hn,List.length_replicate] using transfer_runs S n output hno
  have h₂ : Structured.Runs (.push output false) S₁ 1 S₂ := .push _ _ _
  have hm₂ : S₂ m = List.replicate b true := by simp [S₂,S₁,Ne.symm hnm,hmo,hm]
  have h₃ : Structured.Runs (transfer m output) S₂ (3*b+1) S₃ := by
    simpa only [S₃,hm₂,List.length_replicate] using transfer_runs S₂ m output hmo
  have h₄ : Structured.Runs (.push output false) S₃ 1 S₄ := .push _ _ _
  have hc₄ : S₄ coefficients = w := by
    simp [S₄,S₃,S₂,S₁,hco,Ne.symm hnc,Ne.symm hmc,hc]
  have h₅ : Structured.Runs (transfer coefficients output) S₄ (3*w.length+1) S₅ := by
    simpa only [S₅,hc₄] using transfer_runs S₄ coefficients output hco
  have he : S₅ = Function.update
      (Function.update (Function.update (Function.update S n []) m []) coefficients [])
      output ((Statement.unary a ++ Statement.unary b ++ w).reverse ++ S output) := by
    funext k
    by_cases ho : k=output
    · subst k
      simp only [S₅,Function.update_self,hc₄]
      simp only [S₄,Function.update_self,S₃,Function.update_self,hm₂,
        S₂,Function.update_self,S₁,Function.update_self,hn]
      simp [Statement.unary,List.reverse_append,List.append_assoc,hmo,Ne.symm hnm,hm]
    · by_cases hn' : k=n
      · subst k; simp [S₅,S₄,S₃,S₂,S₁,ho,hnm,hnc]
      · by_cases hm' : k=m
        · subst k; simp [S₅,S₄,S₃,S₂,S₁,ho,hmc]
        · by_cases hc' : k=coefficients
          · subst k; simp [S₅,ho]
          · simp [S₅,S₄,S₃,S₂,S₁,ho,hn',hm',hc']
  rw [← he]
  convert Structured.Runs.seq h₁ (Structured.Runs.seq h₂
    (Structured.Runs.seq h₃ (Structured.Runs.seq h₄ h₅))) using 1 <;> omega

/-- The list of field representatives in precisely the parser's order. -/
def coefficientList {p n m : ℕ} (c : Fin n → Fin n → Fin m → ZMod p) : List ℕ :=
  (List.ofFn (fun i => (List.ofFn (fun j => List.ofFn (fun z => (c i j z).val))).flatten)).flatten

theorem arrayWord_ofFn {n : ℕ} (f : Fin n → ℕ) :
    Structured.arrayWord (List.ofFn f) = Statement.arrayWord Statement.unary f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ,Structured.arrayWord_cons,ih]
    simp [Statement.arrayWord,List.ofFn_succ,Statement.unary,List.append_assoc]

theorem arrayWord_flatten (xs : List (List ℕ)) :
    Structured.arrayWord xs.flatten = (xs.map Structured.arrayWord).flatten := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Structured.arrayWord_append,ih]

theorem coefficientList_word (p : ℕ) [Fact p.Prime] {n m : ℕ}
    (c : Fin n → Fin n → Fin m → ZMod p) :
    Structured.arrayWord (coefficientList c) = coefficientsWord p c := by
  simp [coefficientList,arrayWord_flatten,List.map_ofFn,Function.comp_def,
    arrayWord_ofFn,Statement.arrayWord,coefficientsWord]

section Encoded
variable {Reg Arr : Type*} [DecidableEq Reg] [DecidableEq Arr]
open NatArrayLowering

def encodedProgram (n m : Reg) (coefficients : Arr) :
    Structured.Program (StackIndex Reg Arr) :=
  program (scalarSlot n) (scalarSlot m) (arraySlot coefficients) (scratchSlot 0)

theorem encoded_program_runs (p : ℕ) [Fact p.Prime] (n m : Reg) (coefficients : Arr)
    (hnm : n ≠ m) (S : NatArrayLanguage.Store Reg Arr) (T : TensorDescription p)
    (hn : S.scalar n = T.inputDimension) (hm : S.scalar m = T.outputDimension)
    (hc : S.array coefficients = coefficientList (T.coefficient p)) :
    ∃ t≤3*(T.denseWord p).length+5, ∃ U,
      Structured.Runs (encodedProgram n m coefficients) (encodeStore S) t U ∧
        (U (scratchSlot 0)).reverse = T.denseWord p := by
  have hnc : scalarSlot n ≠ arraySlot coefficients := by simp [scalarSlot,arraySlot]
  have hno : (scalarSlot n : StackIndex Reg Arr) ≠ scratchSlot (0 : Fin 16) := by simp [scalarSlot,scratchSlot]
  have hmc : scalarSlot m ≠ arraySlot coefficients := by simp [scalarSlot,arraySlot]
  have hmo : (scalarSlot m : StackIndex Reg Arr) ≠ scratchSlot (0 : Fin 16) := by simp [scalarSlot,scratchSlot]
  have hco : (arraySlot coefficients : StackIndex Reg Arr) ≠ scratchSlot (0 : Fin 16) := by simp [arraySlot,scratchSlot]
  have hn' : encodeStore S (scalarSlot n) = List.replicate T.inputDimension true := by simp [hn]
  have hm' : encodeStore S (scalarSlot m) = List.replicate T.outputDimension true := by simp [hm]
  have hc' : encodeStore S (arraySlot coefficients) = coefficientsWord p (T.coefficient p) := by
    rw [encodeStore_array,hc,coefficientList_word]
  have h := program_runs (scalarSlot n) (scalarSlot m) (arraySlot coefficients) (scratchSlot 0)
    (by simpa [scalarSlot] using hnm) hnc hno hmc hmo hco (encodeStore S)
    T.inputDimension T.outputDimension (coefficientsWord p (T.coefficient p)) hn' hm' hc'
  refine ⟨_,?_,_,h,?_⟩
  · simp only [denseWord_eq_coefficients,List.length_append,Statement.unary,
      List.length_replicate,List.length_singleton]
    omega
  · simp only [Function.update_self,encodeStore_scratch,List.append_nil,List.reverse_reverse]
    exact (denseWord_eq_coefficients p T).symm

end Encoded
end GroupWL.MachinePrograms.TensorSerialization
