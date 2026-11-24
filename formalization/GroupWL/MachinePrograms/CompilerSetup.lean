import GroupWL.MachinePrograms.UnaryArithmetic
import GroupWL.MachinePrograms.CompilerWiringCanonical

/-! Input orientation and polynomial address parameter for the actual compiler. -/
namespace GroupWL.MachinePrograms.Structured

abbrev CompilerRegister := Fin 24

def compilerDimensionRegisters : Fin 7 ↪ CompilerRegister := ⟨![1,2,3,4,5,6,7],by decide⟩
def compilerWiringRegisters : Fin 8 ↪ CompilerRegister := ⟨![3,0,5,6,7,8,9,10],by decide⟩
def compilerInitialRegisters : Fin 15 ↪ CompilerRegister :=
  ⟨![5,3,6,7,8,9,10,11,12,13,14,15,0,16,1],by decide⟩
def compilerBlankRegisters : Fin 19 ↪ CompilerRegister :=
  ⟨![5,6,0,7,8,9,10,3,11,4,12,13,14,15,16,17,18,19,20],by decide⟩
def compilerTestRegisters : Fin 4 ↪ CompilerRegister := ⟨![3,0,5,6],by decide⟩

def compilerStore (w : List Bool) (d : ℕ) : Store CompilerRegister :=
  Function.update (Function.update (Function.update (fun _ => []) 1 w) 2 (unary w.length)) 3 (unary d)

def CompilerReady (S : Store CompilerRegister) (w : List Bool) (d : ℕ) : Prop :=
  S 1 = w ∧ S 2 = unary w.length ∧ S 3 = unary d ∧
    ∀ i : CompilerRegister, i ≠ 0 → i ≠ 1 → i ≠ 2 → i ≠ 3 → S i = []

theorem compilerStore_ready (w : List Bool) (d : ℕ) : CompilerReady (compilerStore w d) w d := by
  refine ⟨by simp [compilerStore],by simp [compilerStore],by simp [compilerStore],?_⟩
  intro i h₀ h₁ h₂ h₃
  simp [compilerStore,h₁,h₂,h₃]

theorem CompilerReady.update_output {S : Store CompilerRegister} {w : List Bool} {d : ℕ}
    (hs : CompilerReady S w d) (out : List Bool) : CompilerReady (Function.update S 0 out) w d := by
  rcases hs with ⟨h₁,h₂,h₃,he⟩
  refine ⟨by simpa using h₁,by simpa using h₂,by simpa using h₃,?_⟩
  intro i h₀ h₁ h₂ h₃
  simpa [Function.update_of_ne h₀] using he i h₀ h₁ h₂ h₃

theorem CompilerReady.wiring {S : Store CompilerRegister} {w : List Bool} {d : ℕ}
    (hs : CompilerReady S w d) : WiringReady compilerWiringRegisters S d := by
  refine ⟨hs.2.2.1,?_⟩
  intro i hi
  fin_cases i <;> simp_all [compilerWiringRegisters,CompilerReady]

def compilerSetup (c e : ℕ) : Program CompilerRegister :=
  .seq (transfer 0 1) (.seq (dimensionParameter compilerDimensionRegisters c e) (clear 4))

def setupSteps (n c e : ℕ) := (3*n+1)+dimensionSteps n c e+(2*(n+1)^e+1)

theorem compilerSetup_runs (w : List Bool) (c e : ℕ) :
    Runs (compilerSetup c e) (Function.update (fun _ => []) 0 w.reverse) (setupSteps w.length c e)
      (compilerStore w (MachineCircuit.addressBits c e w.length)) := by
  let S : Store CompilerRegister := Function.update (fun _ => []) 0 w.reverse
  let A : Store CompilerRegister := Function.update (fun _ => []) 1 w
  have ht : Runs (transfer 0 1) S (3*w.length+1) A := by
    have h := transfer_runs S 0 1 (by decide)
    simpa [S,A,Function.update_comm (show (0 : CompilerRegister) ≠ 1 from by decide)] using h
  have hp := dimensionParameter_runs A compilerDimensionRegisters w.length c e
    (by simp [A,compilerDimensionRegisters])
    (by intro i hi; fin_cases i <;> simp_all [A,compilerDimensionRegisters])
  let B := Function.update (Function.update (Function.update A 2 (unary w.length))
    4 (unary ((w.length+1)^e))) 3 (unary (c*(w.length+1)^e+w.length+3))
  have hp' : Runs (dimensionParameter compilerDimensionRegisters c e) A (dimensionSteps w.length c e) B := by
    simpa only [B,compilerDimensionRegisters,Function.Embedding.trans_apply,Function.Embedding.coeFn_mk,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three] using hp
  have hc : Runs (clear 4) B (2*(w.length+1)^e+1)
      (compilerStore w (MachineCircuit.addressBits c e w.length)) := by
    have h := clear_runs B 4
    simp only [B,Function.update_of_ne (show (4 : CompilerRegister) ≠ 3 from by decide),
      Function.update_self,unary_length] at h
    convert h using 1
    funext i
    by_cases h₄ : i = 4
    · subst i; simp [compilerStore]
    · simp [B,A,compilerStore,Function.update_apply,h₄,MachineCircuit.addressBits,Nat.add_assoc]
  have hr := ht.seq (hp'.seq hc)
  simpa [compilerSetup,setupSteps,Nat.add_assoc] using hr

end GroupWL.MachinePrograms.Structured
