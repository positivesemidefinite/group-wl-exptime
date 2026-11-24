import GroupWL.MachinePrograms.CompilerBounds
import GroupWL.MachinePrograms.CompilerHeader
import GroupWL.MachinePrograms.CompilerRequestWords
import GroupWL.MachinePrograms.StructuredComplexity

/-! The complete finite-control compiler, including the actual one-tape
polynomial-time theorem for the canonical compact circuit description. -/
namespace GroupWL.MachinePrograms.Structured

open AddressedCircuit CellularTableau CircuitDescription MachineCellular Complexity

def compilerHeaderRegisters : Fin 6 ↪ CompilerRegister := ⟨![2,3,0,4,5,6],by decide⟩

def compilerEmission (M : Machine) : Program CompilerRegister :=
  .seq (emitHeader compilerHeaderRegisters M)
    (.seq (emitWiring compilerWiringRegisters (rule M))
      (.seq (emitCompilerSeeds M) (emitTestRequests compilerTestRegisters M)))

def compilerWiringCoefficient (M : Machine) : ℕ :=
  (FiniteCode.size (Cell M))^3*(16*FiniteCode.size (Gate (Cell M))+600)

def compilerEmissionSteps (M : Machine) (n d : ℕ) : ℕ :=
  headerSteps M n d+(compilerWiringCoefficient M*(d+1)^3+
    (compilerSeedBound M n d+
      FiniteCode.size (Symbol M.workSymbols)*(FiniteCode.size (Gate (Cell M))+22*d+6)))

theorem compilerEmission_writes (S : Store CompilerRegister) (M : Machine)
    (w : BitString) (d : ℕ) (hd : 0 < d) (hw : w.length+1 < 2^d)
    (hs : CompilerReady S w d) :
    Writes 0 (compilerEmission M) S (circuitWord (MachineCircuit.compile M w d))
      (compilerEmissionSteps M w.length d) := by
  have header (V : Store CompilerRegister) (hv : CompilerReady V w d) :=
    emitHeader_runs V compilerHeaderRegisters M w.length d hv.2.1 hv.2.2.1
      (hv.2.2.2 4 (by decide) (by decide) (by decide) (by decide))
      (hv.2.2.2 5 (by decide) (by decide) (by decide) (by decide))
      (hv.2.2.2 6 (by decide) (by decide) (by decide) (by decide))
  have wiring (V : Store CompilerRegister) (hv : CompilerReady V w d) :=
    emitWiring_canonical V compilerWiringRegisters (rule M)
      (MachineCircuit.seeds M w d) (MachineCircuit.tests M d) hd hv.wiring
  have seeds (V : Store CompilerRegister) (hv : CompilerReady V w d) :
      Writes 0 (emitCompilerSeeds M) V (arrayWord requestWord (MachineCircuit.compile M w d).seed)
        (compilerSeedBound M w.length d) := by
    simpa only [seedWords_canonical M w d hw] using emitCompilerSeeds_writes V M w d hv
  let V₁ := Function.update S 0 ((headerWord M w.length d).reverse++S 0)
  let V₂ := Function.update V₁ 0
    ((arrayWord schemaWord (MachineCircuit.compile M w d).schema).reverse++V₁ 0)
  let V₃ := Function.update V₂ 0
    ((arrayWord requestWord (MachineCircuit.compile M w d).seed).reverse++V₂ 0)
  have h₁ : CompilerReady V₁ w d := hs.update_output _
  have h₂ : CompilerReady V₂ w d := h₁.update_output _
  have h₃ : CompilerReady V₃ w d := h₂.update_output _
  have result := (header S hs).seq ((wiring V₁ h₁).seq
    ((seeds V₂ h₂).seq (emitCompilerTests_writes V₃ M w d h₃)))
  simpa only [compilerEmission,compilerEmissionSteps,compilerWiringCoefficient,
    circuitWord,headerWord_canonical,List.append_assoc] using result

def compilerEmissionCoefficient (M : Machine) : ℕ :=
  headerConstant M+compilerWiringCoefficient M+(2*FiniteCode.size (Gate (Cell M))+700)+
    FiniteCode.size (Symbol M.workSymbols)*(FiniteCode.size (Gate (Cell M))+28)

theorem compilerEmissionSteps_le (M : Machine) (n d : ℕ) :
    compilerEmissionSteps M n d ≤ compilerEmissionCoefficient M*(n+d+2)^3 := by
  let B := n+d+2
  have hB : 1 ≤ B := by dsimp [B]; omega
  have h23 : B^2 ≤ B^3 := Nat.pow_le_pow_right (by omega) (by decide)
  have hh : headerSteps M n d ≤ headerConstant M*B^3 :=
    (headerSteps_le M n d).trans (Nat.mul_le_mul_left _
      ((Nat.pow_le_pow_left (by dsimp [B]; omega : n+d+1 ≤ B) 2).trans h23))
  have hw : compilerWiringCoefficient M*(d+1)^3 ≤ compilerWiringCoefficient M*B^3 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [B]; omega : d+1 ≤ B) 3)
  have hs := compilerSeedBound_le M n d
  have ht := compilerTestBound_le M n d
  change compilerEmissionSteps M n d ≤ compilerEmissionCoefficient M*B^3
  dsimp [compilerEmissionSteps,compilerEmissionCoefficient]
  dsimp [B] at hh hw ⊢
  nlinarith

def compilerProgram (M : Machine) (c e : ℕ) : Program CompilerRegister :=
  .seq (compilerSetup c e) (compilerEmission M)

def compilerCoefficient (M : Machine) (c e : ℕ) : ℕ :=
  setupCoefficient c e+compilerEmissionCoefficient M*(c+6)^3

theorem compilerTotalSteps_le (M : Machine) (n c e : ℕ) :
    setupSteps n c e+compilerEmissionSteps M n (MachineCircuit.addressBits c e n) ≤
      compilerCoefficient M c e*(n+1)^(3*(e+1)) := by
  let P := (n+1)^(e+1)
  have hP : 1 ≤ P := Nat.one_le_pow _ _ (by omega)
  have hP3 : P ≤ P^3 := Nat.le_self_pow (by decide) _
  have hsetup : setupSteps n c e ≤ setupCoefficient c e*P^3 :=
    (setupSteps_le n c e).trans (Nat.mul_le_mul_left _ hP3)
  have hemission : compilerEmissionSteps M n (MachineCircuit.addressBits c e n) ≤
      compilerEmissionCoefficient M*(c+6)^3*P^3 := by
    calc
      _ ≤ compilerEmissionCoefficient M*(n+MachineCircuit.addressBits c e n+2)^3 :=
        compilerEmissionSteps_le M n _
      _ ≤ compilerEmissionCoefficient M*((c+6)*P)^3 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (compilerBudget_le n c e) 3)
      _ = _ := by rw [Nat.mul_pow,Nat.mul_assoc]
  have he : (n+1)^(3*(e+1)) = P^3 := by
    dsimp [P]
    rw [← pow_mul,Nat.mul_comm (e+1) 3]
  rw [he]
  dsimp [compilerCoefficient]
  nlinarith

theorem compilerProgram_runs (M : Machine) (c e : ℕ) (w : BitString) :
    ∃ time ≤ compilerCoefficient M c e*(w.length+1)^(3*(e+1)),
      Runs (compilerProgram M c e) (Function.update (fun _ => []) 0 w.reverse) time
        (Function.update (compilerStore w (MachineCircuit.addressBits c e w.length)) 0
          (machineWord M c e w).reverse) := by
  let d := MachineCircuit.addressBits c e w.length
  have setup := compilerSetup_runs w c e
  obtain ⟨t,ht,hem⟩ := compilerEmission_writes (compilerStore w d) M w d
    (MachineCircuit.addressBits_pos c e w.length) (compilerInput_lt w.length c e)
    (compilerStore_ready w d)
  refine ⟨setupSteps w.length c e+t,?_,?_⟩
  · exact (Nat.add_le_add_left ht _).trans (compilerTotalSteps_le M w.length c e)
  · simpa [compilerProgram,compilerStore,machineWord,d] using setup.seq hem

/-- The actual one-tape machine implementing the entire canonical compiler. -/
noncomputable def compilerMachine (M : Machine) (c e : ℕ) : Machine :=
  Stacks.compiled (compile (compilerProgram M c e) true) 0 0

theorem compilerMachine_computesBy (M : Machine) (c e : ℕ) :
    ComputesBy (compilerMachine M c e) (machineWord M c e)
      (fun n => (10*(compilerCoefficient M c e+2)^2)*(n+1)^(2*(3*(e+1)+1))) := by
  apply computesBy_polynomial (compilerProgram M c e) 0 0 (machineWord M c e)
    (compilerCoefficient M c e) (3*(e+1))
  intro w
  obtain ⟨t,ht,hr⟩ := compilerProgram_runs M c e w
  refine ⟨_,t,ht,hr,?_⟩
  simp

end GroupWL.MachinePrograms.Structured
