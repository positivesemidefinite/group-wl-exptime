import GroupWL.MachinePrograms.CompilerSetup
import GroupWL.MachinePrograms.CompilerBlankRequests

/-! Complete seed and test streams on the shared compiler register bank. -/
namespace GroupWL.MachinePrograms.Structured

open AddressedCircuit BinaryAddress CircuitDescription MachineCellular Complexity

def emitCompilerInitial (M : Machine) : Program CompilerRegister := emitInitialRequests compilerInitialRegisters M

theorem emitCompilerInitial_writes (S : Store CompilerRegister) (M : Machine)
    (w : BitString) (d : ℕ) (hs : CompilerReady S w d) :
    Writes 0 (emitCompilerInitial M) S (initialWords M d w)
      ((w.length+1)*(FiniteCode.size (CellularTableau.Gate (Cell M))+260*(w.length+d+1)^2)) := by
  apply emitInitialRequests_runs S compilerInitialRegisters M w d hs.1 hs.2.2.1
  intro i hi hj hk
  fin_cases i <;> simp_all [compilerInitialRegisters,CompilerReady]

def emitCompilerBlank (M : Machine) : Program CompilerRegister :=
  .seq (copy 2 4 5) (.seq (.push 4 true) (.seq (emitBlankRequests compilerBlankRegisters M) (clear 4)))

def compilerBlankBound (M : Machine) (n d : ℕ) :=
  (FiniteCode.size (CellularTableau.Gate (Cell M))+400)*(n+d+2)^2+9*n+6

theorem emitCompilerBlank_writes (S : Store CompilerRegister) (M : Machine)
    (w : BitString) (d : ℕ) (hs : CompilerReady S w d) :
    Writes 0 (emitCompilerBlank M) S (blankWords M (ofNat d (w.length+1)))
      (compilerBlankBound M w.length d) := by
  have h₄ : S 4 = [] := hs.2.2.2 4 (by decide) (by decide) (by decide) (by decide)
  have h₅ : S 5 = [] := hs.2.2.2 5 (by decide) (by decide) (by decide) (by decide)
  let A := Function.update S 4 (unary w.length)
  let B := Function.update S 4 (unary (w.length+1))
  have hcopy : Runs (copy 2 4 5) S (7*w.length+2) A := by
    simpa [A,hs.2.1,h₄,unary_length] using copy_runs S 2 4 5 (by decide) (by decide) (by decide) h₅
  have hpush : Runs (.push 4 true) A 1 B := by
    simpa [A,B,unary,List.replicate_succ] using Runs.push A 4 true
  have hd : B (compilerBlankRegisters 7) = unary d := by simp [B,compilerBlankRegisters,hs.2.2.1]
  have hn : B (compilerBlankRegisters 9) = unary (w.length+1) := by simp [B,compilerBlankRegisters]
  have he : ∀ i : Fin 19, i ≠ 9 → i ≠ 7 → i ≠ 2 → B (compilerBlankRegisters i) = [] := by
    intro i hi hj hk
    fin_cases i <;> simp_all [B,compilerBlankRegisters,CompilerReady]
  obtain ⟨t,ht,hblank⟩ := emitBlankRequests_runs B compilerBlankRegisters M (w.length+1) d hn hd he
  let C := Function.update B 0 ((blankWords M (ofNat d (w.length+1))).reverse++S 0)
  have hblank' : Runs (emitBlankRequests compilerBlankRegisters M) B t C := by
    simpa [C,B,compilerBlankRegisters] using hblank
  have hclear : Runs (clear 4) C (2*(w.length+1)+1)
      (Function.update S 0 ((blankWords M (ofNat d (w.length+1))).reverse++S 0)) := by
    have h := clear_runs C 4
    simp only [C,B,Function.update_of_ne (show (4 : CompilerRegister) ≠ 0 from by decide),
      Function.update_self,unary_length] at h
    convert h using 1
    funext i
    by_cases h₀ : i = 0
    · subst i; simp
    · by_cases hi : i = 4
      · subst i; simp [h₄]
      · simp [Function.update_apply,h₀,hi]
  refine ⟨(7*w.length+2)+(1+(t+(2*(w.length+1)+1))),?_,hcopy.seq (hpush.seq (hblank'.seq hclear))⟩
  dsimp [compilerBlankBound]
  have hsum : w.length+1+d+1 = w.length+d+2 := by omega
  rw [hsum] at ht
  omega

def emitCompilerSeeds (M : Machine) : Program CompilerRegister :=
  .seq (emitCompilerInitial M) (emitCompilerBlank M)

def compilerSeedBound (M : Machine) (n d : ℕ) :=
  (n+1)*(FiniteCode.size (CellularTableau.Gate (Cell M))+260*(n+d+1)^2)+compilerBlankBound M n d

theorem emitCompilerSeeds_writes (S : Store CompilerRegister) (M : Machine)
    (w : BitString) (d : ℕ) (hs : CompilerReady S w d) :
    Writes 0 (emitCompilerSeeds M) S
      (initialWords M d w++blankWords M (ofNat d (w.length+1))) (compilerSeedBound M w.length d) :=
  (emitCompilerInitial_writes S M w d hs).seq
    (emitCompilerBlank_writes _ M w d (hs.update_output _))

theorem emitCompilerTests_writes (S : Store CompilerRegister) (M : Machine)
    (w : BitString) (d : ℕ) (hs : CompilerReady S w d) :
    Writes 0 (emitTestRequests compilerTestRegisters M) S
      (arrayWord requestWord (MachineCircuit.compile M w d).test)
      (FiniteCode.size (Symbol M.workSymbols)*(FiniteCode.size (CellularTableau.Gate (Cell M))+22*d+6)) := by
  apply emitTestRequests_runs S compilerTestRegisters M d hs.2.2.1
  · exact hs.2.2.2 5 (by decide) (by decide) (by decide) (by decide)
  · exact hs.2.2.2 6 (by decide) (by decide) (by decide) (by decide)

end GroupWL.MachinePrograms.Structured
