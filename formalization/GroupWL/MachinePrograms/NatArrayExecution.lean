import GroupWL.MachinePrograms.NatArrayCompiler
import GroupWL.MachinePrograms.NatArrayIO

/-! Executing complete natural-array programs on physical bit strings.
The compiler includes the input scan and, for functions, the output scan. -/
namespace GroupWL.MachinePrograms.NatArrayLowering

open NatArrayLanguage Complexity

variable {Reg Arr : Type*} [DecidableEq Reg] [DecidableEq Arr]
  [Fintype Reg] [Fintype Arr]

def decisionProgram (p : NatArrayLanguage.Program Reg Arr) (input : Arr) :
    Structured.Program (StackIndex Reg Arr) :=
  .seq (importBits (scratchSlot 15) (arraySlot input)) (compileProgram p)

def functionProgram (p : NatArrayLanguage.Program Reg Arr) (input output : Arr) :
    Structured.Program (StackIndex Reg Arr) :=
  .seq (decisionProgram p input) (exportBits (arraySlot output) (scratchSlot 14))

noncomputable def functionMachine (p : NatArrayLanguage.Program Reg Arr) (input output : Arr) :
    Complexity.Machine :=
  Stacks.compiled (Structured.compile (functionProgram p input output) true)
    (scratchSlot 15) (scratchSlot 14)

theorem decisionProgram_runs {p : NatArrayLanguage.Program Reg Arr} {input : Arr}
    {w : BitString} {B t : ℕ} {S : Store Reg Arr}
    (h : Runs B p (inputStore input w) t S) :
    ∃ u ≤ 4*w.length+1+10000*(B+1)^4*t,
      Structured.Runs (decisionProgram p input)
        (Function.update (fun _ => []) (scratchSlot 15) w.reverse) u (encodeStore S) := by
  obtain ⟨u,hu,hr⟩ := compileProgram_runs h
  refine ⟨(3*w.length+w.count true+1)+u, ?_,
    .seq (importInput_runs input w) hr⟩
  have hc := bitScan_cost w
  omega

theorem functionProgram_runs {p : NatArrayLanguage.Program Reg Arr} {input output : Arr}
    {w value : BitString} {B t : ℕ} {S : Store Reg Arr}
    (h : Runs B p (inputStore input w) t S) (ho : S.array output = value.map bitNat) :
    ∃ T u, u ≤ 4*w.length+2+10000*(B+1)^4*t+4*B ∧
      Structured.Runs (functionProgram p input output)
        (Function.update (fun _ => []) (scratchSlot 15) w.reverse) u T ∧
      (T (scratchSlot 14)).reverse = value := by
  obtain ⟨u,hu,hr⟩ := decisionProgram_runs h
  obtain ⟨T,ht,hv⟩ := exportOutput_runs output S value ho
  refine ⟨T,u+(3*value.length+value.count true+1),?_,.seq hr ht,hv⟩
  have hc := bitScan_cost value
  have hvlen : value.length ≤ B := by
    simpa only [ho,List.length_map] using (Store.array_length_le_size S output).trans h.end_bound
  omega

end GroupWL.MachinePrograms.NatArrayLowering
