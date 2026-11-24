import GroupWL.MachinePrograms.NatArrayScalar
import GroupWL.MachinePrograms.NatArrayArrays
import GroupWL.MachinePrograms.NatArrayCleanup
import GroupWL.MachinePrograms.NatArrayLowering

/-! The complete concrete implementation of every natural-array instruction.
All primitive implementations are finite Boolean-stack programs. -/
namespace GroupWL.MachinePrograms.NatArrayLowering

open NatArrayLanguage

variable {Reg Arr : Type*} [DecidableEq Reg] [DecidableEq Arr]
  [Fintype Reg] [Fintype Arr]

def concreteAtom : (a : Atom Reg Arr) → AtomCode a
  | .const r n => (constBody r n).toAtomCode
  | .copy r s => (copyBody r s).toAtomCode
  | .binary op r a b => (binaryBody op r a b).toAtomCode
  | .arrayLength r a => (arrayLengthCode r a).toAtomCode
  | .read r a i => (readCode r a i).toAtomCode
  | .write a i v => (writeCode a i v).toAtomCode
  | .allocate a n v => (allocateCode a n v).toAtomCode
  | .copyArray a b => (copyArrayCode a b).toAtomCode
  | .clearArray a => (clearArrayCode a).toAtomCode
  | .divmod q r a b => (divmodBody q r a b).toAtomCode

def compileProgram (p : NatArrayLanguage.Program Reg Arr) : Structured.Program (StackIndex Reg Arr) :=
  lower concreteAtom p

theorem compileProgram_runs {B : ℕ} {p : NatArrayLanguage.Program Reg Arr} {S T : Store Reg Arr} {t : ℕ}
    (h : Runs B p S t T) :
    ∃ u ≤ 10000*(B+1)^4*t,
      Structured.Runs (compileProgram p) (encodeStore S) u (encodeStore T) :=
  lower_runs concreteAtom h

end GroupWL.MachinePrograms.NatArrayLowering
