import GroupWL.MachinePrograms.NatArrayProofs

/-! Syntactic frame rules: scratch effects are computed from the finite
program syntax, so clients only prove the changing loop invariants. -/
namespace GroupWL.MachinePrograms.NatArrayLanguage
variable {Reg Arr : Type*} [DecidableEq Reg] [DecidableEq Arr] [Fintype Reg] [Fintype Arr]

def Atom.scalarWrites : Atom Reg Arr → Finset Reg
  | .const r _ | .copy r _ | .binary _ r _ _ | .arrayLength r _ | .read r _ _ => {r}
  | .divmod q r _ _ => {q,r}
  | _ => ∅

def Atom.arrayWrites : Atom Reg Arr → Finset Arr
  | .write a _ _ | .allocate a _ _ | .copyArray a _ | .clearArray a => {a}
  | _ => ∅

def Program.scalarWrites : Program Reg Arr → Finset Reg
  | .skip => ∅
  | .atom a => a.scalarWrites
  | .seq p q | .branch _ p q => p.scalarWrites ∪ q.scalarWrites
  | .while _ p => p.scalarWrites

def Program.arrayWrites : Program Reg Arr → Finset Arr
  | .skip => ∅
  | .atom a => a.arrayWrites
  | .seq p q | .branch _ p q => p.arrayWrites ∪ q.arrayWrites
  | .while _ p => p.arrayWrites

theorem Atom.scalar_eq_of_not_mem (a : Atom Reg Arr) (S : Store Reg Arr) (r : Reg)
    (h : r∉a.scalarWrites) : (a.apply S).scalar r=S.scalar r := by
  cases a <;> simp_all [Atom.scalarWrites,Atom.apply,Store.setScalar,Store.setArray]

theorem Atom.array_eq_of_not_mem (a : Atom Reg Arr) (S : Store Reg Arr) (r : Arr)
    (h : r∉a.arrayWrites) : (a.apply S).array r=S.array r := by
  cases a <;> simp_all [Atom.arrayWrites,Atom.apply,Store.setScalar,Store.setArray]

theorem Runs.scalar_eq_of_not_mem {B p S T t}
    (h : Runs (Reg:=Reg) (Arr:=Arr) B p S t T) (r : Reg) (hr : r∉p.scalarWrites) :
    T.scalar r=S.scalar r := by
  induction h with
  | skip _ => rfl
  | atom _ _ _ => exact Atom.scalar_eq_of_not_mem _ _ r hr
  | seq _ _ ihp ihq =>
      simp only [Program.scalarWrites,Finset.mem_union,not_or] at hr
      exact (ihq hr.2).trans (ihp hr.1)
  | branch_nonzero _ _ ih =>
      simp only [Program.scalarWrites,Finset.mem_union,not_or] at hr
      exact ih hr.1
  | branch_zero _ _ ih =>
      simp only [Program.scalarWrites,Finset.mem_union,not_or] at hr
      exact ih hr.2
  | while_zero _ _ => rfl
  | while_nonzero _ _ _ ihp ihr => exact (ihr hr).trans (ihp hr)

theorem Runs.array_eq_of_not_mem {B p S T t}
    (h : Runs (Reg:=Reg) (Arr:=Arr) B p S t T) (r : Arr) (hr : r∉p.arrayWrites) :
    T.array r=S.array r := by
  induction h with
  | skip _ => rfl
  | atom _ _ _ => exact Atom.array_eq_of_not_mem _ _ r hr
  | seq _ _ ihp ihq =>
      simp only [Program.arrayWrites,Finset.mem_union,not_or] at hr
      exact (ihq hr.2).trans (ihp hr.1)
  | branch_nonzero _ _ ih =>
      simp only [Program.arrayWrites,Finset.mem_union,not_or] at hr
      exact ih hr.1
  | branch_zero _ _ ih =>
      simp only [Program.arrayWrites,Finset.mem_union,not_or] at hr
      exact ih hr.2
  | while_zero _ _ => rfl
  | while_nonzero _ _ _ ihp ihr => exact (ihr hr).trans (ihp hr)

end GroupWL.MachinePrograms.NatArrayLanguage

