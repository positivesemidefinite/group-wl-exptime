import GroupWL.MachinePrograms.ArrayMaterialization
import GroupWL.MachinePrograms.NatArrayFrames

/-! Candidate flags, owners, and coordinate numbers for gates of dimension one or two. -/
namespace GroupWL.MachinePrograms.GateCandidates
open NatArrayLanguage
set_option maxHeartbeats 2000000
inductive Reg where
  | length | index | todo | one | zero | two | gate | port | kind | flag | value
  deriving DecidableEq,Fintype
inductive Arr where | kinds | output
  deriving DecidableEq,Fintype
inductive Field where | flag | owner | port deriving DecidableEq,Fintype
abbrev State := Store Reg Arr
abbrev Code := NatArrayLanguage.Program Reg Arr

def result : Field → Reg | .flag=>.flag | .owner=>.gate | .port=>.port
def value (kinds : List ℕ) (i : ℕ) : Field → ℕ
  | .flag => 1-i%2+i%2*kinds[i/2]?.getD 0
  | .owner => i/2
  | .port => i%2

def registers : Fin 5 ↪ Reg := ⟨![.length,.index,.todo,.one,.zero],by decide⟩
def cellAtoms : List (Atom Reg Arr) := [
  .divmod .gate .port .index .two,.read .kind .kinds .gate,
  .const .flag 1,.binary .sub .flag .flag .port,.binary .mul .value .port .kind,
  .binary .add .flag .flag .value]
def cell : Code := atoms cellAtoms
def program (f : Field) : Code := materialize registers .output (result f) cell

structure Inputs (kinds : List ℕ) (S : State) : Prop where
  input : S.array .kinds=kinds
  two : S.scalar .two=2

theorem cell_runs (kinds : List ℕ) (S : State) (M i : ℕ)
    (bounded : S.Bounded M) (input : Inputs kinds S) (binary : ∀x∈kinds,x≤1)
    (index : S.scalar .index=i) (valid : i<2*kinds.length) :
    Runs (storageBound Reg Arr M) cell S 6 (applyAtoms cellAtoms S) ∧
      (applyAtoms cellAtoms S).Bounded M ∧
      ∀f,(applyAtoms cellAtoms S).scalar (result f)=value kinds i f := by
  have hi : i/2<kinds.length := (Nat.div_lt_iff_lt_mul (by decide)).2 (by simpa [Nat.mul_comm] using valid)
  have hp : i%2≤1 := by have := Nat.mod_lt i (by decide : 0<2); omega
  have hk : kinds[i/2]?.getD 0≤1 := by
    cases he : kinds[i/2]? with
    | none => simp
    | some x => exact binary x (List.mem_of_getElem? he)
  have hc : 1-i%2+i%2*kinds[i/2]?.getD 0≤1 := by
    have hcases : i%2=0 ∨ i%2=1 := by omega
    rcases hcases with h | h <;> simp [h] <;> omega
  have hM := input.two ▸ bounded.1 Reg.two
  have small : ValidAtoms M cellAtoms S := by
    simp [cellAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,index,input.two,input.input]
    exact ⟨hi,by nlinarith,by omega⟩
  obtain ⟨run,hU⟩ := atoms_runs bounded cellAtoms small
  refine ⟨run,hU,?_⟩
  intro f
  cases f <;> simp [result,value,cellAtoms,applyAtoms,Atom.apply,BinaryOp.eval,
    Store.setScalar,index,input.two,input.input]

theorem program_runs (f : Field) (kinds : List ℕ) (S : State) (M : ℕ)
    (bounded : S.Bounded M) (input : Inputs kinds S) (binary : ∀x∈kinds,x≤1)
    (length : S.scalar .length=2*kinds.length) :
    ∃t≤20*kinds.length+6,∃U,Runs (storageBound Reg Arr M) (program f) S t U ∧ U.Bounded M ∧
      Inputs kinds U ∧ U.array .output=List.ofFn (fun i : Fin (2*kinds.length) => value kinds i f) := by
  have hM := input.two ▸ bounded.1 Reg.two
  let P : State → Prop := fun U => Inputs kinds U
  have scalarStable : ∀U,P U → ∀i : Fin 4,∀v,P (U.setScalar (registers i.succ) v) := by
    intro U hU i v
    refine ⟨hU.input,?_⟩
    fin_cases i <;> simpa [registers,Store.setScalar] using hU.two
  have outputStable : ∀U,P U → ∀xs,P (U.setArray .output xs) := by
    intro U hU xs; exact ⟨hU.input,hU.two⟩
  have body : ∀U,P U → U.Bounded M → U.scalar (registers 1)<2*kinds.length →
      ∃t≤6,∃V,Runs (storageBound Reg Arr M) cell U t V ∧ V.Bounded M ∧ P V ∧
        V.scalar (result f)=value kinds (U.scalar (registers 1)) f ∧
        V.array .output=U.array .output ∧
        ∀i : Fin 4,V.scalar (registers i.castSucc)=U.scalar (registers i.castSucc) := by
    intro U hU hB hi
    obtain ⟨run,hV,out⟩ := cell_runs kinds U M (U.scalar .index) hB hU binary rfl hi
    refine ⟨6,le_rfl,applyAtoms cellAtoms U,run,hV,?_,out f,rfl,?_⟩
    · exact ⟨hU.input,(run.scalar_eq_of_not_mem .two (by decide)).trans hU.two⟩
    · intro i; fin_cases i <;> exact run.scalar_eq_of_not_mem _ (by decide)
  obtain ⟨t,ht,U,run,hU,hP,out⟩ := materialize_runs registers Arr.output (result f) cell P
    (fun i => value kinds i f) M (2*kinds.length) 6 (by omega)
    scalarStable outputStable body S bounded input length
  exact ⟨t,by omega,U,run,hU,hP,out⟩

end GroupWL.MachinePrograms.GateCandidates
