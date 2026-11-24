import GroupWL.MachinePrograms.CandidateExtend
import GroupWL.MachinePrograms.NatArrayPowers

/-! Fixed finite-register decoder for compact numeric p-group candidates.
It processes the variable number of cyclic-extension stages in a loop. -/
namespace GroupWL.MachinePrograms.CandidateDecoder
open NatArrayLanguage
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

inductive Control where
  | prime | dimension | level | todo | one | zero | order | code | valid
  | power | powerTodo | powerOne | quotient | imageCode | carry
  deriving DecidableEq,Fintype
inductive Output where
  | table
  deriving DecidableEq,Fintype
abbrev Reg := CandidateExtend.Reg ⊕ Control
abbrev Arr := CandidateExtend.Arr ⊕ Output
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr
instance : DecidableEq Reg := inferInstance
instance : DecidableEq Arr := inferInstance
instance : Fintype Reg := inferInstance
instance : Fintype Arr := inferInstance

def powerRegisters : Fin 5 ↪ Reg :=
  ⟨![.inr .order,.inr .level,.inr .power,.inr .powerTodo,.inr .powerOne],by decide⟩
def extractAtoms : List (Atom Reg Arr) := [
  .divmod (.inr .quotient) (.inr .imageCode) (.inr .code) (.inr .power),
  .divmod (.inr .code) (.inr .carry) (.inr .quotient) (.inr .order)]
def setupAtoms : List (Atom Reg Arr) := [
  .copy (.inl CandidateExtend.nReg) (.inr .order),
  .copy (.inl CandidateExtend.dimensionReg) (.inr .level),
  .const (.inl CandidateExtend.identityReg) 0,
  .copyArray (.inl CandidateExtend.tableArray) (.inr .table),
  .copy (.inl CandidateExtend.imageIndex) (.inr .imageCode),
  .copy (.inl CandidateExtend.primeReg) (.inr .prime),
  .copy (.inl CandidateExtend.carryReg) (.inr .carry)]
def finishAtoms : List (Atom Reg Arr) := [
  .copyArray (.inr .table) (.inl CandidateExtend.outputArray),
  .copy (.inr .valid) (.inl CandidateExtend.resultReg)]
def extend : Code := .seq (atoms setupAtoms)
  (.seq (CandidateExtend.compute.map Sum.inl Sum.inl) (atoms finishAtoms))
def body : Code := sequence [power powerRegisters,atoms extractAtoms,
  .branch (.inr .valid) extend .skip,
  .atom (.binary .mul (.inr .order) (.inr .order) (.inr .prime))]
def prepare (p : ℕ) : List (Atom Reg Arr) := [
  .const (.inr .prime) p,.const (.inr .one) 1,.const (.inr .zero) 0,
  .const (.inr .order) 1,.const (.inr .valid) 1,.allocate (.inr .table) (.inr .one) (.inr .zero)]
def decode (p : ℕ) : Code := .seq (atoms (prepare p))
  (countedLoop (.inr .level) (.inr .todo) (.inr .dimension) (.inr .one) body)

theorem extract_runs (S : State) (M n j q : ℕ) (hb : S.Bounded M)
    (hn : S.scalar (.inr .order)=n) (hp : S.scalar (.inr .power)=n^j)
    (hq : S.scalar (.inr .code)=q) (hnpos : 0<n) :
    Runs (storageBound Reg Arr M) (atoms extractAtoms) S 2 (applyAtoms extractAtoms S) ∧
      (applyAtoms extractAtoms S).Bounded M ∧
      (applyAtoms extractAtoms S).scalar (.inr .imageCode)=q%(n^j) ∧
      (applyAtoms extractAtoms S).scalar (.inr .carry)=q/(n^j)%n ∧
      (applyAtoms extractAtoms S).scalar (.inr .code)=q/(n^(j+1)) := by
  have hv : ValidAtoms M extractAtoms S := by
    simp [extractAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,Store.setScalar,hn,hp,
      hnpos,pow_pos hnpos]
  obtain ⟨run,hT⟩ := atoms_runs hb extractAtoms hv
  refine ⟨run,hT,?_,?_,?_⟩ <;>
    simp [applyAtoms,extractAtoms,Atom.apply,Store.setScalar,hq,hn,hp,Nat.div_div_eq_div_mul,pow_succ]

end GroupWL.MachinePrograms.CandidateDecoder
