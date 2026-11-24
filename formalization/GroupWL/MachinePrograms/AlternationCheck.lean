import GroupWL.MachinePrograms.BilinearProgram
import GroupWL.MachinePrograms.NatArrayComponents
import GroupWL.MachinePrograms.NatArrayPower

/-! The exhaustive alternating-form check is a fixed finite array program. -/
namespace GroupWL.MachinePrograms.AlternationCheck

open NatArrayLanguage
open scoped BigOperators

inductive Control where
  | order | powerTodo | powerOne | vectorTodo | coordinateTodo | valid | flag | zero
  deriving DecidableEq, Fintype

abbrev Reg := BilinearEvaluation.Reg ⊕ Control
abbrev Arr := BilinearEvaluation.Arr ⊕ Empty
abbrev State := Store Reg Arr
abbrev Code := NatArrayLanguage.Program Reg Arr

def l (r : BilinearEvaluation.Reg) : Reg := .inl r
def a (r : Control) : Reg := .inr r

def powerRegs : Fin 5 ↪ Reg where
  toFun i := ![l .modulus,l .inputDimension,a .order,a .powerTodo,a .powerOne] i
  inj' := by decide

def evaluate : Code := BilinearEvaluation.evaluate.map Sum.inl Sum.inl
def coordinateStep : Code := .seq evaluate (atoms [
  .binary .eq (a .flag) (l .total) (a .zero),
  .binary .mul (a .valid) (a .valid) (a .flag)])
def coordinates : Code := countedLoop (l .coordinate) (a .coordinateTodo) (l .outputDimension) (l .one) coordinateStep
def vectorStep : Code := .seq (.atom (.copy (l .right) (l .left))) coordinates
def program : Code := .seq (NatArrayPower.program powerRegs)
  (.seq (atoms [.const (a .valid) 1,.const (a .zero) 0,.const (l .one) 1])
    (countedLoop (l .left) (a .vectorTodo) (a .order) (l .one) vectorStep))

def zeroFlag (n : ℕ) : ℕ := if n=0 then 1 else 0
@[simp] theorem zeroFlag_le_one (n : ℕ) : zeroFlag n≤1 := by unfold zeroFlag; split <;> omega
@[simp] theorem zeroFlag_eq_one (n : ℕ) : zeroFlag n=1 ↔ n=0 := by simp [zeroFlag]

def coordinateProduct (C : List ℕ) (p n m x j : ℕ) : ℕ :=
  ∏z ∈ Finset.range j,zeroFlag (BilinearEvaluation.partialValue C p n m x x z n)

@[simp] theorem coordinateProduct_zero (C : List ℕ) (p n m x : ℕ) :
    coordinateProduct C p n m x 0=1 := by simp [coordinateProduct]

theorem coordinateProduct_succ (C : List ℕ) (p n m x j : ℕ) :
    coordinateProduct C p n m x (j+1)=
      coordinateProduct C p n m x j*zeroFlag (BilinearEvaluation.partialValue C p n m x x j n) := by
  simp [coordinateProduct,Finset.prod_range_succ]

theorem coordinateProduct_le_one (C : List ℕ) (p n m x j : ℕ) :
    coordinateProduct C p n m x j≤1 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [coordinateProduct_succ]
    exact (Nat.mul_le_mul ih (zeroFlag_le_one _)).trans (by decide)

theorem evaluator_one {B : ℕ} {S T : BilinearEvaluation.State} {t : ℕ}
    (h : Runs B BilinearEvaluation.evaluate S t T) : T.scalar .one=1 := by
  cases h with
  | seq first last =>
    rw [last.scalar_eq_of_not_mem .one (by decide)]
    cases first with
    | seq h1 rest =>
      cases h1
      cases rest with
      | seq h2 rest =>
        cases h2
        cases rest with
        | seq h3 rest =>
          cases h3
          cases rest
          simp [Atom.apply,Store.setScalar]

theorem coordinateStep_runs (S : State) (M : ℕ) (hb : S.Bounded M)
    (hpositive : 0<S.scalar (l .modulus))
    (hroom : (S.scalar (l .modulus))^3+S.scalar (l .modulus)≤M)
    (hcoordinate : S.scalar (l .coordinate)<S.scalar (l .outputDimension))
    (hlength : (S.array (.inl .coefficients)).length=
      S.scalar (l .inputDimension)*S.scalar (l .inputDimension)*S.scalar (l .outputDimension))
    (hcoefficients : ∀x∈S.array (.inl .coefficients),x<S.scalar (l .modulus))
    (hright : S.scalar (l .right)=S.scalar (l .left))
    (hvalid : S.scalar (a .valid)≤1) (hzero : S.scalar (a .zero)=0) :
    ∃t≤14*(S.scalar (l .inputDimension))^2+9*S.scalar (l .inputDimension)+8,∃T,
      Runs (storageBound Reg Arr M) coordinateStep S t T ∧ T.Bounded M ∧
      T.scalar (l .one)=1 ∧ T.scalar (a .valid)=S.scalar (a .valid)*zeroFlag
        (BilinearEvaluation.partialValue (S.array (.inl .coefficients)) (S.scalar (l .modulus))
          (S.scalar (l .inputDimension)) (S.scalar (l .outputDimension))
          (S.scalar (l .left)) (S.scalar (l .left)) (S.scalar (l .coordinate))
          (S.scalar (l .inputDimension))) := by
  have hM : 1≤M := by omega
  obtain ⟨t,ht,U,evalRun,hU,hval⟩ := BilinearEvaluation.evaluate_runs S.left M hb.left
    hpositive hroom hcoordinate hlength hcoefficients
  change t≤14*(S.scalar (l .inputDimension))^2+9*S.scalar (l .inputDimension)+6 at ht
  let V := U.join S.right
  have hV : V.Bounded M := hU.join hb.right
  have first : Runs (storageBound Reg Arr M) evaluate S t V := evalRun.left_bounded hb
  let as : List (Atom Reg Arr) := [.binary .eq (a .flag) (l .total) (a .zero),
    .binary .mul (a .valid) (a .valid) (a .flag)]
  have vvalid : V.scalar (a .valid)≤1 := hvalid
  have vzero : V.scalar (a .zero)=0 := hzero
  have valid : ValidAtoms M as V := by
    change V.scalar (.inr Control.zero)=0 at vzero
    change V.scalar (.inr Control.valid)≤1 at vvalid
    by_cases h : V.scalar (.inl BilinearEvaluation.Reg.total)=0 <;>
      simp [as,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
        Store.setScalar,a,l,vzero,h,hM] <;> omega
  obtain ⟨last,bounded⟩ := atoms_runs hV as valid
  refine ⟨t+2,by omega,applyAtoms as V,.seq first last,bounded,?_,?_⟩
  · have hone := evaluator_one evalRun
    simpa [applyAtoms,as,Atom.apply,Store.setScalar,V,a,l] using hone
  · simp only [applyAtoms,as,List.foldl_cons,List.foldl_nil,Atom.apply,BinaryOp.eval,
      Store.setScalar,Function.update_apply]
    simp only [a,l,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq,ite_false,ite_true]
    change S.scalar (a .valid)*(if U.scalar .total=S.scalar (a .zero) then 1 else 0)=_
    rw [hzero,hval]
    change S.scalar (a .valid)*zeroFlag
      (BilinearEvaluation.partialValue (S.array (.inl .coefficients)) (S.scalar (l .modulus))
        (S.scalar (l .inputDimension)) (S.scalar (l .outputDimension))
        (S.scalar (l .left)) (S.scalar (l .right)) (S.scalar (l .coordinate))
        (S.scalar (l .inputDimension)))=_
    rw [hright]
    rfl

end GroupWL.MachinePrograms.AlternationCheck
