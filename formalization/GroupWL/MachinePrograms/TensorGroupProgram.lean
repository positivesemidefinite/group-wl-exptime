import GroupWL.MachinePrograms.AlternationCheck
import GroupWL.MachinePrograms.TensorGroupCode

/-! Concrete arithmetic for one product in the tensor group. -/
namespace GroupWL.MachinePrograms.TensorGroupProgram

open NatArrayLanguage

inductive Control where
  | result | place | leftRest | rightRest | leftDigit | rightDigit | quotient | term
  | index | remaining | dimension | half | flag | zero | order | powerTodo | powerOne
  | pairIndex | pairTodo | square
  deriving DecidableEq, Fintype

abbrev Reg := BilinearEvaluation.Reg ⊕ Control
abbrev Arr := BilinearEvaluation.Arr ⊕ Unit
abbrev State := Store Reg Arr
abbrev Code := NatArrayLanguage.Program Reg Arr

def l (r : BilinearEvaluation.Reg) : Reg := .inl r
def a (r : Control) : Reg := .inr r

def evaluate : Code := BilinearEvaluation.evaluate.map Sum.inl Sum.inl

def prepareDigits : List (Atom Reg Arr) := [
  .divmod (a .quotient) (a .leftDigit) (a .leftRest) (l .modulus),
  .copy (a .leftRest) (a .quotient),
  .divmod (a .quotient) (a .rightDigit) (a .rightRest) (l .modulus),
  .copy (a .rightRest) (a .quotient),
  .binary .add (a .term) (a .leftDigit) (a .rightDigit),
  .binary .lt (a .flag) (a .index) (l .inputDimension)]

def central : Code := .seq (.atom (.binary .sub (l .coordinate) (a .index) (l .inputDimension)))
  (.seq evaluate (atoms [.binary .mul (a .flag) (a .half) (l .total),
    .binary .add (a .term) (a .term) (a .flag)]))

def finishDigit : List (Atom Reg Arr) := [
  .divmod (a .quotient) (a .term) (a .term) (l .modulus),
  .binary .mul (a .leftDigit) (a .term) (a .place),
  .binary .add (a .result) (a .result) (a .leftDigit),
  .binary .mul (a .place) (a .place) (l .modulus)]

def step : Code := .seq (atoms prepareDigits)
  (.seq (.branch (a .flag) .skip central) (atoms finishDigit))

def product (half : ℕ) : Code := .seq (atoms [
  .const (l .one) 1,.const (a .result) 0,.const (a .place) 1,.const (a .half) half,
  .copy (a .leftRest) (l .left),.copy (a .rightRest) (l .right),
  .binary .add (a .dimension) (l .inputDimension) (l .outputDimension)])
  (countedLoop (a .index) (a .remaining) (a .dimension) (l .one) step)

theorem central_runs (S : State) (M : ℕ) (bounded : S.Bounded M)
    (positive : 0<S.scalar (l .modulus))
    (room : (S.scalar (l .modulus))^3+3*S.scalar (l .modulus)≤M)
    (coordinate : S.scalar (a .index)-S.scalar (l .inputDimension)<S.scalar (l .outputDimension))
    (length : (S.array (.inl .coefficients)).length=
      S.scalar (l .inputDimension)*S.scalar (l .inputDimension)*S.scalar (l .outputDimension))
    (small : ∀x∈S.array (.inl .coefficients),x<S.scalar (l .modulus))
    (half : S.scalar (a .half)<S.scalar (l .modulus))
    (term : S.scalar (a .term)≤2*S.scalar (l .modulus)) :
    ∃t≤14*(S.scalar (l .inputDimension))^2+9*S.scalar (l .inputDimension)+9,∃T,
      Runs (storageBound Reg Arr M) central S t T ∧ T.Bounded M ∧ T.scalar (l .one)=1 ∧
      T.scalar (a .term)=S.scalar (a .term)+S.scalar (a .half)*
        BilinearEvaluation.partialValue (S.array (.inl .coefficients)) (S.scalar (l .modulus))
          (S.scalar (l .inputDimension)) (S.scalar (l .outputDimension))
          (S.scalar (l .left)) (S.scalar (l .right))
          (S.scalar (a .index)-S.scalar (l .inputDimension)) (S.scalar (l .inputDimension)) := by
  let V := (Atom.binary BinaryOp.sub (l .coordinate) (a .index) (l .inputDimension)).apply S
  have hs : (Atom.binary BinaryOp.sub (l .coordinate) (a .index) (l .inputDimension)).SmallResult M S :=
    (Nat.sub_le _ _).trans (bounded.1 (a .index))
  have prepare : Runs (storageBound Reg Arr M)
      (.atom (.binary .sub (l .coordinate) (a .index) (l .inputDimension))) S 1 V :=
    atom_runs bounded _ trivial hs
  have hV : V.Bounded M := Atom.apply_bounded bounded _ hs
  obtain ⟨t,ht,U,run,hU,hval⟩ := BilinearEvaluation.evaluate_runs V.left M hV.left
    positive (by change (S.scalar (l .modulus))^3+S.scalar (l .modulus)≤M; omega) coordinate length small
  change t≤14*(S.scalar (l .inputDimension))^2+9*S.scalar (l .inputDimension)+6 at ht
  let W := U.join V.right
  have hW : W.Bounded M := hU.join hV.right
  have evalRun : Runs (storageBound Reg Arr M) evaluate V t W := run.left_bounded hV
  have wtotal : W.scalar (l .total)<S.scalar (l .modulus) := by
    change U.scalar .total<S.scalar (l .modulus)
    rw [hval]
    exact Nat.mod_lt _ positive
  have whalf : W.scalar (a .half)=S.scalar (a .half) := rfl
  have wterm : W.scalar (a .term)=S.scalar (a .term) := rfl
  have hprod : W.scalar (a .half)*W.scalar (l .total)≤(S.scalar (l .modulus))^2 := by nlinarith
  have hsq : (S.scalar (l .modulus))^2≤(S.scalar (l .modulus))^3 :=
    pow_le_pow_right' (by omega) (by decide)
  let as : List (Atom Reg Arr) := [.binary .mul (a .flag) (a .half) (l .total),
    .binary .add (a .term) (a .term) (a .flag)]
  have valid : ValidAtoms M as W := by
    change W.scalar (.inr Control.half)*W.scalar (.inl BilinearEvaluation.Reg.total)≤_ at hprod
    change W.scalar (.inr Control.term)=_ at wterm
    simp [as,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar,a,l]
    exact ⟨by nlinarith,by nlinarith⟩
  obtain ⟨last,hT⟩ := atoms_runs hW as valid
  refine ⟨1+(t+2),by omega,applyAtoms as W,.seq prepare (.seq evalRun last),hT,?_,?_⟩
  · have hone := AlternationCheck.evaluator_one run
    simpa [applyAtoms,as,Atom.apply,Store.setScalar,a,l,W] using hone
  · simp only [applyAtoms,as,List.foldl_cons,List.foldl_nil,Atom.apply,BinaryOp.eval,
      Store.setScalar,Function.update_apply]
    simp only [a,l,Sum.inr.injEq,reduceCtorEq,ite_false,ite_true]
    change S.scalar (a .term)+S.scalar (a .half)*U.scalar .total=_
    rw [hval]
    rfl

end GroupWL.MachinePrograms.TensorGroupProgram
