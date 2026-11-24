import GroupWL.MachinePrograms.NatArrayParser
import GroupWL.DimensionEncoding

/-! Raw suffix parsing of positive unary and binary WL dimensions. -/
namespace GroupWL.MachinePrograms.DimensionParser
open NatArrayLanguage
open NatArrayLowering (bitNat)

variable {Reg Arr : Type*} [DecidableEq Reg] [DecidableEq Arr] [Fintype Reg] [Fintype Arr]

-- Position, length, accumulator, validity, scan flag, current bit, temporary, one, two.
def bitStep (e : Statement.DimensionEncoding) (r : Fin 9 ↪ Reg) (input : Arr) : NatArrayLanguage.Program Reg Arr :=
  atoms ([.read (r 5) input (r 0),.binary .add (r 0) (r 0) (r 7)] ++
    (match e with
    | .binary => [.binary .mul (r 2) (r 2) (r 8),.binary .add (r 2) (r 2) (r 5)]
    | .unary => [.binary .add (r 2) (r 2) (r 7),.binary .mul (r 3) (r 3) (r 5)]) ++
    [.binary .lt (r 4) (r 0) (r 1)])

def suffixLoop (e : Statement.DimensionEncoding) (r : Fin 9 ↪ Reg) (input : Arr) : NatArrayLanguage.Program Reg Arr :=
  .while (r 4) (bitStep e r input)

def firstBit (r : Fin 9 ↪ Reg) (input : Arr) : NatArrayLanguage.Program Reg Arr := atoms [
  .read (r 5) input (r 0),.binary .add (r 0) (r 0) (r 7),
  .copy (r 2) (r 5),.copy (r 3) (r 5),.binary .lt (r 4) (r 0) (r 1)]

def program (e : Statement.DimensionEncoding) (r : Fin 9 ↪ Reg) (input : Arr) : NatArrayLanguage.Program Reg Arr :=
  .seq (atoms [.const (r 2) 0,.const (r 3) 0,.const (r 7) 1,.const (r 8) 2,
    .binary .lt (r 4) (r 0) (r 1)])
    (.branch (r 4) (.seq (firstBit r input) (suffixLoop e r input)) .skip)

def valueStep (e : Statement.DimensionEncoding) (n : ℕ) (b : Bool) : ℕ :=
  match e with | .binary =>2*n+bitNat b | .unary =>n+1

def validStep (e : Statement.DimensionEncoding) (v : ℕ) (b : Bool) : ℕ :=
  match e with | .binary =>v | .unary =>v*bitNat b

def valueFold (e : Statement.DimensionEncoding) (n : ℕ) (bits : List Bool) : ℕ :=
  bits.foldl (valueStep e) n

def validFold (e : Statement.DimensionEncoding) (v : ℕ) (bits : List Bool) : ℕ :=
  bits.foldl (validStep e) v

theorem valueFold_bound (e : Statement.DimensionEncoding) (bits : List Bool) (n : ℕ) :
    valueFold e n bits+1≤(n+1)*2^bits.length := by
  induction bits generalizing n with
  | nil => simp [valueFold]
  | cons b bs ih =>
    have hh := ih (valueStep e n b)
    have hv : valueStep e n b+1≤2*(n+1) := by cases e <;> cases b <;> simp [valueStep,bitNat] <;> omega
    simp only [valueFold,List.foldl_cons,List.length_cons] at *
    calc
      _ ≤ (valueStep e n b+1)*2^bs.length := hh
      _ ≤ (2*(n+1))*2^bs.length := Nat.mul_le_mul_right _ hv
      _ = _ := by rw [pow_succ];ring

theorem validFold_bound (e : Statement.DimensionEncoding) (bits : List Bool) (v : ℕ) (hv : v≤1) :
    validFold e v bits≤1 := by
  induction bits generalizing v with
  | nil =>exact hv
  | cons b bs ih =>
    apply ih
    cases e <;> cases b <;> simpa [validStep,bitNat] using hv

theorem validFold_unary (bits : List Bool) (v : ℕ) :
    validFold .unary v bits=if ∀b∈bits,b=true then v else 0 := by
  induction bits generalizing v with
  | nil =>simp [validFold]
  | cons b bs ih =>
    change validFold .unary (validStep .unary v b) bs=_
    rw [ih]
    cases b <;> simp [validStep,bitNat]

theorem parsed_suffix (e : Statement.DimensionEncoding) (b : Bool) (bits : List Bool) :
    Statement.readDimension e (b::bits)=
      if validFold e (bitNat b) bits=0 then none else
        some (valueFold e (bitNat b) bits) := by
  cases e with
  | binary =>
    have hh : ∀bits v,validFold .binary v bits=v := by
      intro bits v
      induction bits generalizing v with
      | nil =>rfl
      | cons b bs ih =>exact ih v
    cases b <;> simp [Statement.readDimension,hh,valueFold,valueStep,bitNat,Statement.binaryValue]
    rfl
  | unary =>
    have hh : ∀bits n,valueFold .unary n bits=n+bits.length := by
      intro bits n
      induction bits generalizing n with
      | nil =>simp [valueFold]
      | cons b bs ih =>
        change valueFold .unary (n+1) bs=n+(bs.length+1)
        rw [ih]
        omega
    cases b <;> simp [Statement.readDimension,validFold_unary,hh,bitNat]
    split <;> simp_all [Nat.add_comm]

end GroupWL.MachinePrograms.DimensionParser
