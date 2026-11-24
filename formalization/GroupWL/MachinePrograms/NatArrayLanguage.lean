import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! # A finite-register language for the operational algorithms

The syntax contains only explicit arithmetic, array, branch, and loop
instructions. No instruction accepts a function on the input or an unbounded
semantic evaluator. Bounded executions record every intermediate store bound.
-/
namespace GroupWL.MachinePrograms.NatArrayLanguage

open scoped BigOperators
universe u v
variable {Reg : Type u} {Arr : Type v}

structure Store (Reg : Type u) (Arr : Type v) where
  scalar : Reg → ℕ
  array : Arr → List ℕ

namespace Store

def setScalar [DecidableEq Reg] (S : Store Reg Arr) (r : Reg) (n : ℕ) : Store Reg Arr :=
  {S with scalar := Function.update S.scalar r n}

def setArray [DecidableEq Arr] (S : Store Reg Arr) (a : Arr) (xs : List ℕ) : Store Reg Arr :=
  {S with array := Function.update S.array a xs}

/-- Unary scalar words and delimiter-separated unary arrays, with one unit
per register for a uniform positive bound. -/
def size [Fintype Reg] [Fintype Arr] (S : Store Reg Arr) : ℕ :=
  (∑ r, (S.scalar r+1)) + (∑ a, ((S.array a).length+(S.array a).sum+1))

theorem scalar_le_size [Fintype Reg] [Fintype Arr] (S : Store Reg Arr) (r : Reg) :
    S.scalar r ≤ S.size := by
  have h := Finset.single_le_sum (s := Finset.univ) (f := fun r => S.scalar r+1)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
  dsimp only at h
  unfold size
  omega

theorem array_length_le_size [Fintype Reg] [Fintype Arr] (S : Store Reg Arr) (a : Arr) :
    (S.array a).length ≤ S.size := by
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun a => (S.array a).length+(S.array a).sum+1)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
  dsimp only at h
  unfold size
  omega

theorem array_sum_le_size [Fintype Reg] [Fintype Arr] (S : Store Reg Arr) (a : Arr) :
    (S.array a).sum ≤ S.size := by
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun a => (S.array a).length+(S.array a).sum+1)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
  dsimp only at h
  unfold size
  omega

end Store

inductive BinaryOp where
  | add | sub | mul | eq | lt | le
  deriving DecidableEq, Fintype

def BinaryOp.eval : BinaryOp → ℕ → ℕ → ℕ
  | .add,a,b => a+b
  | .sub,a,b => a-b
  | .mul,a,b => a*b
  | .eq,a,b => if a=b then 1 else 0
  | .lt,a,b => if a<b then 1 else 0
  | .le,a,b => if a≤b then 1 else 0

inductive Atom (Reg : Type u) (Arr : Type v) where
  | const (destination : Reg) (value : ℕ)
  | copy (destination source : Reg)
  | binary (op : BinaryOp) (destination left right : Reg)
  | arrayLength (destination : Reg) (source : Arr)
  | read (destination : Reg) (source : Arr) (index : Reg)
  | write (destination : Arr) (index value : Reg)
  | allocate (destination : Arr) (length value : Reg)
  | copyArray (destination source : Arr)
  | clearArray (destination : Arr)
  | divmod (quotient remainder dividend divisor : Reg)
  deriving DecidableEq

variable [DecidableEq Reg] [DecidableEq Arr]

def Atom.apply : Atom Reg Arr → Store Reg Arr → Store Reg Arr
  | .const r n,S => S.setScalar r n
  | .copy r s,S => S.setScalar r (S.scalar s)
  | .binary op r a b,S => S.setScalar r (op.eval (S.scalar a) (S.scalar b))
  | .arrayLength r a,S => S.setScalar r (S.array a).length
  | .read r a i,S => S.setScalar r ((S.array a)[S.scalar i]?.getD 0)
  | .write a i v,S => S.setArray a ((S.array a).set (S.scalar i) (S.scalar v))
  | .allocate a n v,S => S.setArray a (List.replicate (S.scalar n) (S.scalar v))
  | .copyArray a b,S => S.setArray a (S.array b)
  | .clearArray a,S => S.setArray a []
  | .divmod q r a b,S =>
      (S.setScalar q (S.scalar a/S.scalar b)).setScalar r (S.scalar a%S.scalar b)

def Atom.Valid : Atom Reg Arr → Store Reg Arr → Prop
  | .read _ a i,S => S.scalar i < (S.array a).length
  | .write a i _,S => S.scalar i < (S.array a).length
  | .divmod q r _ b,S => q ≠ r ∧ 0 < S.scalar b
  | _,_ => True

instance Atom.validDecidable (a : Atom Reg Arr) (S : Store Reg Arr) : Decidable (a.Valid S) := by
  cases a <;> unfold Atom.Valid <;> infer_instance

inductive Program (Reg : Type u) (Arr : Type v) where
  | skip
  | atom (instruction : Atom Reg Arr)
  | seq (first second : Program Reg Arr)
  | branch (flag : Reg) (nonzero zero : Program Reg Arr)
  | while (flag : Reg) (body : Program Reg Arr)
  deriving DecidableEq

variable [Fintype Reg] [Fintype Arr]

/-- Exact abstract instruction count, with a common bound on every store in
the execution. The stack lowering accounts separately for primitive costs. -/
inductive Runs (bound : ℕ) : Program Reg Arr → Store Reg Arr → ℕ → Store Reg Arr → Prop
  | skip {S} (h : S.size ≤ bound) : Runs bound .skip S 0 S
  | atom {a S} (valid : a.Valid S) (before : S.size ≤ bound) (after : (a.apply S).size ≤ bound) :
      Runs bound (.atom a) S 1 (a.apply S)
  | seq {p q S T U t s} (first : Runs bound p S t T) (second : Runs bound q T s U) :
      Runs bound (.seq p q) S (t+s) U
  | branch_nonzero {r p q S T t} (h : S.scalar r ≠ 0) (body : Runs bound p S t T) :
      Runs bound (.branch r p q) S (t+1) T
  | branch_zero {r p q S T t} (h : S.scalar r = 0) (body : Runs bound q S t T) :
      Runs bound (.branch r p q) S (t+1) T
  | while_zero {r p S} (h : S.scalar r = 0) (small : S.size ≤ bound) :
      Runs bound (.while r p) S 1 S
  | while_nonzero {r p S T U t s} (h : S.scalar r ≠ 0) (body : Runs bound p S t T)
      (rest : Runs bound (.while r p) T s U) : Runs bound (.while r p) S (t+s+1) U

theorem Runs.start_bound {bound p S T t} (h : Runs (Reg := Reg) (Arr := Arr) bound p S t T) :
    S.size ≤ bound := by
  induction h with
  | skip h => exact h
  | atom _ h _ => exact h
  | seq _ _ ih _ => exact ih
  | branch_nonzero _ _ ih => exact ih
  | branch_zero _ _ ih => exact ih
  | while_zero _ h => exact h
  | while_nonzero _ _ _ ih _ => exact ih

theorem Runs.end_bound {bound p S T t} (h : Runs (Reg := Reg) (Arr := Arr) bound p S t T) :
    T.size ≤ bound := by
  induction h with
  | skip h => exact h
  | atom _ _ h => exact h
  | seq _ _ _ ih => exact ih
  | branch_nonzero _ _ ih => exact ih
  | branch_zero _ _ ih => exact ih
  | while_zero _ h => exact h
  | while_nonzero _ _ _ _ ih => exact ih

theorem Runs.mono {bound bound' p S T t}
    (h : Runs (Reg := Reg) (Arr := Arr) bound p S t T) (hle : bound ≤ bound') : Runs bound' p S t T := by
  induction h with
  | skip h => exact .skip (h.trans hle)
  | atom hv hb ha => exact .atom hv (hb.trans hle) (ha.trans hle)
  | seq _ _ ih ih' => exact .seq ih ih'
  | branch_nonzero h _ ih => exact .branch_nonzero h ih
  | branch_zero h _ ih => exact .branch_zero h ih
  | while_zero h hs => exact .while_zero h (hs.trans hle)
  | while_nonzero h _ _ ih ih' => exact .while_nonzero h ih ih'

end GroupWL.MachinePrograms.NatArrayLanguage
