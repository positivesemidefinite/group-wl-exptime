import GroupWL.MachinePrograms.ChargedExpressionBounds
import GroupWL.MachinePrograms.NatArrayExpressionClient

/-! A fixed finite-register program materializes the dense input twist from a charge vector. -/
namespace GroupWL.MachinePrograms.ChargedWriter
open NatArrayLanguage NatArrayExpressions

inductive Parameter where
  | inputDim | outputDim | inputStride | outputStride | modulus | rows | dimension
  deriving DecidableEq, Fintype
abbrev Reg := Fin 5 ⊕ Parameter
abbrev Arr := Unit ⊕ Unit
abbrev Term := Total Reg Unit
def loopRegs : Fin 5 ↪ Reg := ⟨Sum.inl, Sum.inl_injective⟩
def sizeReg (_ : Unit) : Reg := .inr .rows

def cell (charges : List ℕ) (p u v x y z : ℕ) : ℕ :=
  let i := z/v
  if z%v=1 then
    if x=i*u ∧ y=i*u+2 then charges[i]?.getD 0
    else if y=i*u ∧ x=i*u+2 then (p-charges[i]?.getD 0)%p else 0
  else 0

def atPosition (charges : List ℕ) (p u v X Z k : ℕ) : ℕ :=
  cell charges p u v (k/Z/X) (k/Z%X) (k%Z)

private def bin (op : BinaryOp) (a b : Term) : Term := .binary (.binary op) a b
private def pr (r : Parameter) : Term := .scalar (.inr r)
private def eqFlag (a b : Term) : Term := bin .eq a b

def term : Term :=
  let k : Term := .scalar (.inl 1)
  let ij : Term := .binary .quotient k (pr .outputDim)
  let x : Term := .binary .quotient ij (pr .inputDim)
  let y : Term := .binary .remainder ij (pr .inputDim)
  let z : Term := .binary .remainder k (pr .outputDim)
  let i : Term := .binary .quotient z (pr .outputStride)
  let a := bin .mul i (pr .inputStride)
  let b := bin .add a (.const 2)
  let get : Term := .read () i
  let neg : Term := .binary .remainder (bin .sub (pr .modulus) get) (pr .modulus)
  .branch (eqFlag (.binary .remainder z (pr .outputStride)) (.const 1))
    (.branch (bin .mul (eqFlag x a) (eqFlag y b)) get
      (.branch (bin .mul (eqFlag y a) (eqFlag x b)) neg (.const 0))) (.const 0)

private theorem test (a : Prop) [Decidable a] (x y : ℕ) :
    (if (if a then 1 else 0)=0 then y else x)=(if a then x else y) := by
  by_cases a <;> simp_all
private theorem test2 (a b : Prop) [Decidable a] [Decidable b] (x y : ℕ) :
    (if (if a then 1 else 0)*(if b then 1 else 0)=0 then y else x)=
      (if a ∧ b then x else y) := by
  by_cases a <;> by_cases b <;> simp_all

theorem term_eval (S : Store Reg Unit) :
    term.eval S=atPosition (S.array ()) (S.scalar (.inr .modulus)) (S.scalar (.inr .inputStride))
      (S.scalar (.inr .outputStride)) (S.scalar (.inr .inputDim)) (S.scalar (.inr .outputDim))
      (S.scalar (.inl 1)) := by
  simp only [term,atPosition,cell,bin,eqFlag,pr,Total.eval,Op.eval,BinaryOp.eval,test,test2]
  rfl

def expr : Expr Reg Arr := (term.expression sizeReg).map id Sum.inl
abbrev Registers := NatArrayExpressions.Registers Reg expr.need
abbrev State := Store Registers Arr
def program : Program Registers Arr := tableProgram expr loopRegs (.inr ())

structure Frame (params : Parameter → ℕ) (charges : List ℕ) (S : Store Reg Arr) : Prop where
  scalar : ∀ r, S.scalar (.inr r)=params r
  array : S.array (.inl ())=charges

private theorem validRegister (r : Reg) (hr : r ∈ (term.expression sizeReg).variables) :
    r=.inl 1 ∨ ∃j, r=.inr j := by
  cases r with
  | inl k => fin_cases k <;> first | exact Or.inl rfl | exact absurd hr (by decide)
  | inr j => exact Or.inr ⟨j,rfl⟩

theorem term_fits (B M : ℕ) (room : 2≤B) (budget : B*B+2≤M) :
    (term.expression sizeReg).Fits B M := by
  have b : B≤M := by nlinarith
  have sq : B*B≤M := by omega
  have two : 2≤M := by omega
  have one : 1≤M := by omega
  simp [term,bin,pr,eqFlag,Total.expression,Expr.Fits,Expr.valueBound,Op.valueBound,
    b,sq,two,one,budget]

theorem program_runs_square (params : Parameter → ℕ) (charges : List ℕ) (S : State) (B M n : ℕ)
    (room : 2≤B) (size : n≤B) (par : ∀r,params r≤B) (vals : ∀v∈charges,v≤B)
    (rows : params .rows=charges.length) (budget : B*B+2≤M)
    (bounded : S.Bounded M) (frame : Frame params charges (inputs S))
    (count : S.scalar (.inl (.inl 0))=n) :
    ∃t≤n*(expr.cost+4)+6,∃U,
      Runs (storageBound Registers Arr M) program S t U ∧ U.Bounded M ∧
      Frame params charges (inputs U) ∧ U.array (.inr ())=List.ofFn (fun k : Fin n =>
        atPosition charges (params .modulus) (params .inputStride) (params .outputStride)
          (params .inputDim) (params .outputDim) k.val) := by
  have hp : 1≤M := by omega
  have len (W : Store Reg Arr) (h : Frame params charges W) :
      ∀a, (project id Sum.inl W).scalar (sizeReg a)=((project id Sum.inl W).array a).length := by
    intro a
    cases a
    exact (h.scalar .rows).trans (rows.trans (congrArg List.length h.array.symm))
  apply tableProgram_runs expr loopRegs (.inr ()) (Frame params charges) _ M n hp
  · intro W h i v
    refine ⟨fun r => ?_,h.array⟩
    simpa [loopRegs,Store.setScalar] using h.scalar r
  · intro W h xs
    exact ⟨h.scalar,by simpa [Store.setArray] using h.array⟩
  · intro W h _ hi
    rw [expr,Expr.map_safe]
    apply (Expr.fits_safe _ _ B M ?_ ?_ (term.expression_valid sizeReg _ (len W h))
      (term_fits B M room budget)).1
    · intro a v hv
      cases a
      exact vals v (h.array ▸ hv)
    · intro r hr
      rcases validRegister r hr with rfl | ⟨j,rfl⟩
      · change W.scalar (.inl 1)≤B
        exact hi.le.trans size
      · exact (h.scalar j) ▸ par j

  · intro W h _
    rw [expr,Expr.map_eval,Total.expression_eval _ _ _ (len W h),term_eval]
    simp only [project,id_eq,h.scalar,h.array,loopRegs,Function.Embedding.coeFn_mk]
  · exact bounded
  · exact frame
  · exact count

theorem program_runs (params : Parameter → ℕ) (charges : List ℕ) (S : State) (B M n : ℕ)
    (room : 2≤B) (size : n≤B) (par : ∀r,params r≤B) (vals : ∀v∈charges,v≤B)
    (rows : params .rows=charges.length) (budget : (B+2)^(2*(term.expression sizeReg).cost)≤M)
    (bounded : S.Bounded M) (frame : Frame params charges (inputs S))
    (count : S.scalar (.inl (.inl 0))=n) :
    ∃t≤n*(expr.cost+4)+6,∃U,
      Runs (storageBound Registers Arr M) program S t U ∧ U.Bounded M ∧
      Frame params charges (inputs U) ∧ U.array (.inr ())=List.ofFn (fun k : Fin n =>
        atPosition charges (params .modulus) (params .inputStride) (params .outputStride)
          (params .inputDim) (params .outputDim) k.val) := by
  have exponent : 2≤2*(term.expression sizeReg).cost := by decide
  have bound : (B+2)^2≤M := (Nat.pow_le_pow_right (by omega) exponent).trans budget
  exact program_runs_square params charges S B M n room size par vals rows (by nlinarith) bounded frame count

end GroupWL.MachinePrograms.ChargedWriter

