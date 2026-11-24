import GroupWL.MachinePrograms.NatArrayFrames
import GroupWL.MachinePrograms.NatArrayProofs

/-! Read-only arithmetic expressions compiled into the finite-register array
instruction language. Conditional reads are required to be valid only on the
branch that executes. -/
namespace GroupWL.MachinePrograms.NatArrayExpressions
open NatArrayLanguage
set_option maxHeartbeats 4000000

inductive Op where
  | binary (op : BinaryOp)
  | quotient
  | remainder
  deriving DecidableEq

def Op.eval : Op → ℕ → ℕ → ℕ
  | .binary op,x,y=>op.eval x y
  | .quotient,x,y=>x/y
  | .remainder,x,y=>x%y

def Op.valid : Op → ℕ → Prop
  | .binary _,_=>True
  | .quotient,y=>0<y
  | .remainder,y=>0<y

inductive Expr (R A : Type*) where
  | const (n : ℕ)
  | scalar (r : R)
  | read (a : A) (index : Expr R A)
  | binary (op : Op) (left right : Expr R A)
  | branch (condition nonzero zero : Expr R A)

variable {R A : Type*} [DecidableEq R] [DecidableEq A]

def Expr.eval : Expr R A → Store R A → ℕ
  | .const n,_=>n
  | .scalar r,S=>S.scalar r
  | .read a i,S=>(S.array a)[i.eval S]?.getD 0
  | .binary op a b,S=>op.eval (a.eval S) (b.eval S)
  | .branch c a b,S=>if c.eval S=0 then b.eval S else a.eval S

def Expr.variables : Expr R A → Finset R
  | .const _=>∅
  | .scalar r=>{r}
  | .read _ i=>i.variables
  | .binary _ a b=>a.variables ∪ b.variables
  | .branch c a b=>c.variables ∪ (a.variables ∪ b.variables)

def Expr.need : Expr R A → ℕ
  | .const _=>0
  | .scalar _=>0
  | .read _ i=>i.need
  | .binary _ a b=>max a.need (b.need+1)
  | .branch c a b=>max c.need (max a.need b.need)

def Expr.cost : Expr R A → ℕ
  | .const _=>1
  | .scalar _=>1
  | .read _ i=>i.cost+1
  | .binary _ a b=>a.cost+b.cost+1
  | .branch c a b=>c.cost+max a.cost b.cost+1

def Expr.Safe (e : Expr R A) (M : ℕ) (S : Store R A) : Prop :=
  match e with
  | .const n=>n≤M
  | .scalar _=>True
  | .read a i=>i.Safe M S ∧ i.eval S<(S.array a).length
  | .binary op a b=>a.Safe M S ∧ b.Safe M S ∧ op.valid (b.eval S) ∧
      op.eval (a.eval S) (b.eval S)≤M
  | .branch c a b=>c.Safe M S ∧ if c.eval S=0 then b.Safe M S else a.Safe M S

def Op.atom (op : Op) (d t : R) : Atom R A :=
  match op with
  | .binary op=>.binary op d d t
  | .quotient=>.divmod d t d t
  | .remainder=>.divmod t d d t

def Expr.compile : Expr R A → R → List R → NatArrayLanguage.Program R A
  | .const n,d,_=>.atom (.const d n)
  | .scalar r,d,_=>.atom (.copy d r)
  | .read a i,d,ss=>.seq (i.compile d ss) (.atom (.read d a d))
  | .binary op a b,d,[]=>.skip
  | .binary op a b,d,t::ss=>.seq (a.compile d (t::ss))
      (.seq (b.compile t ss) (.atom (op.atom d t)))
  | .branch c a b,d,ss=>.seq (c.compile d ss)
      (.branch d (a.compile d ss) (b.compile d ss))

theorem Expr.eval_congr (e : Expr R A) {S U : Store R A}
    (arrays : U.array=S.array) (scalars : ∀r∈e.variables,U.scalar r=S.scalar r) :
    e.eval U=e.eval S := by
  induction e with
  | const n=>rfl
  | scalar r=>exact scalars r (by simp [Expr.variables])
  | read a i ih=>simp only [eval,ih (by simpa [Expr.variables] using scalars),arrays]
  | binary op a b ia ib=>
    rw [eval,eval,ia (fun r hr=>scalars r (by simp [Expr.variables,hr])),
      ib (fun r hr=>scalars r (by simp [Expr.variables,hr]))]
  | branch c a b ic ia ib=>
    rw [eval,eval,ic (fun r hr=>scalars r (by simp [Expr.variables,hr])),
      ia (fun r hr=>scalars r (by simp [Expr.variables,hr])),
      ib (fun r hr=>scalars r (by simp [Expr.variables,hr]))]

theorem Expr.safe_congr (e : Expr R A) {S U : Store R A} (M : ℕ)
    (arrays : U.array=S.array) (scalars : ∀r∈e.variables,U.scalar r=S.scalar r) :
    e.Safe M U↔e.Safe M S := by
  induction e with
  | const n=>rfl
  | scalar r=>rfl
  | read a i ih=>
    have h := fun r hr=>scalars r (show r∈(.read a i : Expr R A).variables from hr)
    simp only [Safe,ih h,Expr.eval_congr i arrays h,arrays]
  | binary op a b ia ib=>
    have ha := fun (r : R) (hr : r∈a.variables)=>scalars r (by simp [Expr.variables,hr] : r∈(.binary op a b : Expr R A).variables)
    have hb := fun (r : R) (hr : r∈b.variables)=>scalars r (by simp [Expr.variables,hr] : r∈(.binary op a b : Expr R A).variables)
    simp only [Safe,ia ha,ib hb,Expr.eval_congr a arrays ha,Expr.eval_congr b arrays hb]
  | branch c a b ic ia ib=>
    have hc := fun (r : R) (hr : r∈c.variables)=>scalars r (by simp [Expr.variables,hr] : r∈(.branch c a b : Expr R A).variables)
    have ha := fun (r : R) (hr : r∈a.variables)=>scalars r (by simp [Expr.variables,hr] : r∈(.branch c a b : Expr R A).variables)
    have hb := fun (r : R) (hr : r∈b.variables)=>scalars r (by simp [Expr.variables,hr] : r∈(.branch c a b : Expr R A).variables)
    simp only [Safe,ic hc,ia ha,ib hb,Expr.eval_congr c arrays hc]

theorem Expr.compile_arrays (e : Expr R A) (d : R) (ss : List R) :
    (e.compile d ss).arrayWrites=∅ := by
  induction e generalizing d ss with
  | const n=>rfl
  | scalar r=>rfl
  | read a i ih=>simp [compile,NatArrayLanguage.Program.arrayWrites,Atom.arrayWrites,ih]
  | binary op a b ia ib=>
    cases ss <;> cases op <;>
      simp [compile,Op.atom,NatArrayLanguage.Program.arrayWrites,Atom.arrayWrites,ia,ib]
  | branch c a b ic ia ib=>simp [compile,NatArrayLanguage.Program.arrayWrites,ic,ia,ib]

theorem Expr.compile_writes (e : Expr R A) (d : R) (ss : List R) :
    (e.compile d ss).scalarWrites⊆(d::ss).toFinset := by
  induction e generalizing d ss with
  | const n=>simp [compile,NatArrayLanguage.Program.scalarWrites,Atom.scalarWrites]
  | scalar r=>simp [compile,NatArrayLanguage.Program.scalarWrites,Atom.scalarWrites]
  | read a i ih=>
    simp only [compile,NatArrayLanguage.Program.scalarWrites,Atom.scalarWrites]
    exact Finset.union_subset (ih d ss) (by simp)
  | binary op a b ia ib=>
    cases ss with
    | nil=>simp [compile,NatArrayLanguage.Program.scalarWrites]
    | cons t ss=>
      have hab : (t::ss).toFinset⊆(d::t::ss).toFinset := by simp [Finset.subset_iff]; tauto
      have hop : (op.atom (A:=A) d t).scalarWrites⊆(d::t::ss).toFinset := by
        cases op <;> simp [Op.atom,Atom.scalarWrites,Finset.subset_iff]
      exact Finset.union_subset (ia d (t::ss)) (Finset.union_subset ((ib t ss).trans hab) hop)
  | branch c a b ic ia ib=>
    exact Finset.union_subset (ic d ss) (Finset.union_subset (ia d ss) (ib d ss))

end GroupWL.MachinePrograms.NatArrayExpressions
