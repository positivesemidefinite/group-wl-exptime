import GroupWL.MachinePrograms.NatArrayExpressionBounds

/-! Total natural expressions: out-of-range reads and zero divisors are
implemented by explicit machine branches, not semantic oracles. -/
namespace GroupWL.MachinePrograms.NatArrayExpressions
open NatArrayLanguage
set_option maxHeartbeats 3000000
inductive Total (R A : Type*) where
  | const (n : ℕ)
  | scalar (r : R)
  | read (a : A) (i : Total R A)
  | binary (op : Op) (a b : Total R A)
  | branch (c a b : Total R A)

variable {R A : Type*} [DecidableEq R] [DecidableEq A]

def Total.eval : Total R A → Store R A → ℕ
  | .const n,_=>n | .scalar r,S=>S.scalar r
  | .read a i,S=>(S.array a)[i.eval S]?.getD 0
  | .binary op a b,S=>op.eval (a.eval S) (b.eval S)
  | .branch c a b,S=>if c.eval S=0 then b.eval S else a.eval S

def Total.expression (length : A → R) : Total R A → Expr R A
  | .const n=>.const n | .scalar r=>.scalar r
  | .read a i=>.branch (.binary (.binary .lt) (i.expression length) (.scalar (length a)))
      (.read a (i.expression length)) (.const 0)
  | .binary (.binary op) a b=>.binary (.binary op) (a.expression length) (b.expression length)
  | .binary .quotient a b=>.branch (b.expression length)
      (.binary .quotient (a.expression length) (b.expression length)) (.const 0)
  | .binary .remainder a b=>.branch (b.expression length)
      (.binary .remainder (a.expression length) (b.expression length)) (a.expression length)
  | .branch c a b=>.branch (c.expression length) (a.expression length) (b.expression length)

theorem Total.expression_eval (e : Total R A) (length : A → R) (S : Store R A)
    (lengths : ∀a,S.scalar (length a)=(S.array a).length) :
    (e.expression length).eval S=e.eval S := by
  induction e with
  | const n=>rfl
  | scalar r=>rfl
  | read a i ih=>
    simp only [expression,Expr.eval,ih,lengths,Op.eval,BinaryOp.eval,eval]
    by_cases h : i.eval S<(S.array a).length
    · simp [h]
    · simp [h,List.getElem?_eq_none (Nat.le_of_not_gt h)]
  | binary op a b ia ib=>
    cases op with
    | binary op=>simp only [expression,Expr.eval,ia,ib,Op.eval,eval]
    | quotient=>simp only [expression,Expr.eval,ia,ib,Op.eval,eval]; split_ifs with h <;> simp [h]
    | remainder=>simp only [expression,Expr.eval,ia,ib,Op.eval,eval]; split_ifs with h <;> simp [h]
  | branch c a b ic ia ib=>simp only [expression,Expr.eval,ic,ia,ib,eval]

theorem Total.expression_valid (e : Total R A) (length : A → R) (S : Store R A)
    (lengths : ∀a,S.scalar (length a)=(S.array a).length) :
    (e.expression length).Valid S := by
  induction e with
  | const n=>trivial
  | scalar r=>trivial
  | read a i ih=>
    simp only [expression,Expr.Valid,Expr.eval,Op.valid,Op.eval,BinaryOp.eval,ih,lengths]
    by_cases h : (i.expression length).eval S<(S.array a).length <;> simp [h]
  | binary op a b ia ib=>
    cases op with
    | binary op=>simp only [expression,Expr.Valid,Op.valid,ia,ib,and_self]
    | quotient=>
      simp only [expression,Expr.Valid,Op.valid,ia,ib,true_and]
      split_ifs <;> first | trivial | omega
    | remainder=>
      simp only [expression,Expr.Valid,Op.valid,ia,ib,true_and]
      split_ifs <;> first | trivial | omega
  | branch c a b ic ia ib=>simp only [expression,Expr.Valid,ic,ia,ib,ite_self,and_self]

def Total.Literals (e : Total R A) (B : ℕ) : Prop := match e with
  | .const n=>n≤B | .scalar _=>True | .read _ i=>i.Literals B
  | .binary _ a b=>a.Literals B ∧ b.Literals B
  | .branch c a b=>c.Literals B ∧ a.Literals B ∧ b.Literals B

theorem Total.expression_literals (e : Total R A) (length : A → R) (B : ℕ)
    (h : e.Literals B) : (e.expression length).Literals B := by
  induction e with
  | const n=>exact h
  | scalar r=>trivial
  | read a i ih=>simpa [expression,Expr.Literals] using ih h
  | binary op a b ia ib=>cases op <;> simp [expression,Expr.Literals,ia h.1,ib h.2]
  | branch c a b ic ia ib=>simp [expression,Expr.Literals,ic h.1,ia h.2.1,ib h.2.2]

theorem Total.expression_safe (e : Total R A) (length : A → R) (S : Store R A) (B M : ℕ)
    (lengths : ∀a,S.scalar (length a)=(S.array a).length) (lit : e.Literals B)
    (vars : ∀r∈(e.expression length).variables,S.scalar r≤B)
    (arrays : ∀a x,x∈S.array a → x≤B)
    (bound : (B+2)^(2*(e.expression length).cost)≤M) :
    (e.expression length).Safe M S :=
  (e.expression length).safe_of_valid S B M (e.expression_valid length S lengths)
    (e.expression_literals length B lit) vars arrays bound

end GroupWL.MachinePrograms.NatArrayExpressions
