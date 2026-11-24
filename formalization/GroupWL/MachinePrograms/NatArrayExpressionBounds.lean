import GroupWL.MachinePrograms.NatArrayExpressionClient

/-! Uniform polynomial bounds for fixed arithmetic expression programs. -/
namespace GroupWL.MachinePrograms.NatArrayExpressions
open NatArrayLanguage
set_option maxHeartbeats 3000000
variable {R A : Type*} [DecidableEq R] [DecidableEq A]

def Expr.Literals (e : Expr R A) (B : ℕ) : Prop := match e with
  | .const n=>n≤B | .scalar _=>True | .read _ i=>i.Literals B
  | .binary _ a b=>a.Literals B ∧ b.Literals B
  | .branch c a b=>c.Literals B ∧ a.Literals B ∧ b.Literals B

def Expr.Valid (e : Expr R A) (S : Store R A) : Prop := match e with
  | .const _=>True | .scalar _=>True
  | .read a i=>i.Valid S ∧ i.eval S<(S.array a).length
  | .binary op a b=>a.Valid S ∧ b.Valid S ∧ op.valid (b.eval S)
  | .branch c a b=>c.Valid S ∧ if c.eval S=0 then b.Valid S else a.Valid S

theorem Expr.cost_pos (e : Expr R A) : 0<e.cost := by induction e <;> simp_all [Expr.cost] <;> omega

theorem Op.eval_le (op : Op) (x y : ℕ) : op.eval x y≤(x+1)*(y+1) := by
  cases op with
  | binary op=>cases op <;> simp [Op.eval,BinaryOp.eval] <;> (try split_ifs) <;> nlinarith
  | quotient=>have h := Nat.div_le_self x y; simp only [Op.eval]; nlinarith
  | remainder=>have h := Nat.mod_le x y; simp only [Op.eval]; nlinarith

theorem pow_step_bound (B n x : ℕ) (hx : x≤(B+2)^n) : x+1≤(B+2)^(n+1) := by
  have hp : 1≤(B+2)^n := Nat.one_le_pow n (B+2) (by omega)
  rw [pow_succ]
  nlinarith

theorem Expr.eval_le (e : Expr R A) (S : Store R A) (B : ℕ)
    (lit : e.Literals B) (vars : ∀r∈e.variables,S.scalar r≤B)
    (arrays : ∀a x,x∈S.array a → x≤B) : e.eval S≤(B+2)^(2*e.cost) := by
  induction e with
  | const n=>simp only [Expr.eval,Expr.cost]; change n≤(B+2)^2; change n≤B at lit; nlinarith
  | scalar r=>have h := vars r (by simp [Expr.variables]); simp only [Expr.eval,Expr.cost]; change S.scalar r≤(B+2)^2; nlinarith
  | read a i ih=>
    have h : (S.array a)[i.eval S]?.getD 0≤B := by
      cases he : (S.array a)[i.eval S]? with
      | none=>simp
      | some x=>exact arrays a x (List.mem_of_getElem? he)
    have hp := (Expr.read a i).cost_pos
    have hB : B≤(B+2)^(2*(Expr.read a i).cost) := by
      calc B≤B+2 := by omega
           _=(B+2)^1 := by simp
           _≤_ := by apply Nat.pow_le_pow_right (by omega); omega
    exact h.trans hB
  | binary op a b ia ib=>
    have ha := ia lit.1 (fun r hr=>vars r (by simp [Expr.variables,hr]))
    have hb := ib lit.2 (fun r hr=>vars r (by simp [Expr.variables,hr]))
    calc
      _ ≤ (a.eval S+1)*(b.eval S+1) := Op.eval_le op _ _
      _ ≤ (B+2)^(2*a.cost+1)*(B+2)^(2*b.cost+1) := Nat.mul_le_mul (pow_step_bound _ _ _ ha) (pow_step_bound _ _ _ hb)
      _ = _ := by rw [←pow_add]; congr 1; simp [Expr.cost]; omega
  | branch c a b ic ia ib=>
    have ha := ia lit.2.1 (fun r hr=>vars r (by simp [Expr.variables,hr]))
    have hb := ib lit.2.2 (fun r hr=>vars r (by simp [Expr.variables,hr]))
    simp only [Expr.eval]
    split_ifs
    · exact hb.trans (by apply Nat.pow_le_pow_right (by omega); simp only [Expr.cost]; omega)
    · exact ha.trans (by apply Nat.pow_le_pow_right (by omega); simp only [Expr.cost]; omega)

theorem Expr.safe_of_valid (e : Expr R A) (S : Store R A) (B M : ℕ)
    (valid : e.Valid S) (lit : e.Literals B) (vars : ∀r∈e.variables,S.scalar r≤B)
    (arrays : ∀a x,x∈S.array a → x≤B) (bound : (B+2)^(2*e.cost)≤M) : e.Safe M S := by
  induction e with
  | const n=>exact le_trans lit (le_trans (by change B≤(B+2)^2; nlinarith : B≤(B+2)^(2*(Expr.const (R:=R) (A:=A) n).cost)) bound)
  | scalar r=>trivial
  | read a i ih=>
    refine ⟨ih valid.1 lit vars ?_,valid.2⟩
    exact le_trans (by apply Nat.pow_le_pow_right (by omega); simp only [Expr.cost]; omega) bound
  | binary op a b ia ib=>
    have va := fun (r:R) (hr:r∈a.variables)=>vars r (by simp [Expr.variables,hr] : r∈(Expr.binary op a b).variables)
    have vb := fun (r:R) (hr:r∈b.variables)=>vars r (by simp [Expr.variables,hr] : r∈(Expr.binary op a b).variables)
    refine ⟨ia valid.1 lit.1 va (le_trans (by apply Nat.pow_le_pow_right (by omega); simp only [Expr.cost]; omega) bound),
      ib valid.2.1 lit.2 vb (le_trans (by apply Nat.pow_le_pow_right (by omega); simp only [Expr.cost]; omega) bound),valid.2.2,?_⟩
    exact ((Expr.binary op a b).eval_le S B lit vars arrays).trans bound
  | branch c a b ic ia ib=>
    have vc := fun (r:R) (hr:r∈c.variables)=>vars r (by simp [Expr.variables,hr] : r∈(Expr.branch c a b).variables)
    have va := fun (r:R) (hr:r∈a.variables)=>vars r (by simp [Expr.variables,hr] : r∈(Expr.branch c a b).variables)
    have vb := fun (r:R) (hr:r∈b.variables)=>vars r (by simp [Expr.variables,hr] : r∈(Expr.branch c a b).variables)
    refine ⟨ic valid.1 lit.1 vc (le_trans (by apply Nat.pow_le_pow_right (by omega); simp only [Expr.cost]; omega) bound),?_⟩
    dsimp only [Expr.Safe]
    split_ifs with hz
    · exact ib (by simpa [Expr.Valid,hz] using valid.2) lit.2.2 vb
        (le_trans (by apply Nat.pow_le_pow_right (by omega); simp only [Expr.cost]; omega) bound)
    · exact ia (by simpa [Expr.Valid,hz] using valid.2) lit.2.1 va
        (le_trans (by apply Nat.pow_le_pow_right (by omega); simp only [Expr.cost]; omega) bound)

end GroupWL.MachinePrograms.NatArrayExpressions
