import GroupWL.MachinePrograms.ExpressionMap

/-! Static per-instruction bounds that retain the small range of comparisons and division. -/
namespace GroupWL.MachinePrograms.NatArrayExpressions
open NatArrayLanguage

def Op.valueBound : Op → ℕ → ℕ → ℕ
  | .binary .add, x,y => x+y
  | .binary .mul, x,y => x*y
  | .binary .sub, x,_ => x
  | .binary _, _,_ => 1
  | .quotient, x,_ => x
  | .remainder, x,_ => x

theorem Op.eval_le_valueBound (op : Op) {x y a b : ℕ} (ha : x≤a) (hb : y≤b) :
    op.eval x y ≤ op.valueBound a b := by
  cases op with
  | binary op =>
    cases op <;> simp only [Op.eval,BinaryOp.eval,Op.valueBound]
    · exact Nat.add_le_add ha hb
    · exact (Nat.sub_le _ _).trans ha
    · exact Nat.mul_le_mul ha hb
    all_goals split <;> omega
  | quotient => exact (Nat.div_le_self _ _).trans ha
  | remainder => exact (Nat.mod_le _ _).trans ha

variable {R A : Type*} [DecidableEq R] [DecidableEq A]

def Expr.valueBound (B : ℕ) : Expr R A → ℕ
  | .const n => n
  | .scalar _ | .read _ _ => B
  | .binary op x y => op.valueBound (x.valueBound B) (y.valueBound B)
  | .branch _ x y => max (x.valueBound B) (y.valueBound B)

def Expr.Fits (B M : ℕ) : Expr R A → Prop
  | .const n => n≤M
  | .scalar _ => True
  | .read _ i => i.Fits B M
  | .binary op a b => a.Fits B M ∧ b.Fits B M ∧ op.valueBound (a.valueBound B) (b.valueBound B)≤M
  | .branch c a b => c.Fits B M ∧ a.Fits B M ∧ b.Fits B M

omit [DecidableEq A] in
theorem Expr.fits_safe (e : Expr R A) (S : Store R A) (B M : ℕ)
    (arrays : ∀a x,x∈S.array a → x≤B) (vars : ∀r∈e.variables,S.scalar r≤B)
    (valid : e.Valid S) (fit : e.Fits B M) : e.Safe M S ∧ e.eval S≤e.valueBound B := by
  induction e with
  | const n => exact ⟨fit,le_rfl⟩
  | scalar r => exact ⟨trivial,vars r (by simp [Expr.variables])⟩
  | read a i ih =>
    have h := ih (by simpa [Expr.variables] using vars) valid.1 fit
    refine ⟨⟨h.1,valid.2⟩,?_⟩
    change (S.array a)[i.eval S]?.getD 0≤B
    cases he : (S.array a)[i.eval S]? with
    | none => simp
    | some v => exact arrays a v (List.mem_of_getElem? he)
  | binary op a b ia ib =>
    have ha := ia (fun r hr => vars r (by simp [Expr.variables,hr])) valid.1 fit.1
    have hb := ib (fun r hr => vars r (by simp [Expr.variables,hr])) valid.2.1 fit.2.1
    have value := op.eval_le_valueBound ha.2 hb.2
    exact ⟨⟨ha.1,hb.1,valid.2.2,value.trans fit.2.2⟩,value⟩
  | branch c a b ic ia ib =>
    have hc := ic (fun r hr => vars r (by simp [Expr.variables,hr])) valid.1 fit.1
    by_cases hz : c.eval S=0
    · have hb := ib (fun r hr => vars r (by simp [Expr.variables,hr])) (by simpa [hz] using valid.2) fit.2.2
      exact ⟨⟨hc.1,by simpa [hz] using hb.1⟩,by simpa only [eval,hz,if_true] using hb.2.trans (le_max_right _ _)⟩
    · have ha := ia (fun r hr => vars r (by simp [Expr.variables,hr])) (by simpa [hz] using valid.2) fit.2.1
      exact ⟨⟨hc.1,by simpa [hz] using ha.1⟩,by simpa only [eval,if_neg hz] using ha.2.trans (le_max_left _ _)⟩
end GroupWL.MachinePrograms.NatArrayExpressions
