import GroupWL.MachinePrograms.TotalExpressions

namespace GroupWL.MachinePrograms.NatArrayExpressions
open NatArrayLanguage
variable {R A R' A' : Type*} [DecidableEq R] [DecidableEq A] [DecidableEq R'] [DecidableEq A']

def project (f : R → R') (g : A → A') (S : Store R' A') : Store R A :=
  ⟨fun r=>S.scalar (f r),fun a=>S.array (g a)⟩

theorem Expr.map_eval (e : Expr R A) (f : R → R') (g : A → A') (S : Store R' A') :
    (e.map f g).eval S=e.eval (project f g S) := by
  induction e <;> simp_all [Expr.map,Expr.eval,project]

theorem Expr.map_safe (e : Expr R A) (f : R → R') (g : A → A') (S : Store R' A') (M : ℕ) :
    (e.map f g).Safe M S↔e.Safe M (project f g S) := by
  induction e <;> simp_all [Expr.map,Expr.Safe,Expr.map_eval,project]

end GroupWL.MachinePrograms.NatArrayExpressions
