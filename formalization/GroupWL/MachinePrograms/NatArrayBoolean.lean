import GroupWL.MachinePrograms.NatArrayFrames
import GroupWL.IndexedRefinement

/-! Finite Boolean expressions compile to explicit comparison and branch instructions. -/
namespace GroupWL.MachinePrograms.NatArrayLanguage
inductive BooleanTest (R : Type*) where
  | equal (left right : R)
  | less (left right : R)
  | all (left right : BooleanTest R)
  | any (left right : BooleanTest R)
namespace BooleanTest
variable {R A : Type*}

def reads : BooleanTest R → List R
  | .equal r s | .less r s => [r,s]
  | .all p q | .any p q => p.reads++q.reads

def size : BooleanTest R → ℕ
  | .equal _ _ | .less _ _ => 1
  | .all p q | .any p q => p.size+q.size+1

def eval (S : Store R A) : BooleanTest R → Bool
  | .equal r s => decide (S.scalar r=S.scalar s)
  | .less r s => decide (S.scalar r<S.scalar s)
  | .all p q => eval S p && eval S q
  | .any p q => eval S p || eval S q

def compile (destination : R) : BooleanTest R → Program R A
  | .equal r s => .atom (.binary .eq destination r s)
  | .less r s => .atom (.binary .lt destination r s)
  | .all p q => .seq (p.compile destination) (.branch destination (q.compile destination) .skip)
  | .any p q => .seq (p.compile destination) (.branch destination .skip (q.compile destination))

theorem eval_congr (p : BooleanTest R) (S T : Store R A)
    (h : ∀ r∈p.reads,S.scalar r=T.scalar r) : p.eval S=p.eval T := by
  induction p with
  | equal r s => simp [eval,h r (by simp [reads]),h s (by simp [reads])]
  | less r s => simp [eval,h r (by simp [reads]),h s (by simp [reads])]
  | all p q ihp ihq =>
    simp only [eval,ihp (fun r hr => h r (by simp [reads,hr])),ihq (fun r hr => h r (by simp [reads,hr]))]
  | any p q ihp ihq =>
    simp only [eval,ihp (fun r hr => h r (by simp [reads,hr])),ihq (fun r hr => h r (by simp [reads,hr]))]

variable [DecidableEq R] [DecidableEq A] [Fintype R] [Fintype A]

theorem writes (p : BooleanTest R) (destination r : R) (h : r≠destination) :
    r∉(p.compile destination : Program R A).scalarWrites := by
  induction p with
  | equal a b => simp [compile,Program.scalarWrites,Atom.scalarWrites,h]
  | less a b => simp [compile,Program.scalarWrites,Atom.scalarWrites,h]
  | all p q ihp ihq => simpa [compile,Program.scalarWrites] using And.intro ihp ihq
  | any p q ihp ihq => simpa [compile,Program.scalarWrites] using And.intro ihp ihq

theorem compile_runs (p : BooleanTest R) (destination : R) (S : Store R A) (B : ℕ)
    (hS : S.Bounded B) (h1 : 1≤B) (hf : destination∉p.reads) :
    ∃ t≤2*p.size,∃ T,Runs (storageBound R A B) (p.compile destination) S t T ∧ T.Bounded B ∧
      T.scalar destination=IndexedRefinement.boolNat (p.eval S) := by
  induction p generalizing S with
  | equal r s =>
    have hb : (if S.scalar r=S.scalar s then 1 else 0)≤B := by split_ifs <;>omega
    have run := atom_runs hS (.binary .eq destination r s) trivial hb
    exact ⟨1,by simp [size],_,run,Atom.apply_bounded hS _ hb,by simp [Atom.apply,eval,BinaryOp.eval,IndexedRefinement.boolNat]⟩
  | less r s =>
    have hb : (if S.scalar r<S.scalar s then 1 else 0)≤B := by split_ifs <;>omega
    have run := atom_runs hS (.binary .lt destination r s) trivial hb
    exact ⟨1,by simp [size],_,run,Atom.apply_bounded hS _ hb,by simp [Atom.apply,eval,BinaryOp.eval,IndexedRefinement.boolNat]⟩
  | all p q ihp ihq =>
    have hp : destination∉p.reads := by intro h;exact hf (List.mem_append_left q.reads h)
    have hq : destination∉q.reads := by intro h;exact hf (List.mem_append_right p.reads h)
    obtain ⟨t,ht,U,run,hU,hu⟩ := ihp S hS hp
    have he : q.eval U=q.eval S := q.eval_congr U S (fun r hr => run.scalar_eq_of_not_mem r
      (p.writes destination r (by intro h;subst r;exact hq hr)))
    cases hv : p.eval S with
    | false =>
      refine ⟨t+1,by simp only [size];omega,U,Runs.seq run (Runs.branch_zero
        (by simp [hu,hv,IndexedRefinement.boolNat]) (Runs.skip (Store.size_le_of_bounded hU))),hU,?_⟩
      simp [eval,hv,hu,IndexedRefinement.boolNat]
    | true =>
      obtain ⟨u,ht',T,run',hT,hout⟩ := ihq U hU hq
      refine ⟨t+(u+1),by simp only [size];omega,T,Runs.seq run (Runs.branch_nonzero
        (by simp [hu,hv,IndexedRefinement.boolNat]) run'),hT,?_⟩
      simpa [eval,hv,he] using hout
  | any p q ihp ihq =>
    have hp : destination∉p.reads := by intro h;exact hf (List.mem_append_left q.reads h)
    have hq : destination∉q.reads := by intro h;exact hf (List.mem_append_right p.reads h)
    obtain ⟨t,ht,U,run,hU,hu⟩ := ihp S hS hp
    have he : q.eval U=q.eval S := q.eval_congr U S (fun r hr => run.scalar_eq_of_not_mem r
      (p.writes destination r (by intro h;subst r;exact hq hr)))
    cases hv : p.eval S with
    | true =>
      refine ⟨t+1,by simp only [size];omega,U,Runs.seq run (Runs.branch_nonzero
        (by simp [hu,hv,IndexedRefinement.boolNat]) (Runs.skip (Store.size_le_of_bounded hU))),hU,?_⟩
      simp [eval,hv,hu,IndexedRefinement.boolNat]
    | false =>
      obtain ⟨u,ht',T,run',hT,hout⟩ := ihq U hU hq
      refine ⟨t+(u+1),by simp only [size];omega,T,Runs.seq run (Runs.branch_zero
        (by simp [hu,hv,IndexedRefinement.boolNat]) run'),hT,?_⟩
      simpa [eval,hv,he] using hout
end BooleanTest
end GroupWL.MachinePrograms.NatArrayLanguage
