import GroupWL.MachinePrograms.NatArrayExpressions

/-! Exact source instruction bounds for the read-only expression compiler. -/
namespace GroupWL.MachinePrograms.NatArrayExpressions
open NatArrayLanguage
set_option maxHeartbeats 4000000
variable {R A : Type*} [DecidableEq R] [DecidableEq A] [Fintype R] [Fintype A]

def Fresh (e : Expr R A) (d : R) (ss : List R) : Prop :=
  ∀r∈e.variables,r∉d::ss

theorem run_inputs (compiled observed : Expr R A) (d : R) (ss : List R)
    (fresh : Fresh observed d ss) {M t : ℕ} {S U : Store R A}
    (run : Runs M (compiled.compile d ss) S t U) :
    U.array=S.array ∧ ∀r∈observed.variables,U.scalar r=S.scalar r := by
  constructor
  · funext a
    exact run.array_eq_of_not_mem a (by simp [compiled.compile_arrays])
  · intro r hr
    apply run.scalar_eq_of_not_mem r
    intro hw
    have hm := compiled.compile_writes d ss hw
    exact fresh r hr (List.mem_toFinset.mp hm)

theorem Op.atom_correct (op : Op) (d t : R) (S : Store R A) (M : ℕ)
    (bounded : S.Bounded M) (distinct : d≠t) (valid : op.valid (S.scalar t))
    (small : op.eval (S.scalar d) (S.scalar t)≤M) :
    Runs (storageBound R A M) (.atom (op.atom d t)) S 1 ((op.atom d t).apply S) ∧
      ((op.atom d t).apply S).Bounded M ∧
      ((op.atom d t).apply S).scalar d=op.eval (S.scalar d) (S.scalar t) := by
  have hv : (op.atom (A:=A) d t).Valid S := by
    cases op <;> simp_all [Op.atom,Op.valid,Atom.Valid,Ne.symm distinct]
  have hs : (op.atom d t).SmallResult M S := by
    cases op <;> simp_all [Op.atom,Op.eval,Atom.SmallResult]
  refine ⟨atom_runs bounded _ hv hs,Atom.apply_bounded bounded _ hs,?_⟩
  cases op <;> simp [Op.atom,Op.eval,Atom.apply,Store.setScalar,distinct]

theorem Expr.compile_runs (e : Expr R A) (d : R) (ss : List R) (S : Store R A) (M : ℕ)
    (bounded : S.Bounded M) (safe : e.Safe M S) (room : e.need≤ss.length)
    (distinct : (d::ss).Nodup) (fresh : Fresh e d ss) :
    ∃t≤e.cost,∃U,Runs (storageBound R A M) (e.compile d ss) S t U ∧
      U.Bounded M ∧ U.scalar d=e.eval S := by
  induction e generalizing d ss S with
  | const n=>
    exact ⟨1,le_rfl,_,atom_runs bounded _ trivial safe,Atom.apply_bounded bounded _ safe,by simp [Atom.apply,Expr.eval]⟩
  | scalar r=>
    exact ⟨1,le_rfl,_,atom_runs bounded _ trivial trivial,Atom.apply_bounded bounded _ trivial,by simp [Atom.apply,Expr.eval]⟩
  | read a i ih=>
    obtain ⟨t,ht,U,run,hU,out⟩ := ih d ss S bounded safe.1 room distinct fresh
    have arrays := (run_inputs i i d ss fresh run).1
    have valid : (Atom.read d a d).Valid U := by
      change U.scalar d<(U.array a).length
      rw [out,arrays]
      exact safe.2
    have last := atom_runs hU (Atom.read d a d) valid trivial
    refine ⟨t+1,by simpa [Expr.cost] using Nat.add_le_add_right ht 1,_,.seq run last,
      Atom.apply_bounded hU _ trivial,?_⟩
    simp only [Atom.apply,Store.setScalar_same,Expr.eval,out,arrays]
  | binary op a b ia ib=>
    cases ss with
    | nil=>simp [Expr.need] at room
    | cons q ss=>
      have ra : a.need≤(q::ss).length := le_trans (le_max_left _ _) room
      have rb : b.need≤ss.length := by change max a.need (b.need+1)≤ss.length+1 at room; omega
      have fa : Fresh a d (q::ss) := fun r hr=>fresh r (by simp [Expr.variables,hr])
      have fb : Fresh b d (q::ss) := fun r hr=>fresh r (by simp [Expr.variables,hr])
      have fb' : Fresh b q ss := by
        intro r hr hm
        exact fb r hr (List.mem_cons_of_mem d hm)
      obtain ⟨ta,hta,U,runa,hU,outa⟩ := ia d (q::ss) S bounded safe.1 ra distinct fa
      have inputs := run_inputs a b d (q::ss) fb runa
      have bsafe : b.Safe M U := (b.safe_congr M inputs.1 inputs.2).mpr safe.2.1
      have beval : b.eval U=b.eval S := b.eval_congr inputs.1 inputs.2
      have nodup := List.nodup_cons.mp distinct
      obtain ⟨tb,htb,V,runb,hV,outb⟩ := ib q ss U hU bsafe rb nodup.2 fb'
      have dd : d≠q := by intro h; exact nodup.1 (by simp [h])
      have preserve : V.scalar d=U.scalar d := by
        apply runb.scalar_eq_of_not_mem d
        intro h
        exact nodup.1 (List.mem_toFinset.mp (b.compile_writes q ss h))
      have vd : V.scalar d=a.eval S := preserve.trans outa
      have vq : V.scalar q=b.eval S := outb.trans beval
      obtain ⟨last,hW,out⟩ := Op.atom_correct op d q V M hV dd
        (by rw [vq]; exact safe.2.2.1) (by rw [vd,vq]; exact safe.2.2.2)
      refine ⟨ta+(tb+1),by simp only [Expr.cost]; omega,_,.seq runa (.seq runb last),hW,?_⟩
      simpa only [vd,vq,Expr.eval] using out
  | branch c a b ic ia ib=>
      have rc : c.need≤ss.length := le_trans (le_max_left _ _) room
      have ra : a.need≤ss.length := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) room
      have rb : b.need≤ss.length := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) room
      have fc : Fresh c d ss := fun r hr=>fresh r (by simp [Expr.variables,hr])
      have fa : Fresh a d ss := fun r hr=>fresh r (by simp [Expr.variables,hr])
      have fb : Fresh b d ss := fun r hr=>fresh r (by simp [Expr.variables,hr])
      obtain ⟨tc,htc,U,runc,hU,outc⟩ := ic d ss S bounded safe.1 rc distinct fc
      by_cases hz : c.eval S=0
      · have inputs := run_inputs c b d ss fb runc
        have bsafe : b.Safe M U := (b.safe_congr M inputs.1 inputs.2).mpr (by simpa [Expr.Safe,hz] using safe.2)
        obtain ⟨tb,htb,V,runb,hV,outb⟩ := ib d ss U hU bsafe rb distinct fb
        refine ⟨tc+(tb+1),by simp only [Expr.cost]; omega,V,
          .seq runc (.branch_zero (outc.trans hz) runb),hV,?_⟩
        rw [Expr.eval,hz,if_pos rfl]
        exact outb.trans (b.eval_congr inputs.1 inputs.2)
      · have inputs := run_inputs c a d ss fa runc
        have asafe : a.Safe M U := (a.safe_congr M inputs.1 inputs.2).mpr (by simpa [Expr.Safe,hz] using safe.2)
        obtain ⟨ta,hta,V,runa,hV,outa⟩ := ia d ss U hU asafe ra distinct fa
        refine ⟨tc+(ta+1),by simp only [Expr.cost]; omega,V,
          .seq runc (.branch_nonzero (by rwa [outc]) runa),hV,?_⟩
        rw [Expr.eval,if_neg hz]
        exact outa.trans (a.eval_congr inputs.1 inputs.2)

end GroupWL.MachinePrograms.NatArrayExpressions
