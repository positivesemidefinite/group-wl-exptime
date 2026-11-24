import GroupWL.MachinePrograms.NatArrayComponents
import GroupWL.MachinePrograms.NatArrayFrames

/-! The actual linear dimension cap used before enumerating tuple universes. -/
namespace GroupWL.MachinePrograms.TensorClamp
open NatArrayLanguage
variable {R A : Type*} [DecidableEq R] [DecidableEq A] [Fintype R] [Fintype A]

def prepare (r : Fin 7 ↪ R) : List (Atom R A) := [
  .const (r 3) 10,.binary .add (r 4) (r 0) (r 1),
  .binary .add (r 5) (r 4) (r 3),.binary .lt (r 6) (r 5) (r 2)]
def program (r : Fin 7 ↪ R) : NatArrayLanguage.Program R A :=
  .seq (atoms (prepare r)) (.branch (r 6) (.atom (.copy (r 2) (r 5))) .skip)

theorem program_runs (r : Fin 7 ↪ R) (S : Store R A) (B n m k : ℕ)
    (bounded : S.Bounded B) (hn : S.scalar (r 0)=n) (hm : S.scalar (r 1)=m)
    (hk : S.scalar (r 2)=k) (room : n+m+10≤B) :
    ∃t≤6,∃T,Runs (storageBound R A B) (program r) S t T ∧ T.Bounded B ∧
      T.scalar (r 2)=min k (n+m+10) := by
  have h1 : 1≤B := by omega
  have valid : ValidAtoms B (prepare r) S := by
    simp [prepare,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar,r.injective.eq_iff,hn,hm]
    refine ⟨by omega,by omega,room,?_⟩
    split_ifs <;> omega
  obtain ⟨first,hU⟩ := atoms_runs bounded (prepare r) valid
  let U := applyAtoms (prepare r) S
  have uk : U.scalar (r 2)=k := by simp [U,applyAtoms,prepare,Atom.apply,Store.setScalar,r.injective.eq_iff,hk]
  have cap : U.scalar (r 5)=n+m+10 := by
    simp [U,applyAtoms,prepare,Atom.apply,BinaryOp.eval,Store.setScalar,r.injective.eq_iff,hn,hm]
  have flag : U.scalar (r 6)=if n+m+10<k then 1 else 0 := by
    simp [U,applyAtoms,prepare,Atom.apply,BinaryOp.eval,Store.setScalar,r.injective.eq_iff,hn,hm,hk]
  by_cases h : n+m+10<k
  · have last := atom_runs hU (.copy (r 2) (r 5)) trivial trivial
    have hT := (Atom.copy (r 2) (r 5) : Atom R A).apply_bounded hU trivial
    refine ⟨6,le_rfl,_,.seq first (.branch_nonzero (by change U.scalar (r 6)≠0; simp [flag,h]) last),hT,?_⟩
    simp only [Atom.apply,Store.setScalar,Function.update_self,min_eq_right (Nat.le_of_lt h)]
    exact cap
  · refine ⟨5,by omega,U,.seq first (.branch_zero (by change U.scalar (r 6)=0; simp [flag,h]) (.skip (Store.size_le_of_bounded hU))),hU,?_⟩
    simpa [min_eq_left (by omega : k≤n+m+10)] using uk

end GroupWL.MachinePrograms.TensorClamp
