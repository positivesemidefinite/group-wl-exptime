import GroupWL.MachinePrograms.NatArrayCountedLoops
import GroupWL.MachinePrograms.NatArrayFrames

/-! Exponentiation by a counted loop of the concrete array language. -/
namespace GroupWL.MachinePrograms.NatArrayPower

open NatArrayLanguage
variable {Reg Arr : Type*} [DecidableEq Reg] [DecidableEq Arr]
  [Fintype Reg] [Fintype Arr]

/-- Slots: base, exponent, result, remaining iterations, constant one. -/
def step (r : Fin 5 ↪ Reg) : NatArrayLanguage.Program Reg Arr :=
  atoms [.binary .mul (r 2) (r 2) (r 0),.binary .sub (r 3) (r 3) (r 4)]

def program (r : Fin 5 ↪ Reg) : NatArrayLanguage.Program Reg Arr :=
  .seq (atoms [.const (r 4) 1,.const (r 2) 1,.copy (r 3) (r 1)]) (.while (r 3) (step r))

theorem program_runs (r : Fin 5 ↪ Reg) (S : Store Reg Arr) (b n M : ℕ)
    (hb : S.Bounded M) (hbase : S.scalar (r 0)=b) (hexp : S.scalar (r 1)=n)
    (hpositive : 1≤b) (hroom : b^n≤M) :
    ∃T t,t≤3*n+4 ∧ Runs (storageBound Reg Arr M) (program r) S t T ∧
      T.Bounded M ∧ T.scalar (r 0)=b ∧ T.scalar (r 1)=n ∧
      T.scalar (r 2)=b^n ∧ T.scalar (r 3)=0 ∧ T.scalar (r 4)=1 := by
  have hM : 1≤M := (one_le_pow₀ hpositive).trans hroom
  let as : List (Atom Reg Arr) := [.const (r 4) 1,.const (r 2) 1,.copy (r 3) (r 1)]
  let U := applyAtoms as S
  obtain ⟨first,hU⟩ := atoms_runs hb as (by simp [as,ValidAtoms,Atom.Valid,Atom.SmallResult,hM])
  let I : ℕ → Store Reg Arr → Prop := fun i T =>
    T.Bounded M ∧ T.scalar (r 0)=b ∧ T.scalar (r 1)=n ∧ T.scalar (r 4)=1 ∧
      T.scalar (r 2)=b^i ∧ T.scalar (r 3)=n-i
  have start : I 0 U := by
    refine ⟨hU,?_,?_,?_,?_,?_⟩ <;>
      simp [U,applyAtoms,as,Atom.apply,Store.setScalar,r.injective.eq_iff,hbase,hexp]
  have next : ∀i<n,∀T,I i T → ∃t≤2,∃V,Runs (storageBound Reg Arr M) (step r) T t V ∧ I (i+1) V := by
    intro i hi T hT
    rcases hT with ⟨hT,htbase,htexp,htone,htpow,htrem⟩
    have hpow : b^(i+1)≤M := (pow_le_pow_right' hpositive (by omega)).trans hroom
    let bs : List (Atom Reg Arr) := [.binary .mul (r 2) (r 2) (r 0),.binary .sub (r 3) (r 3) (r 4)]
    have valid : ValidAtoms M bs T := by
      simp [bs,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
        Store.setScalar,r.injective.eq_iff,htbase,htpow,htrem,htone,←pow_succ]
      have hn : n≤M := by simpa [htexp] using hT.1 (r 1)
      exact ⟨hpow,by omega⟩
    obtain ⟨run,hV⟩ := atoms_runs hT bs valid
    refine ⟨2,le_rfl,applyAtoms bs T,run,hV,?_,?_,?_,?_,?_⟩ <;>
      simp [applyAtoms,bs,Atom.apply,BinaryOp.eval,Store.setScalar,r.injective.eq_iff,
        htbase,htexp,htpow,htrem,htone,pow_succ,Nat.sub_sub]
  have active : ∀i<n,∀T,I i T → T.scalar (r 3)≠0 := by
    intro i hi T hT
    have := hT.2.2.2.2.2
    omega
  have done : ∀T,I n T → T.scalar (r 3)=0 ∧ T.size≤storageBound Reg Arr M := by
    intro T hT
    exact ⟨by have := hT.2.2.2.2.2; omega,Store.size_le_of_bounded hT.1⟩
  obtain ⟨t,ht,T,last,hT⟩ := while_runs_invariant (storageBound Reg Arr M) (r 3) (step r)
    I n 2 next active done U start
  refine ⟨T,3+t,by omega,.seq first last,hT.1,hT.2.1,hT.2.2.1,hT.2.2.2.2.1,?_,hT.2.2.2.1⟩
  have := hT.2.2.2.2.2
  omega

end GroupWL.MachinePrograms.NatArrayPower
