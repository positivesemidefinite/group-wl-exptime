import GroupWL.MachinePrograms.NatArrayPowers
import GroupWL.IndexedTuples

/-! An operational tuple-coordinate replacement from its numeric code. -/
namespace GroupWL.MachinePrograms.NatArrayLanguage
variable {R A : Type*} [DecidableEq R] [DecidableEq A] [Fintype R] [Fintype A]

def replacementPowerRegisters : Fin 5 ↪ Fin 11 :=
  ⟨fun i => ⟨i.val,by omega⟩,
    by intro i j h; exact Fin.ext (congrArg (fun x : Fin 11 => x.val) h)⟩

def replacementAtoms (reg : Fin 11 ↪ R) : List (Atom R A) := [
  .divmod (reg 5) (reg 6) (reg 9) (reg 2),
  .divmod (reg 5) (reg 6) (reg 5) (reg 0),
  .binary .mul (reg 7) (reg 6) (reg 2),
  .binary .sub (reg 8) (reg 9) (reg 7),
  .binary .mul (reg 7) (reg 10) (reg 2),
  .binary .add (reg 8) (reg 8) (reg 7)]

/-- Base 0, coordinate 1, original tuple code 9, replacement value 10,
result 8. Registers 2 through 7 are scratch. -/
def replaceTuple (reg : Fin 11 ↪ R) : Program R A :=
  .seq (power (replacementPowerRegisters.trans reg)) (atoms (replacementAtoms reg))

theorem replaceTuple_runs (reg : Fin 11 ↪ R) {n k : ℕ} (hnpos : 0<n)
    (a : Fin k → Fin n) (i : Fin k) (x : Fin n) (S : Store R A) (B : ℕ)
    (hS : S.Bounded B) (hn : S.scalar (reg 0)=n) (hi : S.scalar (reg 1)=i.val)
    (hc : S.scalar (reg 9)=(finFunctionFinEquiv a).val) (hx : S.scalar (reg 10)=x.val)
    (hB : n^k≤B) :
    ∃ T,Runs (storageBound R A B) (replaceTuple reg) S (3*i.val+10) T ∧
      T.Bounded B ∧ T.scalar (reg 8)=(finFunctionFinEquiv (Function.update a i x)).val := by
  have eqreg (i j : Fin 11) : reg i=reg j ↔ i=j := reg.injective.eq_iff
  have hpow : n^i.val≤B := (pow_le_pow_right' hnpos (Nat.le_of_lt i.isLt)).trans hB
  obtain ⟨U,powrun,hU,hpower⟩ := power_runs (replacementPowerRegisters.trans reg) S n i.val B
    hS hnpos (by simpa [replacementPowerRegisters] using hn)
    (by simpa [replacementPowerRegisters] using hi) hpow
  have hpower' : U.scalar (reg 2)=n^i.val := by simpa [replacementPowerRegisters] using hpower
  have frames (j : Fin 11) (hj2 : j≠2) (hj3 : j≠3) (hj4 : j≠4) : U.scalar (reg j)=S.scalar (reg j) := by
    apply powrun.scalar_eq_of_not_mem
    simp [power,powerLoop,powerBody,atoms,NatArrayLanguage.sequence,replacementPowerRegisters,
      Program.scalarWrites,Atom.scalarWrites,eqreg,hj2,hj3,hj4]
  have hnU : U.scalar (reg 0)=n := (frames _ (by decide) (by decide) (by decide)).trans hn
  have hcU : U.scalar (reg 9)=(finFunctionFinEquiv a).val :=
    (frames _ (by decide) (by decide) (by decide)).trans hc
  have hxU : U.scalar (reg 10)=x.val := (frames _ (by decide) (by decide) (by decide)).trans hx
  have hdigit : (finFunctionFinEquiv a).val/n^i.val%n=(a i).val := by
    change IndexedRefinement.digit n (finFunctionFinEquiv a).val i.val=(a i).val
    rw [IndexedRefinement.digit_equiv,Equiv.symm_apply_apply]
  have hcode : (finFunctionFinEquiv a).val≤B := (Nat.le_of_lt (finFunctionFinEquiv a).isLt).trans hB
  have hremoved : (a i).val*n^i.val≤B := by
    have hd := Nat.mul_le_mul_right (n^i.val) (Nat.mod_le ((finFunctionFinEquiv a).val/n^i.val) n)
    rw [hdigit] at hd
    exact (hd.trans (Nat.div_mul_le_self _ _)).trans hcode
  have hnew : (finFunctionFinEquiv a).val-(a i).val*n^i.val+x.val*n^i.val≤B := by
    rw [← IndexedTuples.code_update]
    exact (Nat.le_of_lt (finFunctionFinEquiv (Function.update a i x)).isLt).trans hB
  have hslot : x.val*n^i.val≤B := by omega
  have hvalid : ValidAtoms B (replacementAtoms reg) U := by
    simp only [replacementAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,Function.update_apply,eqreg]
    simp +decide only [if_true,if_false,hnU,hpower',hcU,hxU,hdigit]
    refine ⟨⟨reg.injective.ne (by decide),pow_pos hnpos _⟩,trivial,
      ⟨reg.injective.ne (by decide),hnpos⟩,trivial,trivial,hremoved,trivial,?_,trivial,hslot,trivial,hnew,trivial⟩
    omega
  obtain ⟨arith,hT⟩ := atoms_runs hU (replacementAtoms reg) hvalid
  refine ⟨applyAtoms (replacementAtoms reg) U,?_,hT,?_⟩
  · have run := Runs.seq powrun arith
    convert run using 1 <;> simp [replacementAtoms] <;> omega
  · simp +decide only [applyAtoms,replacementAtoms,List.foldl_cons,List.foldl_nil,Atom.apply,BinaryOp.eval,
      Store.setScalar,Function.update_apply,eqreg,if_true,if_false,hnU,hpower',hcU,hxU,hdigit]
    exact (IndexedTuples.code_update a i x).symm

end GroupWL.MachinePrograms.NatArrayLanguage
