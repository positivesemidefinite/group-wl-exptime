import GroupWL.MachinePrograms.NatArrayFrames

/-! Variable natural powers computed by a finite arithmetic loop. -/
namespace GroupWL.MachinePrograms.NatArrayLanguage
variable {R A : Type*} [DecidableEq R] [DecidableEq A] [Fintype R] [Fintype A]

def powerBody (reg : Fin 5 ↪ R) : Program R A := atoms [
  .binary .mul (reg 2) (reg 2) (reg 0),
  .binary .sub (reg 3) (reg 3) (reg 4)]

def powerLoop (reg : Fin 5 ↪ R) : Program R A := .while (reg 3) (powerBody reg)

theorem powerLoop_runs (reg : Fin 5 ↪ R) (a e acc B : ℕ) (ha : 0<a) :
    ∀ S : Store R A, S.Bounded B → S.scalar (reg 0)=a → S.scalar (reg 2)=acc →
      S.scalar (reg 3)=e → S.scalar (reg 4)=1 → acc*a^e≤B →
      Runs (storageBound R A B) (powerLoop reg) S (3*e+1)
        ((S.setScalar (reg 2) (acc*a^e)).setScalar (reg 3) 0) ∧
        ((S.setScalar (reg 2) (acc*a^e)).setScalar (reg 3) 0).Bounded B := by
  have eqreg (i j : Fin 5) : reg i=reg j ↔ i=j := reg.injective.eq_iff
  induction e generalizing acc with
  | zero =>
    intro S hS hbase hacc he hone hbig
    have hfinal : (S.setScalar (reg 2) (acc*a^0)).setScalar (reg 3) 0=S := by
      apply Store.ext
      · intro r
        by_cases hr : r=reg 3
        · subst r; simp [he]
        · by_cases hr' : r=reg 2
          · subst r; simp [eqreg,hacc]
          · simp [Store.setScalar,hr,hr']
      · intro r; rfl
    rw [hfinal]
    exact ⟨Runs.while_zero he (Store.size_le_of_bounded hS),hS⟩
  | succ e ih =>
    intro S hS hbase hacc he hone hbig
    have hpow : 1≤a^e := one_le_pow₀ ha
    have hprod : acc*a≤B := by rw [pow_succ] at hbig; nlinarith
    have hvalid : ValidAtoms B
        [.binary .mul (reg 2) (reg 2) (reg 0),.binary .sub (reg 3) (reg 3) (reg 4)] S := by
      simp only [ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar]
      simp [eqreg,hbase,hacc,he,hone,hprod,show e≤B by have := hS.1 (reg 3); omega]
    obtain ⟨body,hT⟩ := atoms_runs hS _ hvalid
    let T := (S.setScalar (reg 2) (acc*a)).setScalar (reg 3) e
    have hbody : Runs (storageBound R A B) (powerBody reg) S 2 T := by
      simpa [powerBody,T,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,eqreg,hbase,hacc,he,hone]
        using body
    have hbT : T.Bounded B := (hS.setScalar _ hprod).setScalar _ (by have := hS.1 (reg 3); omega)
    obtain ⟨rest,hU⟩ := ih (acc*a) T hbT (by simp [T,eqreg,hbase])
      (by simp [T,eqreg]) (by simp [T]) (by simp [T,eqreg,hone])
      (by simpa [pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hbig)
    have hfinal : (T.setScalar (reg 2) ((acc*a)*a^e)).setScalar (reg 3) 0=
        (S.setScalar (reg 2) (acc*a^(e+1))).setScalar (reg 3) 0 := by
      apply Store.ext
      · intro r
        by_cases hr : r=reg 3
        · subst r; simp
        · by_cases hr' : r=reg 2
          · subst r; simp [eqreg,pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
          · simp [T,Store.setScalar,hr,hr']
      · intro r; rfl
    rw [hfinal] at rest hU
    refine ⟨?_,hU⟩
    have run := Runs.while_nonzero (by omega : S.scalar (reg 3)≠0) hbody rest
    convert run using 1 <;> omega

def power (reg : Fin 5 ↪ R) : Program R A := .seq
  (atoms [.const (reg 2) 1,.const (reg 4) 1,.copy (reg 3) (reg 1)]) (powerLoop reg)

theorem power_runs (reg : Fin 5 ↪ R) (S : Store R A) (a e B : ℕ)
    (hS : S.Bounded B) (ha : 0<a) (hbase : S.scalar (reg 0)=a)
    (hexp : S.scalar (reg 1)=e) (hbig : a^e≤B) :
    ∃ T,Runs (storageBound R A B) (power reg) S (3*e+4) T ∧ T.Bounded B ∧
      T.scalar (reg 2)=a^e := by
  have eqreg (i j : Fin 5) : reg i=reg j ↔ i=j := reg.injective.eq_iff
  have h1 : 1≤B := (one_le_pow₀ ha).trans hbig
  have hvalid : ValidAtoms B [.const (reg 2) 1,.const (reg 4) 1,.copy (reg 3) (reg 1)] S := by
    simp [ValidAtoms,Atom.Valid,Atom.SmallResult,h1]
  obtain ⟨first,hT⟩ := atoms_runs hS _ hvalid
  let T := applyAtoms [.const (reg 2) 1,.const (reg 4) 1,.copy (reg 3) (reg 1)] S
  have hbaseT : T.scalar (reg 0)=a := by simp [T,applyAtoms,Atom.apply,Store.setScalar,eqreg,hbase]
  have haccT : T.scalar (reg 2)=1 := by simp [T,applyAtoms,Atom.apply,Store.setScalar,eqreg]
  have heT : T.scalar (reg 3)=e := by simp [T,applyAtoms,Atom.apply,Store.setScalar,eqreg,hexp]
  have h1T : T.scalar (reg 4)=1 := by simp [T,applyAtoms,Atom.apply,Store.setScalar,eqreg]
  obtain ⟨rest,hU⟩ := powerLoop_runs reg a e 1 B ha T hT hbaseT haccT heT h1T (by simpa using hbig)
  refine ⟨_,?_,hU,?_⟩
  · have run := Runs.seq first rest
    convert run using 1 <;> simp <;> omega
  · simp [eqreg]

end GroupWL.MachinePrograms.NatArrayLanguage
