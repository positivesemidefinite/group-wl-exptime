import GroupWL.MachinePrograms.NatArrayFrames
import GroupWL.IndexedRefinement

/-! Preserve a bounded tuple's digits while changing its numeric radix. -/
namespace GroupWL.MachinePrograms.NatArrayRadix
open NatArrayLanguage
open scoped BigOperators
abbrev Reg := Fin 10
abbrev Arr := Unit
abbrev Code := Program Reg Arr
set_option maxRecDepth 4096

def recode (n N v : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => v%n+N*recode n N (v/n) k

theorem recode_lt (n N v k : ℕ) (hn : 0<n) (hN : n≤N) (hv : v<n^k) : recode n N v k<N^k := by
  induction k generalizing v with
  | zero => simp [recode]
  | succ k ih =>
    have hq : v/n<n^k := by
      apply (Nat.div_lt_iff_lt_mul hn).mpr
      simpa [pow_succ,Nat.mul_comm] using hv
    have hr := Nat.mod_lt v hn
    have hi := ih (v/n) hq
    simp only [recode,pow_succ]
    nlinarith

def bodyAtoms : List (Atom Reg Arr) := [
  .divmod 9 6 2 0,.binary .mul 7 4 6,.binary .add 5 5 7,.binary .mul 4 4 1,
  .copy 2 9,.binary .sub 3 3 8]
def body : Code := atoms bodyAtoms
def loop : Code := .while 3 body

theorem loop_runs (n N v k power acc : ℕ) (S : Store Reg Arr) (B : ℕ)
    (hS : S.Bounded B) (hn : S.scalar 0=n) (hN : S.scalar 1=N) (hv : S.scalar 2=v)
    (hk : S.scalar 3=k) (hp : S.scalar 4=power) (ha : S.scalar 5=acc) (hone : S.scalar 8=1)
    (hnpos : 0<n) (hle : n≤N) (hsmall : v<n^k)
    (hacc : acc+power*recode n N v k≤B) (hpow : power*N^k≤B) :
    ∃ T,Runs (storageBound Reg Arr B) loop S (7*k+1) T ∧ T.Bounded B ∧
      T.scalar 5=acc+power*recode n N v k ∧ T.scalar 4=power*N^k ∧ T.scalar 2=0 ∧ T.scalar 3=0 := by
  induction k generalizing v power acc S with
  | zero =>
    refine ⟨S,Runs.while_zero hk (Store.size_le_of_bounded hS),hS,?_,?_,?_,hk⟩
    · simpa [recode] using ha
    · simpa using hp
    · have : v=0 := by simpa using hsmall
      simpa [this] using hv
  | succ k ih =>
    have hq : v/n<n^k := by
      apply (Nat.div_lt_iff_lt_mul hnpos).mpr
      simpa [pow_succ,Nat.mul_comm] using hsmall
    have hdigit : v%n≤recode n N v (k+1) := by simp [recode]
    have hnextacc : acc+power*(v%n)≤B :=
      (Nat.add_le_add_left (Nat.mul_le_mul_left power hdigit) acc).trans hacc
    have hterm : power*(v%n)≤B := (Nat.le_add_left _ _).trans hnextacc
    have hnextpow : power*N≤B := by
      have hNpos : 0<N := lt_of_lt_of_le hnpos hle
      have h1 : 1≤N^k := one_le_pow₀ hNpos
      simp only [pow_succ] at hpow
      nlinarith
    have hsub : k≤B := by have := hS.1 3;rw [hk] at this;omega
    have valid : ValidAtoms B bodyAtoms S := by
      simp [bodyAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar,
        hn,hN,hv,hk,hp,ha,hone,hnpos,hterm,hnextacc,hnextpow,hsub]
    obtain ⟨first,hU⟩ := atoms_runs hS bodyAtoms valid
    let U := applyAtoms bodyAtoms S
    obtain ⟨T,last,hT,accT,powerT,valueT,todoT⟩ := ih (v/n) (power*N) (acc+power*(v%n)) U hU
      (by simp [U,applyAtoms,bodyAtoms,Atom.apply,Store.setScalar,hn])
      (by simp [U,applyAtoms,bodyAtoms,Atom.apply,Store.setScalar,hN])
      (by simp [U,applyAtoms,bodyAtoms,Atom.apply,Store.setScalar,hn,hv])
      (by simp [U,applyAtoms,bodyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,hk,hone])
      (by simp [U,applyAtoms,bodyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,hp,hN])
      (by simp [U,applyAtoms,bodyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,ha,hp,hv,hn])
      (by simp [U,applyAtoms,bodyAtoms,Atom.apply,Store.setScalar,hone]) hq
      (by simpa only [recode,Nat.mul_add,Nat.mul_assoc,Nat.add_assoc] using hacc)
      (by simpa only [pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hpow)
    refine ⟨T,?_,hT,?_,?_,valueT,todoT⟩
    · have full := Runs.while_nonzero (show S.scalar 3≠0 by rw [hk];omega) first last
      convert full using 1 <;> simp [bodyAtoms] <;> omega
    · simpa only [recode,Nat.mul_add,Nat.mul_assoc,Nat.add_assoc] using accT
    · simpa only [pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using powerT

def prelude : List (Atom Reg Arr) := [.const 4 1,.const 5 0,.const 8 1]
def convert : Code := .seq (atoms prelude) loop

theorem convert_runs (n N v k : ℕ) (S : Store Reg Arr) (B : ℕ)
    (hS : S.Bounded B) (hn : S.scalar 0=n) (hN : S.scalar 1=N) (hv : S.scalar 2=v) (hk : S.scalar 3=k)
    (hnpos : 0<n) (hle : n≤N) (hsmall : v<n^k) (hroom : N^k≤B) :
    ∃ T,Runs (storageBound Reg Arr B) convert S (7*k+4) T ∧ T.Bounded B ∧
      T.scalar 5=recode n N v k ∧ T.scalar 4=N^k ∧ T.scalar 2=0 ∧ T.scalar 3=0 := by
  have hNpos : 0<N := lt_of_lt_of_le hnpos hle
  have h1 : 1≤B := (one_le_pow₀ hNpos).trans hroom
  have valid : ValidAtoms B prelude S := by simp [prelude,ValidAtoms,Atom.Valid,Atom.SmallResult,h1]
  obtain ⟨first,hU⟩ := atoms_runs hS prelude valid
  let U := applyAtoms prelude S
  obtain ⟨T,last,hT,accT,powerT,hvT,hkT⟩ := loop_runs n N v k 1 0 U B hU
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar,hn])
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar,hN])
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar,hv])
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar,hk])
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar])
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar])
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar]) hnpos hle hsmall
    (by simpa using (Nat.le_of_lt (recode_lt n N v k hnpos hle hsmall)).trans hroom)
    (by simpa using hroom)
  refine ⟨T,?_,hT,by simpa using accT,by simpa using powerT,hvT,hkT⟩
  convert Runs.seq first last using 1 <;> simp [prelude] <;> omega

theorem code_succ {n k : ℕ} (a : Fin (k+1) → Fin n) :
    (finFunctionFinEquiv a).val=(a 0).val+n*(finFunctionFinEquiv (fun i => a i.succ)).val := by
  rw [finFunctionFinEquiv_apply,Fin.sum_univ_succ]
  simp only [Fin.val_zero,pow_zero,mul_one,Fin.val_succ,finFunctionFinEquiv_apply,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [pow_succ]
  ring

theorem recode_tuple {n N k : ℕ} (hn : 0<n) (hN : n≤N) (a : Fin k → Fin n) :
    recode n N (finFunctionFinEquiv a).val k=
      (finFunctionFinEquiv (fun i => (⟨(a i).val,lt_of_lt_of_le (a i).isLt hN⟩ : Fin N))).val := by
  induction k with
  | zero => simp [recode,finFunctionFinEquiv_apply]
  | succ k ih =>
    rw [recode,code_succ a,code_succ,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (a 0).isLt,
      Nat.add_mul_div_left _ _ hn,Nat.div_eq_of_lt (a 0).isLt,zero_add,ih]
end GroupWL.MachinePrograms.NatArrayRadix
