import GroupWL.MachinePrograms.ExtensionTableAssembly

/-! The numerically constructed operation is precisely the extension
operation used by the exhaustive p-group decoder. -/
namespace GroupWL.MachinePrograms.ExtensionTablePrograms

variable {p n : ℕ}

def encodePair {K : Type*} (e : K ≃ Fin n) (a : Fin p × K) : Fin (p*n) :=
  finProdFinEquiv (a.1,e a.2)

def encodedMap {K : Type*} (e : K ≃ Fin n) (θ : K → K) : Fin n → Fin n :=
  fun x => e (θ (e.symm x))

theorem encodedMap_iterate {K : Type*} (e : K ≃ Fin n) (θ : K → K) (j : ℕ) (x : K) :
    (encodedMap e θ)^[j] (e x)=e (θ^[j] x) := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [Function.iterate_succ_apply',ih,encodedMap,Equiv.symm_apply_apply]

theorem operation_code (hp : 0<p) (mul : Fin n → Fin n → Fin n)
    (θ : Fin n → Fin n) (c e : Fin n) (a b : Fin p × Fin n) :
    operation hp mul θ c e (finProdFinEquiv a) (finProdFinEquiv b)=
      finProdFinEquiv (⟨(a.1.val+b.1.val)%p,Nat.mod_lt _ hp⟩,
        mul (mul (if (a.1.val+b.1.val)/p=0 then e else c) (θ^[b.1.val] a.2)) b.2) := by
  simp only [operation,Equiv.symm_apply_apply]

theorem quotient_le_one (hp : 0<p) (a b : Fin p) : (a.val+b.val)/p≤1 := by
  have hlt : a.val+b.val<2*p := by have := a.isLt; have := b.isLt; omega
  have hdiv : (a.val+b.val)/p<2 := (Nat.div_lt_iff_lt_mul hp).mpr hlt
  omega

theorem operation_extensionMul {K : Type*} [Monoid K] (hp : 0<p)
    (e : K ≃ Fin n) (θ : K → K) (c : K) (a b : Fin p × K) :
    operation hp (GroupInitial.encodedMul e) (encodedMap e θ) (e c) (e 1)
      (encodePair e a) (encodePair e b)=
      encodePair e (PGroupDecomposition.extensionMul p hp θ c a b) := by
  rw [encodePair,encodePair,operation_code]
  have hfactor : (if (a.1.val+b.1.val)/p=0 then e 1 else e c)=e (c^((a.1.val+b.1.val)/p)) := by
    have hq := quotient_le_one hp a.1 b.1
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hq with h0 | h1
    · simp [h0]
    · simp [h1]
  simp only [hfactor,encodedMap_iterate,GroupInitial.encodedMul,Equiv.symm_apply_apply]
  rfl

end GroupWL.MachinePrograms.ExtensionTablePrograms
