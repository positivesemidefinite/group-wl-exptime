import GroupWL.MachinePrograms.BilinearProgram
import GroupWL.MachinePrograms.EvaluationAssemblyCorrectness

/-! The counted arithmetic evaluator computes the original bilinear map. -/
namespace GroupWL.MachinePrograms.BilinearEvaluation

open scoped BigOperators

variable (p : ℕ) [Fact p.Prime]

def vectorEquiv (n : ℕ) : (Fin n → ZMod p) ≃ Fin (p^n) :=
  (Equiv.piCongrRight (fun _ : Fin n => (ZMod.finEquiv p).toEquiv)).symm.trans finFunctionFinEquiv

def decodeVector (n : ℕ) (x : Fin (p^n)) : Fin n → ZMod p := (vectorEquiv p n).symm x

theorem decodeVector_val {n : ℕ} (x : Fin (p^n)) (i : Fin n) :
    (decodeVector p n x i).val=digit p x.val i.val := by
  cases p with
  | zero => exact (Nat.not_prime_zero (Fact.out : Nat.Prime 0)).elim
  | succ p => rfl

theorem coefficientList_read {n m : ℕ} (c : Fin n → Fin n → Fin m → ZMod p)
    (i j : Fin n) (z : Fin m) :
    read (TensorSerialization.coefficientList c) ((i.val*n+j.val)*m+z.val)=(c i j z).val := by
  rw [TensorSerialization.coefficientList,←EvaluationAssembly.entries3_nested]
  exact EvaluationAssembly.entries3_read _ i j z

theorem coefficientList_length {n m : ℕ} (c : Fin n → Fin n → Fin m → ZMod p) :
    (TensorSerialization.coefficientList c).length=n*n*m := by
  rw [TensorSerialization.coefficientList,←EvaluationAssembly.entries3_nested]
  exact EvaluationAssembly.entries3_length _

theorem coefficientList_lt {n m : ℕ} (c : Fin n → Fin n → Fin m → ZMod p) :
    ∀x∈TensorSerialization.coefficientList c,x<p := by
  intro x hx
  rw [TensorSerialization.coefficientList,←EvaluationAssembly.entries3_nested] at hx
  simp only [EvaluationAssembly.entries3,List.mem_ofFn] at hx
  obtain ⟨i,rfl⟩ := hx
  exact ZMod.val_lt _

theorem partialValue_correct {n m : ℕ} (c : Fin n → Fin n → Fin m → ZMod p)
    (x y : Fin (p^n)) (z : Fin m) :
    partialValue (TensorSerialization.coefficientList c) p n m x.val y.val z.val n =
      (Statement.coefficientBilinear p c (decodeVector p n x) (decodeVector p n y) z).val := by
  have hcast :
      (partialValue (TensorSerialization.coefficientList c) p n m x.val y.val z.val n : ZMod p) =
        Statement.coefficientBilinear p c (decodeVector p n x) (decodeVector p n y) z := by
    simp only [partialValue,ZMod.natCast_mod,Nat.cast_sum,Nat.cast_mul]
    simp_rw [←Fin.sum_univ_eq_sum_range]
    simp only [coefficientList_read,←decodeVector_val,ZMod.natCast_zmod_val]
    simp only [Statement.coefficientBilinear,LinearMap.mk₂_apply,Finset.sum_apply,
      Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hv := congrArg ZMod.val hcast
  simpa only [ZMod.val_natCast,partialValue,Nat.mod_mod] using hv

theorem evaluate_tensor_runs (T : Statement.TensorDescription p)
    (x y : Fin (p^T.inputDimension)) (z : Fin T.outputDimension)
    (S : State) (M : ℕ) (hb : S.Bounded M)
    (hp : S.scalar .modulus=p) (hn : S.scalar .inputDimension=T.inputDimension)
    (hm : S.scalar .outputDimension=T.outputDimension)
    (hx : S.scalar .left=x.val) (hy : S.scalar .right=y.val)
    (hz : S.scalar .coordinate=z.val)
    (hc : S.array .coefficients=TensorSerialization.coefficientList (T.coefficient p))
    (hroom : p^3+p≤M) :
    ∃t≤14*T.inputDimension^2+9*T.inputDimension+6,∃U,
      NatArrayLanguage.Runs (NatArrayLanguage.storageBound Reg Arr M) evaluate S t U ∧
      U.Bounded M ∧ U.scalar .total=
        (T.tensor (decodeVector p T.inputDimension x) (decodeVector p T.inputDimension y) z).val := by
  obtain ⟨t,ht,U,hr,hU,hu⟩ := evaluate_runs S M hb
    (by rw [hp]; exact (Fact.out : p.Prime).pos) (by rwa [hp]) (by simpa [hz,hm] using z.isLt)
    (by rw [hc,coefficientList_length,hn,hm])
    (by rw [hc,hp]; exact coefficientList_lt p _)
  refine ⟨t,by simpa [hn] using ht,U,hr,hU,?_⟩
  rw [hc,hp,hn,hm,hx,hy,hz,partialValue_correct,Statement.coefficientBilinear_coefficient] at hu
  exact hu

end GroupWL.MachinePrograms.BilinearEvaluation
