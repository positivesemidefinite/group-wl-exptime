import GroupWL.MachinePrograms.BilinearSemantics
import Mathlib.Logic.Equiv.Fin.Basic

/-! Exact base-p indices for the tensor group and its multiplication table. -/
namespace GroupWL.MachinePrograms.TensorGroupCode

open scoped BigOperators
open BilinearEvaluation

def multiplicationDigit (C : List ℕ) (p n m half g h i : ℕ) : ℕ :=
  (digit p g i+digit p h i+
    if i<n then 0 else half*partialValue C p n m g h (i-n) n)%p

def codePrefix (p : ℕ) (d : ℕ → ℕ) (i : ℕ) : ℕ := ∑j ∈ Finset.range i,d j*p^j

@[simp] theorem codePrefix_zero (p : ℕ) (d : ℕ → ℕ) : codePrefix p d 0=0 := by simp [codePrefix]
theorem codePrefix_succ (p : ℕ) (d : ℕ → ℕ) (i : ℕ) :
    codePrefix p d (i+1)=codePrefix p d i+d i*p^i := by simp [codePrefix,Finset.sum_range_succ]

theorem codePrefix_lt (p : ℕ) (d : ℕ → ℕ) (i : ℕ) (hp : 0<p)
    (hd : ∀ j < i, d j < p) : codePrefix p d i<p^i := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hi := ih (fun j hj => hd j (by omega))
    have hlast := hd i (by omega)
    rw [codePrefix_succ,pow_succ]
    nlinarith

def multiplication (C : List ℕ) (p n m half g h : ℕ) : ℕ :=
  codePrefix p (multiplicationDigit C p n m half g h) (n+m)

theorem multiplication_lt (C : List ℕ) (p n m half g h : ℕ) (hp : 0<p) :
    multiplication C p n m half g h<p^(n+m) :=
  codePrefix_lt _ _ _ hp (fun _ _ => Nat.mod_lt _ hp)

variable (p : ℕ) [Fact p.Prime]

def natVector (n value : ℕ) : Fin n → ZMod p := fun i => (digit p value i.val : ZMod p)

theorem partialValue_nat_correct {n m : ℕ} (c : Fin n → Fin n → Fin m → ZMod p)
    (x y : ℕ) (z : Fin m) :
    partialValue (TensorSerialization.coefficientList c) p n m x y z.val n =
      (Statement.coefficientBilinear p c (natVector p n x) (natVector p n y) z).val := by
  have hcast :
      (partialValue (TensorSerialization.coefficientList c) p n m x y z.val n : ZMod p)=
        Statement.coefficientBilinear p c (natVector p n x) (natVector p n y) z := by
    simp only [partialValue,ZMod.natCast_mod,Nat.cast_sum,Nat.cast_mul]
    simp_rw [←Fin.sum_univ_eq_sum_range]
    simp only [coefficientList_read,ZMod.natCast_zmod_val]
    simp only [Statement.coefficientBilinear,LinearMap.mk₂_apply,Finset.sum_apply,
      Pi.smul_apply,smul_eq_mul,Finset.mul_sum,natVector]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simpa only [ZMod.val_natCast,partialValue,Nat.mod_mod] using congrArg ZMod.val hcast

def groupEquiv (T : Statement.TensorDescription p) : T.Carrier ≃ Fin (p^(T.inputDimension+T.outputDimension)) :=
  TensorGroup.equivProd.trans ((Fin.appendEquiv T.inputDimension T.outputDimension).trans
    (vectorEquiv p (T.inputDimension+T.outputDimension)))

theorem vectorEquiv_val {n : ℕ} (f : Fin n → ZMod p) :
    (vectorEquiv p n f).val=∑i,(f i).val*p^i.val := by
  cases p with
  | zero => exact (Nat.not_prime_zero (Fact.out : Nat.Prime 0)).elim
  | succ p => rfl

theorem groupEquiv_val (T : Statement.TensorDescription p) (g : T.Carrier) :
    (groupEquiv p T g).val=∑i : Fin (T.inputDimension+T.outputDimension),
      (Fin.append g.fst g.snd i).val*p^i.val := vectorEquiv_val p _

theorem groupEquiv_fst_val (T : Statement.TensorDescription p)
    (g : Fin (p^(T.inputDimension+T.outputDimension))) (i : Fin T.inputDimension) :
    (((groupEquiv p T).symm g).fst i).val = digit p g.val i.val := by
  exact decodeVector_val p g (Fin.castAdd T.outputDimension i)

theorem groupEquiv_snd_val (T : Statement.TensorDescription p)
    (g : Fin (p^(T.inputDimension+T.outputDimension))) (i : Fin T.outputDimension) :
    (((groupEquiv p T).symm g).snd i).val = digit p g.val (T.inputDimension+i.val) := by
  exact decodeVector_val p g (Fin.natAdd T.inputDimension i)

theorem natVector_fst (T : Statement.TensorDescription p)
    (g : Fin (p^(T.inputDimension+T.outputDimension))) :
    natVector p T.inputDimension g.val=((groupEquiv p T).symm g).fst := by
  funext i
  rw [natVector,←groupEquiv_fst_val,ZMod.natCast_zmod_val]

theorem multiplicationDigit_correct (T : Statement.TensorDescription p)
    (g h : Fin (p^(T.inputDimension+T.outputDimension)))
    (i : Fin (T.inputDimension+T.outputDimension)) :
    multiplicationDigit (TensorSerialization.coefficientList (T.coefficient p)) p T.inputDimension
        T.outputDimension ((2 : ZMod p)⁻¹).val g.val h.val i.val =
      (Fin.append (((groupEquiv p T).symm g)*((groupEquiv p T).symm h)).fst
        (((groupEquiv p T).symm g)*((groupEquiv p T).symm h)).snd i).val := by
  induction i using Fin.addCases with
  | left i =>
    simp only [multiplicationDigit,Fin.val_castAdd,i.isLt,if_pos,Nat.add_zero,Fin.append_left,
      TensorGroup.mul_fst,Pi.add_apply,ZMod.val_add,groupEquiv_fst_val]
  | right i =>
    have hi : ¬T.inputDimension+i.val<T.inputDimension := by omega
    simp only [multiplicationDigit,Fin.val_natAdd,hi,if_false,Nat.add_sub_cancel_left,
      Fin.append_right,TensorGroup.mul_snd,Pi.add_apply,Pi.smul_apply,smul_eq_mul,ZMod.val_add,ZMod.val_mul,
      groupEquiv_snd_val]
    rw [partialValue_nat_correct,natVector_fst,natVector_fst,Statement.coefficientBilinear_coefficient]
    exact Nat.add_mod _ _ _

theorem multiplication_correct (T : Statement.TensorDescription p)
    (g h : Fin (p^(T.inputDimension+T.outputDimension))) :
    multiplication (TensorSerialization.coefficientList (T.coefficient p)) p T.inputDimension
        T.outputDimension ((2 : ZMod p)⁻¹).val g.val h.val =
      (groupEquiv p T (((groupEquiv p T).symm g)*((groupEquiv p T).symm h))).val := by
  rw [multiplication,codePrefix,←Fin.sum_univ_eq_sum_range,groupEquiv_val]
  apply Finset.sum_congr rfl
  intro i hi
  rw [multiplicationDigit_correct]

end GroupWL.MachinePrograms.TensorGroupCode
