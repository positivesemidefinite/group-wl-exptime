import GroupWL.CachedElimination
import GroupWL.MachinePrograms.MatrixArithmetic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! The array multiplication program realizes multiplication of actual
finite-field coefficient matrices used by the kernel construction. -/
namespace GroupWL.MatrixEncoding

open CachedElimination
open scoped BigOperators
open MachinePrograms.MatrixArithmetic

variable {p m n k : ℕ} [NeZero p]

def word (A : MatrixData (F:=ZMod p) m n) : List ℕ :=
  List.ofFn (fun z : Fin (m*n) =>
    let ij := finProdFinEquiv.symm z
    A[ij.1][ij.2].val)

@[simp] theorem word_length (A : MatrixData (F:=ZMod p) m n) : (word A).length=m*n :=
  List.length_ofFn

theorem word_read (A : MatrixData (F:=ZMod p) m n) (i : Fin m) (j : Fin n) :
    read (word A) (i.val*n+j.val) = A[i][j].val := by
  have h : i.val*n+j.val < m*n := by
    simpa [Nat.mul_comm,Nat.add_comm] using (finProdFinEquiv (i,j)).isLt
  simp only [MachinePrograms.MatrixArithmetic.read,word,List.getElem?_ofFn,dif_pos h,Option.getD_some]
  have he : (⟨i.val*n+j.val,h⟩ : Fin (m*n)) = finProdFinEquiv (i,j) := by
    apply Fin.ext
    simp [Nat.mul_comm,Nat.add_comm]
  simp only [he,Equiv.symm_apply_apply]

theorem word_values_lt (A : MatrixData (F:=ZMod p) m n) :
    ∀ x∈word A,x<p := by
  intro x hx
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  exact ZMod.val_lt _

def product (A : MatrixData (F:=ZMod p) m n) (B : MatrixData (F:=ZMod p) n k) :
    MatrixData (F:=ZMod p) m k :=
  Vector.ofFn (fun i => Vector.ofFn (fun j => ∑ l : Fin n, A[i][l]*B[l][j]))

@[simp] theorem product_entry (A : MatrixData (F:=ZMod p) m n)
    (B : MatrixData (F:=ZMod p) n k) (i : Fin m) (j : Fin k) :
    (product A B)[i][j] = ∑ l : Fin n, A[i][l]*B[l][j] := by simp [product]

theorem partialDot_correct (A : MatrixData (F:=ZMod p) m n)
    (B : MatrixData (F:=ZMod p) n k) (i : Fin m) (j : Fin k) :
    partialDot (word A) (word B) n k i.val j.val p n = (product A B)[i][j].val := by
  have hs : ((∑ l ∈ Finset.range n,
      read (word A) (i.val*n+l)*read (word B) (l*k+j.val) : ℕ) : ZMod p) =
      ∑ l : Fin n, A[i][l]*B[l][j] := by
    rw [Nat.cast_sum,←Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro l hl
    rw [word_read A i l,word_read B l j,Nat.cast_mul]
    simp
  have he := congrArg ZMod.val hs
  simpa only [ZMod.val_natCast,partialDot,product_entry] using he

theorem word_product (A : MatrixData (F:=ZMod p) m n) (B : MatrixData (F:=ZMod p) n k) :
    word (product A B) = List.ofFn (fun z : Fin (m*k) =>
      partialDot (word A) (word B) n k (z.val/k) (z.val%k) p n) := by
  change List.ofFn (fun z : Fin (m*k) =>
    (product A B)[(finProdFinEquiv.symm z).1][(finProdFinEquiv.symm z).2].val) = _
  congr 1
  funext z
  exact (partialDot_correct A B (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2).symm

section Prime
variable [Fact p.Prime]

theorem product_toLinear (A : MatrixData (F:=ZMod p) m n) (B : MatrixData (F:=ZMod p) n k) :
    toLinear (product A B) = (toLinear A).comp (toLinear B) := by
  apply LinearMap.ext
  intro x
  funext i
  simp only [toLinear,LinearMap.coe_mk,AddHom.coe_mk,product_entry,
    LinearMap.comp_apply,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro l hl
  ring

end Prime

theorem multiply_word_runs (A : MatrixData (F:=ZMod p) m n) (B : MatrixData (F:=ZMod p) n k)
    (S : State) (M : ℕ) (bounded : S.Bounded M)
    (rows : S.scalar .rows=m) (inner : S.scalar .inner=n) (cols : S.scalar .cols=k)
    (modulus : S.scalar .modulus=p) (left : S.array .left=word A) (right : S.array .right=word B)
    (small : p*p+p≤M) (total : m*k≤M) :
    ∃ t≤m*k*(12*n+9)+7,∃ T,
      MachinePrograms.NatArrayLanguage.Runs
        (MachinePrograms.NatArrayLanguage.storageBound Reg Arr M) multiply S t T ∧
      T.Bounded M ∧ T.array .output=word (product A B) := by
  have hp : 0<p := NeZero.pos p
  obtain ⟨t,ht,T,run,hT,hout⟩ := multiply_runs S M bounded (by omega)
    (by omega) (by rwa [modulus]) (by rwa [rows,cols])
    (by simp [left,rows,inner]) (by simp [right,inner,cols])
    (by simpa only [left,modulus] using word_values_lt A)
    (by simpa only [right,modulus] using word_values_lt B)
  rw [rows,inner,cols] at ht
  refine ⟨t,ht,T,run,hT,?_⟩
  rw [word_product]
  simpa only [matrixEntry,rows,inner,cols,modulus,left,right] using hout

end GroupWL.MatrixEncoding
