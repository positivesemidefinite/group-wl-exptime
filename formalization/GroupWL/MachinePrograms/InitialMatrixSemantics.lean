import GroupWL.MachinePrograms.InitialMatrixAssembly

/-! The constructed numeric initial matrix is the concrete Version-I
atomic-signature relation under the explicit tuple enumeration. -/
namespace GroupWL.MachinePrograms.InitialMatrixPrograms
open GroupWL.IndexedRefinement

theorem pointSignature_left {n m k : ℕ} (mul : Fin n → Fin n → Fin n)
    (mul' : Fin m → Fin m → Fin m) (a : Fin k → Fin n) :
    pointSignature mul mul' (IndexedTuples.enumeration n m k (.inl a))=GroupInitial.signature mul a := by
  unfold pointSignature pointMul pointCode selectMul
  generalize_proofs bound
  generalize hd : decide (n^k ≤ (IndexedTuples.enumeration n m k (.inl a)).val)=d at bound ⊢
  cases d
  · simp only [selectBase,selectCode,Bool.false_eq_true,if_false,IndexedTuples.enumeration_left]
    change GroupInitial.signature mul (finFunctionFinEquiv.symm (finFunctionFinEquiv a))=_
    rw [Equiv.symm_apply_apply]
  ·
    have hh : ¬ n^k ≤ (IndexedTuples.enumeration n m k (.inl a)).val := by
      simpa only [IndexedTuples.enumeration_left] using Nat.not_le_of_lt (finFunctionFinEquiv a).isLt
    simp_all

theorem pointSignature_right {n m k : ℕ} (mul : Fin n → Fin n → Fin n)
    (mul' : Fin m → Fin m → Fin m) (a : Fin k → Fin m) :
    pointSignature mul mul' (IndexedTuples.enumeration n m k (.inr a))=GroupInitial.signature mul' a := by
  unfold pointSignature pointMul pointCode selectMul
  generalize_proofs bound
  generalize hd : decide (n^k ≤ (IndexedTuples.enumeration n m k (.inr a)).val)=d at bound ⊢
  cases d
  ·
    have hh : n^k ≤ (IndexedTuples.enumeration n m k (.inr a)).val := by
      simp only [IndexedTuples.enumeration_right]
      exact Nat.le_add_right _ _
    simp_all
  · simp only [selectBase,selectCode,if_true,IndexedTuples.enumeration_right,Nat.add_sub_cancel_left]
    change GroupInitial.signature mul' (finFunctionFinEquiv.symm (finFunctionFinEquiv a))=_
    rw [Equiv.symm_apply_apply]

theorem pointSignature_enumeration {n m k : ℕ} (mul : Fin n → Fin n → Fin n)
    (mul' : Fin m → Fin m → Fin m) (a : FiniteWL.Index (Fin n) (Fin m) k) :
    pointSignature mul mul' (IndexedTuples.enumeration n m k a)=
      Sum.elim (GroupInitial.signature mul) (GroupInitial.signature mul') a := by
  cases a with
  | inl a => exact pointSignature_left mul mul' a
  | inr a => exact pointSignature_right mul mul' a

theorem initialEq_correct {n m k : ℕ} (mul : Fin n → Fin n → Fin n)
    (mul' : Fin m → Fin m → Fin m) (a c : Fin (n^k+m^k)) :
    initialEq mul mul' a c=true ↔ pointSignature mul mul' a=pointSignature mul mul' c := by
  simp only [initialEq,decide_eq_true_eq]

theorem initialRelation_eq_table_zero {n m k : ℕ} (mul : Fin n → Fin n → Fin n)
    (mul' : Fin m → Fin m → Fin m)
    (edges : Fin (n^k+m^k) → Multiset (Fin k → Fin (n^k+m^k))) :
    initialRelation (k:=k) mul mul'=CompressedRefinement.table edges (initialEq mul mul') 0 := rfl

end GroupWL.MachinePrograms.InitialMatrixPrograms

