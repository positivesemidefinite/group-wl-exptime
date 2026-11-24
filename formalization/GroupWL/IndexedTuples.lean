import GroupWL.IndexedRefinement
import GroupWL.FiniteWL

/-! The explicit disjoint tuple enumeration and its numeric replacement
formula, used by the concrete preprocessing program. -/
namespace GroupWL.IndexedTuples
open IndexedRefinement
open scoped BigOperators

theorem code_update {n k : ℕ} (a : Fin k → Fin n) (i : Fin k) (x : Fin n) :
    (finFunctionFinEquiv (Function.update a i x)).val=
      (finFunctionFinEquiv a).val-(a i).val*n^i.val+x.val*n^i.val := by
  have hsum : (finFunctionFinEquiv a).val=
      (∑ j∈Finset.univ.erase i,(a j).val*n^j.val)+(a i).val*n^i.val := by
    rw [finFunctionFinEquiv_apply]
    exact (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm
  have hup : (finFunctionFinEquiv (Function.update a i x)).val=
      (∑ j∈Finset.univ.erase i,(a j).val*n^j.val)+x.val*n^i.val := by
    rw [finFunctionFinEquiv_apply,← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp only [Function.update_self]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [hup,hsum,Nat.add_sub_cancel]

def replaceCode (n code index value : ℕ) : ℕ :=
  code-digit n code index*n^index+value*n^index

theorem replaceCode_correct {n k : ℕ} (a : Fin k → Fin n) (i : Fin k) (x : Fin n) :
    replaceCode n (finFunctionFinEquiv a).val i.val x.val=
      (finFunctionFinEquiv (Function.update a i x)).val := by
  rw [replaceCode,digit_equiv,Equiv.symm_apply_apply,code_update]

def enumeration (n m k : ℕ) : FiniteWL.Index (Fin n) (Fin m) k ≃ Fin (n^k+m^k) :=
  (Equiv.sumCongr finFunctionFinEquiv finFunctionFinEquiv).trans finSumFinEquiv

def fanout (n m k row : ℕ) : ℕ := if row<n^k then n else m

def target (n m k row slot index : ℕ) : ℕ :=
  if row<n^k then
    if slot<n then replaceCode n row index slot else row
  else if slot<m then n^k+replaceCode m (row-n^k) index slot else row

@[simp] theorem enumeration_left {n m k : ℕ} (a : Fin k → Fin n) :
    (enumeration n m k (.inl a)).val=(finFunctionFinEquiv a).val := rfl

@[simp] theorem enumeration_right {n m k : ℕ} (a : Fin k → Fin m) :
    (enumeration n m k (.inr a)).val=n^k+(finFunctionFinEquiv a).val := rfl

theorem target_left {n m k : ℕ} (a : Fin k → Fin n) (i : Fin k) (x : Fin n) :
    target n m k (enumeration n m k (.inl a)).val x.val i.val=
      (enumeration n m k (.inl (Function.update a i x))).val := by
  simp only [enumeration_left,target,if_pos (finFunctionFinEquiv a).isLt,if_pos x.isLt]
  exact replaceCode_correct a i x

theorem target_right {n m k : ℕ} (a : Fin k → Fin m) (i : Fin k) (x : Fin m) :
    target n m k (enumeration n m k (.inr a)).val x.val i.val=
      (enumeration n m k (.inr (Function.update a i x))).val := by
  simp only [enumeration_right,target,show ¬n^k+(finFunctionFinEquiv a).val<n^k by omega,
    if_false,if_pos x.isLt,Nat.add_sub_cancel_left]
  rw [replaceCode_correct]

theorem target_lt {n m k : ℕ} (row : Fin (n^k+m^k)) (slot : ℕ) (i : Fin k) :
    target n m k row.val slot i.val<n^k+m^k := by
  obtain ⟨a,rfl⟩ := (enumeration n m k).surjective row
  cases a with
  | inl a =>
    by_cases hs : slot<n
    · rw [target_left a i ⟨slot,hs⟩]
      exact (enumeration n m k (.inl (Function.update a i ⟨slot,hs⟩))).isLt
    · simp only [enumeration_left,target,if_pos (finFunctionFinEquiv a).isLt,if_neg hs]
      exact (enumeration n m k (.inl a)).isLt
  | inr a =>
    by_cases hs : slot<m
    · rw [target_right a i ⟨slot,hs⟩]
      exact (enumeration n m k (.inr (Function.update a i ⟨slot,hs⟩))).isLt
    · simpa [target,hs,show ¬n^k+(finFunctionFinEquiv a).val<n^k by omega] using
        (enumeration n m k (.inr a)).isLt

def data (n m k : ℕ) (hn : 0<n) : Data (n^k+m^k) k (max n m) where
  positive := Nat.add_pos_left (pow_pos hn _) _
  fanout row := fanout n m k row.val
  fanout_le row := by
    unfold fanout
    split_ifs
    · exact Nat.le_max_left ..
    · exact Nat.le_max_right ..
  target row slot i := ⟨target n m k row.val slot.val i.val,target_lt row slot.val i⟩

@[simp] theorem data_fanout (n m k : ℕ) (hn : 0<n) (row : Fin (n^k+m^k)) :
    (data n m k hn).fanout row=fanout n m k row.val := rfl

@[simp] theorem data_target (n m k : ℕ) (hn : 0<n) (row : Fin (n^k+m^k))
    (slot : Fin (max n m)) (i : Fin k) :
    ((data n m k hn).target row slot i).val=target n m k row.val slot.val i.val := rfl

end GroupWL.IndexedTuples
