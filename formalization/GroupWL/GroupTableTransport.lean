import GroupWL.VerifiedGroupTable

/-! Finite table validation is invariant under explicit carrier reindexing. -/
namespace GroupWL.VerifiedGroupTable
variable {K L : Type*} [Fintype K] [Fintype L]

theorem valid_reindex (e : L ≃ K) (identity : K) (op : K → K → K) (h : Valid identity op) :
    Valid (e.symm identity) (fun a b => e.symm (op (e a) (e b))) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro a
    apply e.injective
    simp only [Equiv.apply_symm_apply,h.1]
  · intro a
    apply e.injective
    simp only [Equiv.apply_symm_apply,h.2.1]
  · intro a b c
    apply e.injective
    simp only [Equiv.apply_symm_apply,h.2.2.1]
  · intro a b c heq
    apply e.injective
    apply h.2.2.2 (e a)
    simpa only [Equiv.apply_symm_apply] using congrArg e heq

theorem valid_reindex_iff (e : L ≃ K) (identity : K) (op : K → K → K) :
    Valid identity op ↔ Valid (e.symm identity) (fun a b => e.symm (op (e a) (e b))) := by
  refine ⟨valid_reindex e identity op,fun h => ?_⟩
  have hh := valid_reindex e.symm _ _ h
  simpa only [Equiv.symm_symm,Equiv.apply_symm_apply,Equiv.symm_apply_apply] using hh

end GroupWL.VerifiedGroupTable
