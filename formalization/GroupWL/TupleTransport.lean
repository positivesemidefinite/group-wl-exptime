import GroupWL.IndexedTupleEdges

/-! Coordinatewise transport of tuple replacement multisets. -/
namespace GroupWL.FiniteWL
variable {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D] {k : ℕ}

def reindex (e : A ≃ C) (e' : B ≃ D) : Index A B k ≃ Index C D k :=
  Equiv.sumCongr (Equiv.piCongrRight (fun _ : Fin k => e)) (Equiv.piCongrRight (fun _ : Fin k => e'))

theorem edges_reindex (e : A ≃ C) (e' : B ≃ D) (a : Index A B k) :
    edges (reindex e e' a)=(edges a).map (fun v i => reindex e e' (v i)) := by
  cases a with
  | inl a =>
    change Finset.univ.val.map (fun x : C => fun i => Sum.inl (Function.update (e ∘ a) i x))=_
    rw [←Multiset.map_univ_val_equiv e,Multiset.map_map]
    simp only [edges,Multiset.map_map]
    apply Multiset.map_congr rfl
    intro x hx
    funext i
    change (Sum.inl (Function.update (e ∘ a) i (e x)) : Index C D k)=Sum.inl (e ∘ Function.update a i x)
    exact congrArg Sum.inl (Function.comp_update e a i x).symm
  | inr a =>
    change Finset.univ.val.map (fun x : D => fun i => Sum.inr (Function.update (e' ∘ a) i x))=_
    rw [←Multiset.map_univ_val_equiv e',Multiset.map_map]
    simp only [edges,Multiset.map_map]
    apply Multiset.map_congr rfl
    intro x hx
    funext i
    change (Sum.inr (Function.update (e' ∘ a) i (e' x)) : Index C D k)=Sum.inr (e' ∘ Function.update a i x)
    exact congrArg Sum.inr (Function.comp_update e' a i x).symm

def numericEnumeration {n m : ℕ} (e : A ≃ Fin n) (e' : B ≃ Fin m) : Index A B k ≃ Fin (n^k+m^k) :=
  (reindex e e').trans (IndexedTuples.enumeration n m k)

theorem edges_numericEnumeration {n m : ℕ} (hn : 0<n) (e : A ≃ Fin n) (e' : B ≃ Fin m)
    (a : Index A B k) :
    (IndexedTuples.data n m k hn).edges (numericEnumeration e e' a)=
      (edges a).map (fun v i => numericEnumeration e e' (v i)) := by
  rw [numericEnumeration,Equiv.trans_apply,IndexedTuples.edges_enumeration,edges_reindex,Multiset.map_map]
  rfl
end GroupWL.FiniteWL
