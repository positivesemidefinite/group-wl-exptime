import GroupWL.FiniteCodeConstructions
import Mathlib.Data.List.OfFn

/-! Numeric subtype codes enumerate the satisfying parent codes in increasing order. -/
namespace GroupWL.FiniteCode

def enumeration (α : Type*) [FiniteCode α] : List α := List.ofFn (equiv (α := α)).symm

theorem ofFn_sum {α β γ : Type*} [FiniteCode α] [FiniteCode β] (f : α ⊕ β → γ) :
    List.ofFn (fun i => f ((equiv (α := α ⊕ β)).symm i)) =
      List.ofFn (fun i => f (.inl ((equiv (α := α)).symm i))) ++
      List.ofFn (fun i => f (.inr ((equiv (α := β)).symm i))) := by
  change List.ofFn (fun i => f ((Equiv.sumCongr (equiv (α := α)) (equiv (α := β))).symm
    (finSumFinEquiv.symm i))) = _
  rw [List.ofFn_add]
  congr 1
  · congr 1
    funext i
    have he : (Fin.castLE (Nat.le_add_right (size α) (size β)) i : Fin (size α+size β)) =
        finSumFinEquiv (.inl i) := rfl
    rw [he,Equiv.symm_apply_apply]
    rfl
  · congr 1
    funext i
    have he : (Fin.natAdd (size α) i : Fin (size α+size β)) = finSumFinEquiv (.inr i) := rfl
    rw [he,Equiv.symm_apply_apply]
    rfl

theorem ofFn_prod {α β γ : Type*} [FiniteCode α] [FiniteCode β] (f : α × β → γ) :
    List.ofFn (fun i => f ((equiv (α := α × β)).symm i)) =
      (List.ofFn (fun i => List.ofFn (fun j =>
        f ((equiv (α := α)).symm i,(equiv (α := β)).symm j)))).flatten := by
  change List.ofFn (fun i => f ((Equiv.prodCongr (equiv (α := α)) (equiv (α := β))).symm
    (finProdFinEquiv.symm i))) = _
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have hlt : i.val*size β+j.val < size α*size β := by
    calc
      _ < i.val*size β+size β := Nat.add_lt_add_left j.isLt _
      _ = (i.val+1)*size β := by rw [Nat.add_mul,Nat.one_mul]
      _ ≤ _ := Nat.mul_le_mul_right _ i.isLt
  have he : (⟨i.val*size β+j.val,hlt⟩ : Fin (size α*size β)) =
      finProdFinEquiv (i,j) := by
    apply Fin.ext
    change i.val*size β+j.val = j.val+size β*i.val
    rw [Nat.mul_comm i.val (size β),Nat.add_comm]
  rw [he,Equiv.symm_apply_apply]
  rfl

theorem ofFn_option {α γ : Type*} [FiniteCode α] (f : Option α → γ) :
    List.ofFn (fun i => f ((equiv (α := Option α)).symm i)) =
      f none :: List.ofFn (fun i => f (some ((equiv (α := α)).symm i))) := by
  change List.ofFn (fun i => f ((Equiv.optionCongr (equiv (α := α))).symm
    (finSuccEquiv (size α) i))) = _
  rw [List.ofFn_succ]
  simp only [finSuccEquiv_zero,finSuccEquiv_succ]
  rfl

theorem ofFn_bool {γ : Type*} (f : Bool → γ) :
    List.ofFn (fun i => f ((equiv (α := Bool)).symm i)) = [f false,f true] := by
  change List.ofFn (fun i : Fin 2 => f (finTwoEquiv i)) = _
  rw [List.ofFn_succ,List.ofFn_succ,List.ofFn_zero]
  rfl

variable {α : Type*} [FiniteCode α]

theorem subtype_enumeration (p : α → Prop) [DecidablePred p] :
    List.ofFn (fun i : Fin (size {a : α // p a}) =>
      equiv (α := α) ((equiv (α := {a : α // p a})).symm i).val) =
    (List.finRange (size α)).filter (fun i => decide (p ((equiv (α := α)).symm i))) := by
  have hfun : (fun i : Fin (size {a : α // p a}) =>
      equiv (α := α) ((equiv (α := {a : α // p a})).symm i).val) =
      (subtypeSet p).orderEmbOfFin rfl := by
    funext i
    change equiv ((equiv (α := α)).symm _) = _
    simp only [Equiv.apply_symm_apply]
    rfl
  rw [hfun,List.ofFn_eq_map]
  change (List.finRange (subtypeSet p).card).map ((subtypeSet p).orderEmbOfFin rfl) = _
  rw [Finset.listMap_orderEmbOfFin_finRange]
  apply (Finset.sortedLT_sort _).eq_of_mem_iff
  · exact ((List.sortedLT_finRange _).pairwise.filter _).sortedLT
  · intro i
    simp [subtypeSet]

theorem subtype_values (p : α → Prop) [DecidablePred p] :
    List.ofFn (fun i : Fin (size {a : α // p a}) =>
      (equiv (α := α) ((equiv (α := {a : α // p a})).symm i).val).val) =
    ((List.finRange (size α)).filter
      (fun i => decide (p ((equiv (α := α)).symm i)))).map Fin.val := by
  rw [← subtype_enumeration p,List.map_ofFn]
  rfl

theorem subtype_values_filter (p : α → Prop) [DecidablePred p] (q : ℕ → Bool)
    (hq : ∀ i : Fin (size α), q i.val=decide (p ((equiv (α := α)).symm i))) :
    List.ofFn (fun i : Fin (size {a : α // p a}) =>
      (equiv (α := α) ((equiv (α := {a : α // p a})).symm i).val).val) =
    (List.range (size α)).filter q := by
  rw [subtype_values]
  have hmap : (List.finRange (size α)).map Fin.val=List.range (size α) := by simp
  rw [← hmap,List.filter_map]
  congr 1
  congr 1
  funext i
  exact (hq i).symm

end GroupWL.FiniteCode
