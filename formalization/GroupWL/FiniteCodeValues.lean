import GroupWL.FiniteCodeRanks

/-! Arithmetic formulas for the canonical finite index constructors. -/
namespace GroupWL.FiniteCode

@[simp] theorem bool_false_val : (equiv (α:=Bool) false).val=0 := rfl
@[simp] theorem bool_true_val : (equiv (α:=Bool) true).val=1 := rfl
@[simp] theorem fin_val {n : ℕ} (i : Fin n) : (equiv i).val=i.val := rfl

theorem prod_val {α β : Type*} [FiniteCode α] [FiniteCode β] (a : α) (b : β) :
    (equiv (a,b)).val=(equiv a).val*size β+(equiv b).val := by
  change (equiv b).val+size β*(equiv a).val=(equiv a).val*size β+(equiv b).val
  ac_rfl

@[simp] theorem sum_inl_val {α β : Type*} [FiniteCode α] [FiniteCode β] (a : α) :
    (equiv (α:=α⊕β) (.inl a)).val=(equiv a).val := rfl

@[simp] theorem sum_inr_val {α β : Type*} [FiniteCode α] [FiniteCode β] (b : β) :
    (equiv (α:=α⊕β) (.inr b)).val=size α+(equiv b).val := rfl

@[simp] theorem option_none_val {α : Type*} [FiniteCode α] :
    (equiv (α:=Option α) none).val=0 := by
  change ((finSuccEquiv (size α)).symm none).val=0
  simp

@[simp] theorem option_some_val {α : Type*} [FiniteCode α] (a : α) :
    (equiv (α:=Option α) (some a)).val=(equiv a).val+1 := by
  change ((finSuccEquiv (size α)).symm (some (equiv a))).val=(equiv a).val+1
  simp

end GroupWL.FiniteCode
