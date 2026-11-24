import GroupWL.FiniteCodeEnumeration
import GroupWL.MachinePrograms.FilterRanks

/-! Prefix-count descriptions of canonical dependent and filtered codes. -/
namespace GroupWL.FiniteCode
open scoped BigOperators
set_option linter.unusedSimpArgs false

variable {α : Type*} {β : α → Type*} [FiniteCode α] [∀ a,FiniteCode (β a)]

private theorem val_transport {α : Type*} (n : α → ℕ) {a b : α} (h : a=b) (i : Fin (n a)) :
    (h ▸ i).val=i.val := by cases h; rfl

theorem sigma_val (a : α) (b : β a) :
    (equiv (α:=Σ a,β a) ⟨a,b⟩).val=
      (∑ i : Fin (equiv a).val,size (β ((equiv (α:=α)).symm ⟨i.val,i.isLt.trans (equiv a).isLt⟩)))+
        (equiv b).val := by
  simp only [equiv,FiniteCode.sigma,Equiv.trans_apply,Equiv.sigmaCongrRight,Equiv.sigmaCongrLeft,
    Equiv.symm_apply_apply,Equiv.apply_symm_apply,finSigmaFinEquiv_apply]
  try dsimp only
  congr 1
  simp only [Equiv.coe_fn_symm_mk,Equiv.coe_fn_mk,Equiv.symm_symm]
  exact val_transport (fun x => size (β x)) ((equiv (α:=α)).symm_apply_apply a).symm (equiv b)

end GroupWL.FiniteCode
