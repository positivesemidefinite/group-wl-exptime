import GroupWL.FiniteCodes
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Sort

/-! Explicit codes for dependent finite products and finite predicate filters. -/
namespace GroupWL.FiniteCode

abbrev fintype (α : Type*) [FiniteCode α] : Fintype α :=
  Fintype.ofEquiv (Fin (size α)) (equiv (α := α)).symm

instance : FiniteCode PUnit :=
  ⟨1, ⟨fun _ => 0, fun _ => PUnit.unit,
    fun _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩⟩

instance sigma {α : Type*} {β : α → Type*} [FiniteCode α] [∀ a, FiniteCode (β a)] :
    FiniteCode (Σ a, β a) :=
  let e := equiv (α := α)
  ⟨∑ i : Fin (size α), size (β (e.symm i)),
    (Equiv.sigmaCongrRight fun a => equiv (α := β a)) |>.trans
      ((Equiv.sigmaCongrLeft (β := fun a => Fin (size (β a))) e.symm).symm.trans finSigmaFinEquiv)⟩

def subtypeSet {α : Type*} [FiniteCode α] (p : α → Prop) [DecidablePred p] :
    Finset (Fin (size α)) := Finset.univ.filter (fun i => p ((equiv (α := α)).symm i))

def subtypeEquiv {α : Type*} [FiniteCode α] (p : α → Prop) [DecidablePred p] :
    {a : α // p a} ≃ {i : Fin (size α) // i ∈ subtypeSet p} where
  toFun a := ⟨equiv a.val, by simp [subtypeSet,a.property]⟩
  invFun i := ⟨(equiv (α := α)).symm i.val, (Finset.mem_filter.mp i.property).2⟩
  left_inv a := Subtype.ext ((equiv (α := α)).symm_apply_apply a)
  right_inv i := Subtype.ext ((equiv (α := α)).apply_symm_apply i)

instance subtype {α : Type*} [FiniteCode α] (p : α → Prop) [DecidablePred p] :
    FiniteCode {a : α // p a} :=
  ⟨(subtypeSet p).card, (subtypeEquiv p).trans
    ((subtypeSet p).orderIsoOfFin rfl).symm.toEquiv⟩

theorem subtype_size_le {α : Type*} [FiniteCode α] (p : α → Prop) [DecidablePred p] :
    size {a : α // p a} ≤ size α := by
  change (subtypeSet p).card ≤ size α
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

end GroupWL.FiniteCode
