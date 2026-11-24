import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Card

/-! Explicit finite codes assembled without a choice of enumeration. -/
namespace GroupWL

class FiniteCode (α : Type*) where
  size : ℕ
  equiv : α ≃ Fin size

namespace FiniteCode

instance : FiniteCode Bool := ⟨2, finTwoEquiv.symm⟩
instance (n : ℕ) : FiniteCode (Fin n) := ⟨n, Equiv.refl _⟩

instance {α : Type*} [FiniteCode α] : FiniteCode (Option α) :=
  ⟨size α + 1, (Equiv.optionCongr (equiv (α := α))).trans (finSuccEquiv (size α)).symm⟩

instance {α β : Type*} [FiniteCode α] [FiniteCode β] : FiniteCode (α ⊕ β) :=
  ⟨size α + size β, (Equiv.sumCongr (equiv (α := α)) (equiv (α := β))).trans finSumFinEquiv⟩

instance {α β : Type*} [FiniteCode α] [FiniteCode β] : FiniteCode (α × β) :=
  ⟨size α * size β, (Equiv.prodCongr (equiv (α := α)) (equiv (α := β))).trans finProdFinEquiv⟩

theorem card_eq_size (α : Type*) [Fintype α] [FiniteCode α] :
    Fintype.card α = size α := by
  simpa using Fintype.card_congr (equiv (α := α))

end FiniteCode
end GroupWL
