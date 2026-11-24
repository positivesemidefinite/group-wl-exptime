import GroupWL.MachinePrograms.SourceCoefficients
import Mathlib.Data.ZMod.Basic

/-! The subtraction-safe natural-number program computes the signed field
coefficient, including cancellation when square endpoints coincide. -/
namespace GroupWL.SourceCoefficientResidues

def signedResidue (p l r a b : ℕ) : ℕ := ((l+p-r+a)+p-b)%p

theorem signedResidue_cast (p l r a b : ℕ) (hr : r ≤ p) (hb : b ≤ p) :
    (signedResidue p l r a b : ZMod p) = (l : ZMod p)-r+a-b := by
  have h₁ : r ≤ l+p := by omega
  have h₂ : b ≤ l+p-r+a+p := by omega
  simp only [signedResidue,ZMod.natCast_mod,Nat.cast_sub h₂,Nat.cast_add,Nat.cast_sub h₁,
    ZMod.natCast_self,add_zero]

theorem delta_le_one (x y : ℕ) : MachinePrograms.SourceCoefficients.delta x y ≤ 1 := by
  unfold MachinePrograms.SourceCoefficients.delta
  split <;> omega

theorem delta_cast (p x y : ℕ) :
    (MachinePrograms.SourceCoefficients.delta x y : ZMod p) = if x=y then 1 else 0 := by
  unfold MachinePrograms.SourceCoefficients.delta
  split <;> simp_all

theorem delta_mul_cast (p x y k : ℕ) :
    (MachinePrograms.SourceCoefficients.delta x y*MachinePrograms.SourceCoefficients.delta k 0 : ZMod p) =
      if x=y ∧ k=0 then 1 else 0 := by
  simp only [Nat.cast_mul,delta_cast]
  split_ifs <;> simp_all

end GroupWL.SourceCoefficientResidues
