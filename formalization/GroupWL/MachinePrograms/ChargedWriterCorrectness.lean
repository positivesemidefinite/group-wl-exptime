import GroupWL.MachinePrograms.ChargedWriter
import GroupWL.MachinePrograms.ChargeArithmetic

/-! The single charge-vector lookup returns the exact Gaussian-coordinate twist entry. -/
namespace GroupWL.MachinePrograms.ChargedWriter
open IncidenceTensor ConstructiveIncidence ConstructiveCoordinates ChargeCoordinates

def chargeWord {I : Type} [FiniteCode I] (p : ℕ) (β : I → ZMod p) : List ℕ :=
  List.ofFn (fun j : Fin (FiniteCode.size I) => (β (FiniteCode.equiv.symm j)).val)

@[simp] theorem chargeWord_length {I : Type} [FiniteCode I] (p : ℕ) (β : I → ZMod p) :
    (chargeWord p β).length=FiniteCode.size I := List.length_ofFn

theorem chargeWord_read {I : Type} [FiniteCode I] (p : ℕ) (β : I → ZMod p) (i : I) :
    (chargeWord p β)[(FiniteCode.equiv i).val]?.getD 0=(β i).val := by
  simp [chargeWord]

private theorem locate (v i z : ℕ) (hv : 1<v) :
    i*v+1=z ↔ z%v=1 ∧ z/v=i := by
  constructor
  · rintro rfl
    rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hv,Nat.mul_comm i v,
      Nat.mul_add_div (by omega : 0<v),Nat.div_eq_of_lt hv,Nat.add_zero]
    exact ⟨rfl,rfl⟩
  · rintro ⟨hm,hd⟩
    rw [←hd,←hm]
    exact Nat.div_add_mod' _ _

private def signed {p : ℕ} [Fact p.Prime] (a : ZMod p) (s x y : ℕ) : ZMod p :=
  a * (delta s x * delta (s+2) y - delta s y * delta (s+2) x)

private theorem signed_val {p : ℕ} [Fact p.Prime] (a : ZMod p) (s x y : ℕ) :
    (signed a s x y).val=
      if x=s ∧ y=s+2 then a.val else if y=s ∧ x=s+2 then (p-a.val)%p else 0 := by
  by_cases hx : x=s <;> by_cases hy : y=s+2 <;> by_cases hx' : x=s+2 <;> by_cases hy' : y=s
  all_goals first | omega | simp_all [signed,delta,eq_comm,ZMod.neg_val']

theorem cell_eq_sum {I : Type} [FiniteCode I] [Fintype I]
    (p : ℕ) [Fact p.Prime] (β : I → ZMod p) (u v x y z : ℕ) (hv : 1<v) :
    cell (chargeWord p β) p u v x y z =
      (∑i : I, signed (β i) ((FiniteCode.equiv i).val*u) x y *
        delta ((FiniteCode.equiv i).val*v+1) z).val := by
  classical
  by_cases hz : z%v=1
  · by_cases hb : z/v<FiniteCode.size I
    · let a : I := FiniteCode.equiv.symm ⟨z/v,hb⟩
      have ha : (FiniteCode.equiv a).val=z/v := by simp [a]
      have atA : (FiniteCode.equiv a).val*v+1=z := (locate v _ _ hv).mpr ⟨hz,ha.symm⟩
      rw [Finset.sum_eq_single a]
      · simp only [delta,atA,if_true,mul_one,signed_val,cell,hz,if_true]
        have hread := chargeWord_read p β a
        rw [ha] at hread ⊢
        rw [hread]
      · intro b _ hba
        have he : (FiniteCode.equiv b).val*v+1≠z := by
          intro he
          apply hba
          apply FiniteCode.equiv.injective
          exact Fin.ext (((locate v _ _ hv).mp he).2.symm.trans ha.symm)
        simp [delta,he]
      · simp
    · have zero : ∀i : I,(FiniteCode.equiv i).val*v+1≠z := by
        intro i he
        exact hb (((locate v _ _ hv).mp he).2 ▸ (FiniteCode.equiv i).isLt)
      have missing : (chargeWord p β)[z/v]?=none := List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hb)
      simp only [delta,zero,if_false,mul_zero,Finset.sum_const_zero,ZMod.val_zero]
      simp [cell,hz,missing]
  · have zero : ∀i : I,(FiniteCode.equiv i).val*v+1≠z := by
      intro i he
      exact hz ((locate v _ _ hv).mp he).1
    simp [cell,hz,delta,zero]

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [FiniteCode I] [FiniteCode J] (p : ℕ) [Fact p.Prime]
variable {V : J → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module (ZMod p) (V j)]
variable (A : AffineSystem (ZMod p) I J V)
  (R : ∀ j, Coordinates (ZMod p) (ReadoutRadical A j)) (q : ℕ)
local notation "X" => FiniteCode.size (InputIndex A R q)
local notation "Z" => FiniteCode.size (OutputIndex A R q)
theorem positions_eq_twist (hq : 2≤q) (β : I → ZMod p) :
    List.ofFn (fun k : Fin (X*X*Z) =>
      atPosition (chargeWord p β) p (q*2) (FiniteCode.size (Pair q)*2) X Z k.val)=
      ConstructiveTensorAssembly.twistEntries p A R q (epsilonCharge A q hq β) := by
  rw [denseTwist,EvaluationAssembly.entries3]
  apply congrArg List.ofFn
  funext k
  have h := (FiniteCode.equiv (firstPair q hq)).isLt
  exact cell_eq_sum p β (q*2) (FiniteCode.size (Pair q)*2) _ _ _ (by omega)
end GroupWL.MachinePrograms.ChargedWriter
