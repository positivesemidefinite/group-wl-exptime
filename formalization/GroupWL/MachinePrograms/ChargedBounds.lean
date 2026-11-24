import GroupWL.MachinePrograms.ChargedAssembly

/-! Uniform polynomial bounds for the final writer and the two tensor assemblies. -/
set_option exponentiation.threshold 512
namespace GroupWL.MachinePrograms.ChargedAssembly
open ChargedWriter
def writerBase (s : ℕ) := 16*(s+1)^3
def writerMemory (s : ℕ) := (writerBase s+2)^264

theorem writer_cost : expr.cost=132 := rfl
theorem writer_scratch : expr.need=3 := rfl

theorem pairCount_le (q : ℕ) : FiniteCode.size (IncidenceTensor.Pair q)≤q*q :=
  FiniteCode.subtype_size_le _

theorem room {s X Z q c p k blocks w : ℕ}
    (hx : X≤s) (hz : Z≤s) (hq : q≤s) (hc : c≤q*q)
    (hp : p≤s) (hk : k≤s) (hi : blocks≤s) (hw : w≤s) :
    2+X+Z+q*2+c*2+p+k+blocks+X*X+X*X*Z≤writerBase s ∧
    (writerBase s+2)^(2*(term.expression sizeReg).cost)≤writerMemory s ∧
    writerBase s≤writerMemory s ∧
    X+w+(X+w)*(X+w)+(X+w)*(X+w)*Z≤writerMemory s := by
  have hc' : c≤s*s := hc.trans (Nat.mul_le_mul hq hq)
  have a : 2+X+Z+q*2+c*2+p+k+blocks+X*X+X*X*Z≤writerBase s := by
    calc _ ≤ 2+s+s+s*2+(s*s)*2+s+s+s+s*s+s*s*s := by gcongr
         _ ≤ _ := by unfold writerBase; nlinarith
  have b : writerBase s≤writerMemory s := by
    calc _ ≤ (writerBase s+2)^1 := by simp
         _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide : 1≤264)
  refine ⟨a,le_rfl,b,le_trans ?_ b⟩
  calc _ ≤ s+s+(s+s)*(s+s)+(s+s)*(s+s)*s := by gcongr
       _ ≤ _ := by unfold writerBase; nlinarith

theorem writerMemory_polynomial (s : ℕ) : writerMemory s≤18^264*(s+1)^792 := by
  unfold writerMemory writerBase
  have h : 16*(s+1)^3+2≤18*(s+1)^3 := by
    have hpos : 1≤(s+1)^3 := Nat.one_le_pow _ _ (by omega)
    omega
  calc _ ≤ (18*(s+1)^3)^264 := Nat.pow_le_pow_left h _
       _ = _ := by rw [mul_pow,←pow_mul]

theorem time_bound {s X Z w : ℕ} (hx : X≤s) (hz : Z≤s) (hw : w≤s) :
    cost (X*X*Z) ((X+w)*(X+w)*Z) ≤
      Fintype.card R₂+Fintype.card A₂+322*(s+1)^3 := by
  have h₁ : X*X*Z≤s*s*s := by gcongr
  have h₂ : (X+w)*(X+w)*Z≤(s+s)*(s+s)*s := by gcongr
  unfold cost
  rw [writer_cost]
  nlinarith

end GroupWL.MachinePrograms.ChargedAssembly

namespace GroupWL.MachinePrograms.LayoutRecordPrograms
variable (p : ℕ) [Fact p.Prime] {T : Type} [FiniteCode T] {r : ℕ}
theorem Output.rejecting_chargeWord (D : AddressedCircuit.Circuit T r) (L : ℕ) {S : State}
    (h : Output (ComparisonMetadata.ofComparison p (CircuitComparisons.comparisons D (ZMod p)))
      L (FiniteCode.size (CircuitComparisons.Comparison D)-3) S) :
    S.array chargeArray=ChargedWriter.chargeWord p
      ((CircuitComparisons.comparisons D (ZMod p)).sourceShift (L:=L)
        (CircuitComparisons.rejectingConstant D (ZMod p))) :=
  h.rejecting_charge p L D
end GroupWL.MachinePrograms.LayoutRecordPrograms
