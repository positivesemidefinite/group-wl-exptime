import GroupWL.MachinePrograms.RingDimensions
import GroupWL.MachinePrograms.ArrayScale
import GroupWL.MachinePrograms.PrefixSums

namespace GroupWL.MachinePrograms

theorem count_le_mul (xs : List ℕ) (b : ℕ) (h : ∀ x∈xs,x≤b) (i : ℕ) :
    FilterRanks.count xs i≤ i*b := by
  induction i with
  | zero => simp [FilterRanks.count]
  | succ i ih =>
    have hv := RingDimensions.read_le xs b h i
    simp only [FilterRanks.count,Nat.succ_mul]
    omega

namespace RingDimensions

def dimensions (widths : List ℕ) (b : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin (b+widths.length) => value widths b i.val)

theorem value_le (widths : List ℕ) (b i : ℕ) (hv : ∀ x∈widths,x≤b) : value widths b i≤b+2 := by
  unfold value
  split
  · omega
  · have h := read_le widths b hv (i-b)
    omega

theorem dimensions_values (widths : List ℕ) (b : ℕ) (hv : ∀ x∈widths,x≤b) :
    ∀ x∈dimensions widths b,x≤b+2 := by
  intro x hx
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  exact value_le widths b i.val hv

end RingDimensions
end GroupWL.MachinePrograms
