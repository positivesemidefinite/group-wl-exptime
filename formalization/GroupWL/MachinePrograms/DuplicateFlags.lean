import GroupWL.MachinePrograms.RepeatedSelection
import GroupWL.MachinePrograms.RectangleFlags
import GroupWL.MachinePrograms.FilterRanksSemantics

/-! Repeating Boolean selection flags preserves stable ranks, with two entries per selected record. -/
namespace GroupWL.MachinePrograms.DuplicateFlags

def word (xs : List ℕ) : List ℕ := RepeatedSelection.repeated xs xs.length 1 2

@[simp] theorem length (xs : List ℕ) : (word xs).length=2*xs.length := by
  simp [word,RepeatedSelection.repeated,Nat.mul_comm]

theorem read (xs : List ℕ) (i k : ℕ) (hi : i<xs.length) (hk : k<2) :
    (word xs)[2*i+k]?.getD 0=xs[i]?.getD 0 := by
  have hb : 2*i+k<xs.length*1*2 := by omega
  simp only [word,RepeatedSelection.repeated,List.getElem?_ofFn]
  split_ifs with h
  all_goals first
    | exact (h hb).elim
    | have hd : (2*i+k)/2=i := by omega
      simp only [Option.getD_some,ArrayRepeatBlocks.entry,Nat.div_one,Nat.mod_one,Nat.mul_one,Nat.add_zero,hd]

theorem binary (xs : List ℕ) (h : ∀x∈xs,x≤1) : ∀x∈word xs,x≤1 := by
  intro x hx
  rcases List.mem_ofFn.mp hx with ⟨i,rfl⟩
  exact RectangleFlags.read_small h _

theorem count_even (xs : List ℕ) (i : ℕ) (hi : i≤xs.length) :
    FilterRanks.count (word xs) (2*i)=2*FilterRanks.count xs i := by
  induction i with
  | zero => simp [FilterRanks.count]
  | succ i ih =>
      have hi' : i<xs.length := by omega
      have he : 2*(i+1)=2*i+1+1 := by omega
      rw [he,FilterRanks.count,FilterRanks.count,ih (by omega),read xs i 1 hi' (by decide)]
      have hzero := read xs i 0 hi' (by decide)
      simp only [Nat.add_zero] at hzero
      rw [hzero,FilterRanks.count]
      omega

theorem count_key (xs : List ℕ) (i k : ℕ) (hi : i<xs.length) (hk : k<2)
    (chosen : xs[i]?.getD 0=1) :
    FilterRanks.count (word xs) (2*i+k)=2*FilterRanks.count xs i+k := by
  interval_cases k
  · simpa using count_even xs i (by omega)
  · rw [FilterRanks.count,count_even xs i (by omega)]
    have h := read xs i 0 hi (by decide)
    simp only [Nat.add_zero] at h
    rw [h,chosen]

end GroupWL.MachinePrograms.DuplicateFlags
