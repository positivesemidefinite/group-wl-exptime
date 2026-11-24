import GroupWL.MachinePrograms.SelectArray

/-! Stable-compaction output is the increasing-index filtered list. -/
namespace GroupWL.MachinePrograms.SelectArray

theorem selectedPrefix_eq_filter (flags values : List ℕ) (n : ℕ) :
    selectedPrefix flags values n=
      ((List.range n).filter (fun i => flags[i]?.getD 0≠0)).map (fun i => values[i]?.getD 0) := by
  induction n with
  | zero => simp [selectedPrefix]
  | succ n ih =>
    simp only [selectedPrefix,List.range_succ,List.filter_append,List.map_append,ih]
    by_cases h : flags[n]?.getD 0=0 <;> simp [h]


theorem selectedPrefix_read (flags values : List ℕ) (binary : ∀x∈flags,x≤1)
    (n i : ℕ) (hi : i<n) (chosen : flags[i]?.getD 0=1) :
    (selectedPrefix flags values n)[FilterRanks.count flags i]?=some (values[i]?.getD 0) := by
  induction n with
  | zero => omega
  | succ n ih =>
    have hh := selectedPrefix_length flags values binary n
    by_cases hn : i<n
    · have hm := FilterRanks.count_mono flags (show i+1≤n by omega)
      have hlt : FilterRanks.count flags i<(selectedPrefix flags values n).length := by
        rw [hh]
        simpa only [FilterRanks.count,chosen] using hm
      rw [selectedPrefix,List.getElem?_append_left hlt]
      exact ih hn
    · have he : i=n := by omega
      subst i
      rw [selectedPrefix,chosen]
      simp only [Nat.one_ne_zero,↓reduceIte]
      rw [←hh]
      simp

end GroupWL.MachinePrograms.SelectArray
