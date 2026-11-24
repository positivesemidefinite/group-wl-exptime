import GroupWL.MachinePrograms.FilterRanksSemantics

namespace GroupWL.MachinePrograms.PaddedFlags
open scoped BigOperators

def word (dimension blocks cap : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin (blocks*cap) => if i.val%cap<dimension then 1 else 0)

theorem initial_sum (d n : ℕ) (h : d≤n) :
    (∑i∈Finset.range n,if i<d then 1 else 0 : ℕ)=d := by
  induction n generalizing d with
  | zero =>
      have hd : d=0 := by omega
      simp [hd]
  | succ n ih =>
      rw [Finset.sum_range_succ]
      by_cases hd : d≤n
      · rw [ih d hd,if_neg (by omega)]; omega
      · have he : d=n+1 := by omega
        subst d
        have hs : (∑i∈Finset.range n,if i<n+1 then 1 else 0 : ℕ)=n := by
          calc
            _=∑i∈Finset.range n,(1:ℕ) := Finset.sum_congr rfl (fun i hi => if_pos (by have := Finset.mem_range.mp hi; omega))
            _=n := by simp
        rw [hs,if_pos (by omega)]

theorem read (d n cap i j : ℕ) (hi : i<n) (hj : j<cap) :
    (word d n cap)[i*cap+j]?.getD 0=if j<d then 1 else 0 := by
  have hb : i*cap+j<n*cap := by nlinarith [Nat.mul_le_mul_right cap (Nat.succ_le_of_lt hi)]
  simp only [word,List.getElem?_ofFn,dif_pos hb,Option.getD_some]
  simp only [Nat.mul_add_mod',Nat.mod_eq_of_lt hj]

theorem count_blocks (d n cap i : ℕ) (hd : d≤cap) (hi : i≤n) :
    FilterRanks.count (word d n cap) (i*cap)=i*d := by
  rw [FilterRanks.count_eq_sum,FilterRanks.sum_range_blocks]
  calc
    _=∑a∈Finset.range i,d := by
      apply Finset.sum_congr rfl
      intro a ha
      calc
        _=∑b∈Finset.range cap,(if b<d then 1 else 0 : ℕ) := by
          apply Finset.sum_congr rfl
          intro b hb
          exact read d n cap a b (by have := Finset.mem_range.mp ha; omega) (Finset.mem_range.mp hb)
        _=d := initial_sum d cap hd
    _=i*d := by simp

theorem count_key (d n cap i j : ℕ) (hd : d≤cap) (hi : i<n) (hj : j≤d) :
    FilterRanks.count (word d n cap) (i*cap+j)=i*d+j := by
  rw [FilterRanks.count_eq_sum,Finset.sum_range_add,←FilterRanks.count_eq_sum,count_blocks d n cap i hd hi.le]
  congr 1
  calc
    _=∑b∈Finset.range j,(1:ℕ) := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [read d n cap i b hi (by have := Finset.mem_range.mp hb; omega),if_pos (by have := Finset.mem_range.mp hb; omega)]
    _=j := by simp

end GroupWL.MachinePrograms.PaddedFlags
