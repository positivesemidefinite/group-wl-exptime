import GroupWL.MachinePrograms.TupleTargets

/-! The two generated target blocks are precisely the indexed WL input. -/
namespace GroupWL.MachinePrograms.TupleTargets
open IndexedRefinement IndexedTuples

theorem word_length (n k b offset : ℕ) : (word n k b offset).length=(n^k*b)*k := List.length_ofFn

theorem word_read_coordinates (n k b offset : ℕ) (row : Fin (n^k)) (slot : Fin b) (i : Fin k) :
    IndexedRefinement.read (word n k b offset) (address k b row.val slot.val i.val)=
      offset+if slot.val<n then replaceCode n row.val i.val slot.val else row.val := by
  have hk : 0<k := by have := i.isLt; omega
  have hb : 0<b := by have := slot.isLt; omega
  have hz : address k b row.val slot.val i.val<(n^k*b)*k :=
    (finProdFinEquiv (finProdFinEquiv (row,slot),i)).isLt
  simp only [IndexedRefinement.read,word,List.getElem?_ofFn,dif_pos hz,Option.getD_some,value]
  simp [address,Nat.add_mul_div_left _ _ hk,Nat.add_mul_div_left _ _ hb,
    Nat.add_mul_mod_self_left,Nat.div_eq_of_lt i.isLt,Nat.div_eq_of_lt slot.isLt,
    Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt slot.isLt]

theorem append_words_read (n m k b : ℕ) (row : Fin (n^k+m^k)) (slot : Fin b) (i : Fin k) :
    IndexedRefinement.read (word n k b 0++word m k b (n^k)) (address k b row.val slot.val i.val)=
      IndexedTuples.target n m k row.val slot.val i.val := by
  obtain ⟨side,rfl⟩ := finSumFinEquiv.surjective row
  cases side with
  | inl row =>
    have hz : address k b row.val slot.val i.val<(word n k b 0).length := by
      rw [word_length]
      exact (finProdFinEquiv (finProdFinEquiv (row,slot),i)).isLt
    change IndexedRefinement.read (word n k b 0++word m k b (n^k))
      (address k b row.val slot.val i.val)=_
    rw [IndexedRefinement.read,List.getElem?_append_left hz]
    change IndexedRefinement.read (word n k b 0) (address k b row.val slot.val i.val)=_
    rw [word_read_coordinates]
    simp [IndexedTuples.target,row.isLt]
  | inr row =>
    change IndexedRefinement.read (word n k b 0++word m k b (n^k))
      (address k b (n^k+row.val) slot.val i.val)=
        IndexedTuples.target n m k (n^k+row.val) slot.val i.val
    have hz : address k b (n^k+row.val) slot.val i.val=
        (word n k b 0).length+address k b row.val slot.val i.val := by rw [word_length]; unfold address; ring
    rw [hz,IndexedRefinement.read,List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
    change IndexedRefinement.read (word m k b (n^k)) (address k b row.val slot.val i.val)=_
    rw [word_read_coordinates]
    simp only [IndexedTuples.target,show ¬n^k+row.val<n^k by omega,if_false,Nat.add_sub_cancel_left]
    split_ifs <;> rfl

theorem targetWord_eq_append (n m k : ℕ) (hn : 0<n) :
    (IndexedTuples.data n m k hn).targetWord=
      word n k (max n m) 0++word m k (max n m) (n^k) := by
  let D := IndexedTuples.data n m k hn
  have hlen : D.targetWord.length=
      (word n k (max n m) 0++word m k (max n m) (n^k)).length := by
    simp only [Data.targetWord_length,List.length_append,word_length]
    ring
  apply List.ext_getElem hlen
  intro j hj hj'
  let z : Fin (((n^k+m^k)*max n m)*k) := ⟨j,by simpa [D] using hj⟩
  let ri := finProdFinEquiv.symm z
  let rs := finProdFinEquiv.symm ri.1
  have hz : address k (max n m) rs.1.val rs.2.val ri.2.val=j := by
    change (finProdFinEquiv (finProdFinEquiv (rs.1,rs.2),ri.2)).val=j
    have hs : finProdFinEquiv rs=ri.1 := Equiv.apply_symm_apply _ _
    change (finProdFinEquiv (finProdFinEquiv rs,ri.2)).val=j
    rw [hs]
    change (finProdFinEquiv ri).val=z.val
    exact congrArg Fin.val (Equiv.apply_symm_apply finProdFinEquiv z)
  have hl := D.targetWord_read rs.1 rs.2 ri.2
  have hr := append_words_read n m k (max n m) rs.1 rs.2 ri.2
  change IndexedRefinement.read D.targetWord (address k (max n m) rs.1.val rs.2.val ri.2.val)=_ at hl
  rw [hz] at hl hr
  have he : IndexedRefinement.read D.targetWord j=
      IndexedRefinement.read (word n k (max n m) 0++word m k (max n m) (n^k)) j := hl.trans hr.symm
  simpa only [IndexedRefinement.read,List.getElem?_eq_getElem hj,
    List.getElem?_eq_getElem hj',Option.getD_some] using he

end GroupWL.MachinePrograms.TupleTargets
