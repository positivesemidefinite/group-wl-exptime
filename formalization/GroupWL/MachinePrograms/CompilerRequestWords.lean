import GroupWL.MachinePrograms.CompilerBlankRequests
import GroupWL.FiniteCodeEnumeration

/-! The executable request streams have the exact canonical finite-code order. -/
namespace GroupWL.MachinePrograms.Structured

open AddressedCircuit BinaryAddress BinaryIntervals CircuitDescription MachineCellular Complexity

theorem initialBitWords_ofFn (M : Machine) (d n : ℕ) (w : List Bool) :
    initialBitWords M d n w =
      (List.ofFn (fun i : Fin w.length => initialPositionWord M d (n+i.val) w[i.val]?)).flatten := by
  induction w generalizing n with
  | nil => simp [initialBitWords]
  | cons b w ih =>
    simp only [initialBitWords,List.length_cons,List.ofFn_succ,List.flatten_cons,Fin.val_zero,
      Nat.add_zero,List.getElem?_cons_zero,Fin.val_succ,List.getElem?_cons_succ]
    rw [ih]
    congr 3
    funext i
    congr 1
    omega

theorem initialWords_ofFn (M : Machine) (d : ℕ) (w : List Bool) :
    initialWords M d w =
      (List.ofFn (fun i : Fin (w.length+1) => initialPositionWord M d i.val w[i.val]?)).flatten := by
  rw [initialWords,initialBitWords_ofFn]
  rw [List.ofFn_succ_last]
  simp [List.flatten_append,List.getElem?_eq_none,Fin.val_castSucc]

theorem cyclicInitial_initialLetter (M : Machine) (w : List Bool) (d n : ℕ) (hn : n < 2^d) :
    cyclicInitial M w (2^d) (n : ZMod (2^d)) = initialLetter M n w[n]? := by
  dsimp only [cyclicInitial,encode,initial,initialLetter]
  simp [ZMod.val_natCast,Nat.mod_eq_of_lt hn]

theorem initialWords_canonical (M : Machine) (w : List Bool) (d : ℕ) (hw : w.length+1 < 2^d) :
    initialWords M d w =
      (List.ofFn (fun i : Fin (w.length+1) => requestWord
        (⟨CellularTableau.Gate.scalar (MachineCircuit.seedRequest M w d (.inl i)).letter,
          (MachineCircuit.seedRequest M w d (.inl i)).domain⟩ :
          Request (CellularTableau.Gate (Cell M)) (d+d)))).flatten := by
  rw [initialWords_ofFn]
  congr 2
  funext i
  simp only [initialPositionWord,requestWord,MachineCircuit.seedRequest,
    cyclicInitial_initialLetter M w d i.val (by omega)]

theorem blankSequence_ofFn (M : Machine) {d : ℕ} (a : Address d) (j m : ℕ) :
    blankSequence M a j m = (List.ofFn (fun i : Fin m => blankAt M a (j+i.val))).flatten := by
  induction m generalizing j with
  | zero => simp [blankSequence]
  | succ m ih =>
    simp only [blankSequence,List.ofFn_succ,List.flatten_cons,Fin.val_zero,Nat.add_zero,Fin.val_succ]
    rw [ih]
    congr 3
    funext i
    congr 1
    omega

theorem blankWords_ofFn (M : Machine) {d : ℕ} (a : Address d) :
    blankWords M a = (List.ofFn (fun i : Fin (FiniteCode.size (Option (Fin d))) =>
      blankPositionWord M a ((FiniteCode.equiv (α := Option (Fin d))).symm i))).flatten := by
  rw [FiniteCode.ofFn_option (fun h : Option (Fin d) => blankPositionWord M a h)]
  simp only [List.flatten_cons,blankWords,blankSequence_ofFn,Nat.zero_add]
  congr 3
  funext i
  simp [blankAt,i.isLt]
  rfl

theorem seedWords_canonical (M : Machine) (w : List Bool) (d : ℕ) (hw : w.length+1 < 2^d) :
    initialWords M d w++blankWords M (ofNat d (w.length+1)) =
      arrayWord requestWord (MachineCircuit.compile M w d).seed := by
  change _ = (List.ofFn (fun i => requestWord
    (⟨CellularTableau.Gate.scalar (MachineCircuit.seedRequest M w d
      ((FiniteCode.equiv (α := MachineCircuit.SeedIndex w d)).symm i)).letter,
      (MachineCircuit.seedRequest M w d
        ((FiniteCode.equiv (α := MachineCircuit.SeedIndex w d)).symm i)).domain⟩ :
        Request (CellularTableau.Gate (Cell M)) (d+d)))).flatten
  rw [FiniteCode.ofFn_sum (fun i : MachineCircuit.SeedIndex w d => requestWord
    (⟨CellularTableau.Gate.scalar (MachineCircuit.seedRequest M w d i).letter,
      (MachineCircuit.seedRequest M w d i).domain⟩ :
      Request (CellularTableau.Gate (Cell M)) (d+d))),List.flatten_append]
  rw [initialWords_canonical M w d hw,blankWords_ofFn]
  rfl

end GroupWL.MachinePrograms.Structured
