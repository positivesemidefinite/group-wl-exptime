import GroupWL.MachinePrograms.StackTape

/-! Exact initialization and output-cleanup costs for the single-tape stack
implementation. Both scans use the concrete unit-step transition function. -/
namespace GroupWL.MachinePrograms.Stacks

open Complexity

variable {K Q : Type*} [DecidableEq K] {a : ℕ}

def preprocessCells (e : Work K ≃ Fin a) (input : K) (w : BitString)
    (n : ℕ) (z : ℤ) : Symbol a :=
  if z = -1 then workSymbol e (true,fun _ => none)
  else if 0 ≤ z then
    if z.toNat < n then workSymbol e (false,Function.update (fun _ => none) input w[z.toNat]?)
    else .inl w[z.toNat]?
  else .inl none

@[simp] theorem preprocessCells_current (e : Work K ≃ Fin a) (input : K) (w : BitString)
    (n : ℕ) : preprocessCells e input w n (n : ℤ) = .inl w[n]? := by
  simp [preprocessCells]

theorem preprocessCells_step (e : Work K ≃ Fin a) (input : K) (w : BitString)
    (n : ℕ) :
    Function.update (preprocessCells e input w n) (n : ℤ)
      (workSymbol e (false,Function.update (fun _ => none) input w[n]?)) =
    preprocessCells e input w (n+1) := by
  funext z
  by_cases hz : z=(n : ℤ)
  · subst z
    simp [preprocessCells]
  · rw [Function.update_of_ne hz]
    by_cases hm : z = -1
    · simp [preprocessCells,hm]
    · by_cases hp : 0 ≤ z
      · have hn : z.toNat ≠ n := by omega
        have hl : (z.toNat < n+1) ↔ z.toNat < n := by omega
        simp only [preprocessCells,if_neg hm,if_pos hp,hl]
      · simp [preprocessCells,hm,hp]

theorem preprocessCells_encodes (e : Work K ≃ Fin a) (input : K) (w : BitString) :
    Encodes e (Function.update (fun _ => []) input w.reverse)
      (preprocessCells e input w w.length) := by
  constructor
  · intro z
    by_cases hm : z = -1
    · simp [preprocessCells,hm]
    · by_cases hp : 0 ≤ z
      · by_cases hn : z.toNat < w.length <;> simp [preprocessCells,hm,hp,hn,emptyWork]
      · simp [preprocessCells,hm,hp,emptyWork]
  · intro k i
    by_cases hk : k=input
    · subst k
      by_cases hi : i < w.length
      · simp [preprocessCells,hi]
      · simp [preprocessCells,hi,emptyWork]
    · by_cases hi : i < w.length
      · simp [preprocessCells,hi,Function.update_of_ne hk]
      · simp [preprocessCells,hi,Function.update_of_ne hk,emptyWork]

variable (M : Machine K Q) (input output : K) (e : Work K ≃ Fin a)

theorem preprocess_scan (w : BitString) (n : ℕ) (hn : n ≤ w.length) :
    (tapeProgram M input output e).run
      ⟨.inr .initScan,0,preprocessCells e input w 0⟩ n =
      ⟨.inr .initScan,(n : ℤ),preprocessCells e input w n⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Program.run,ih (by omega)]
      have hg : w[n]? = some w[n] := List.getElem?_eq_getElem (by omega)
      simp only [Program.tick,tapeProgram,tapeTransition,preprocessCells_current,hg,
        Direction.offset]
      have ht := preprocessCells_step e input w n
      rw [hg] at ht
      rw [ht]
      congr 1

theorem preprocess_start (w : BitString) :
    (tapeProgram M input output e).execute w 2 =
      ⟨.inr .initScan,0,preprocessCells e input w 0⟩ := by
  simp only [Program.execute,Program.run,Program.initial,Program.tick,
    tapeProgram,tapeTransition,Direction.offset,Function.update_eq_self]
  apply MachinePrograms.Config.ext
  · rfl
  · norm_num
  · funext z
    by_cases hm : z = -1
    · subst z
      simp [preprocessCells]
    · simp [preprocessCells,hm]

theorem preprocess_return (S : K → List Bool) (cells : ℤ → Symbol a)
    (h : Encodes e S cells) (n : ℕ) :
    (tapeProgram M input output e).run ⟨.inr .initReturn,(n : ℤ)-1,cells⟩ (n+1) =
      ⟨.inr (.normal M.start),-1,cells⟩ := by
  have hs := (tapeProgram M input output e).run_scan .initReturn ((n : ℤ)-1) cells .backward n
    (by
      intro i hi
      have hn : (n : ℤ)-1+(i : ℤ)*Direction.backward.offset ≠ -1 := by
        simp only [Direction.offset]
        omega
      simp [tapeProgram,tapeTransition,h.1,hn])
  have hp : (n : ℤ)-1+(n : ℤ)*Direction.backward.offset = -1 := by
    simp only [Direction.offset]
    ring
  rw [hp] at hs
  rw [Program.run,hs]
  simp [Program.tick,tapeProgram,tapeTransition,h.bottom,Direction.offset,Function.update_eq_self]

/-- Preprocessing includes the boundary mark, the input scan, and the return
to the mark. It uses exactly twice the input length plus four tape steps. -/
theorem initialize_tape (w : BitString) :
    ∃ cells, (tapeProgram M input output e).execute w (2*w.length+4) =
      ⟨.inr (.normal M.start),-1,cells⟩ ∧
      Encodes e (Function.update (fun _ => []) input w.reverse) cells := by
  let cells := preprocessCells e input w w.length
  have henc := preprocessCells_encodes e input w
  have hend : (tapeProgram M input output e).run
      ⟨.inr .initScan,(w.length : ℤ),cells⟩ 1 =
      ⟨.inr .initReturn,(w.length : ℤ)-1,cells⟩ := by
    have hc : cells (w.length : ℤ) = .inl none := by simp [cells]
    simp only [Program.run,Program.tick,tapeProgram,hc,tapeTransition,Direction.offset]
    rw [← hc,Function.update_eq_self]
    rfl
  refine ⟨cells,?_,henc⟩
  have ht : 2*w.length+4 = ((2+w.length)+1)+(w.length+1) := by omega
  rw [ht,Program.execute,
    (tapeProgram M input output e).run_add _ (2+w.length+1) (w.length+1),
    (tapeProgram M input output e).run_add _ (2+w.length) 1,
    (tapeProgram M input output e).run_add _ 2 w.length]
  change (tapeProgram M input output e).run
    ((tapeProgram M input output e).run
      ((tapeProgram M input output e).run
        ((tapeProgram M input output e).execute w 2) w.length) 1) (w.length+1) = _
  rw [preprocess_start,preprocess_scan _ _ _ _ _ _ (le_refl _),hend]
  exact preprocess_return M input output e _ cells henc w.length

def cleanupCells (cells : ℤ → Symbol a) (w : BitString) (n : ℕ) (z : ℤ) : Symbol a :=
  if 0 ≤ z ∧ z.toNat < n then .inl w[z.toNat]? else cells z

@[simp] theorem cleanupCells_zero (cells : ℤ → Symbol a) (w : BitString) :
    cleanupCells cells w 0 = cells := by funext z; simp [cleanupCells]

@[simp] theorem cleanupCells_current (cells : ℤ → Symbol a) (w : BitString) (n : ℕ) :
    cleanupCells cells w n (n : ℤ) = cells n := by simp [cleanupCells]

theorem cleanupCells_step (cells : ℤ → Symbol a) (w : BitString) (n : ℕ) :
    Function.update (cleanupCells cells w n) (n : ℤ) (.inl w[n]?) =
      cleanupCells cells w (n+1) := by
  funext z
  by_cases hz : z=(n : ℤ)
  · subst z
    simp [cleanupCells]
  · rw [Function.update_of_ne hz]
    by_cases hp : 0 ≤ z
    · have hn : z.toNat ≠ n := by omega
      have hl : (z.toNat < n+1) ↔ z.toNat < n := by omega
      simp only [cleanupCells,hp,true_and,hl]
    · simp [cleanupCells,hp]

theorem cleanup_scan (S : K → List Bool) (cells : ℤ → Symbol a) (h : Encodes e S cells)
    (b : Bool) (n : ℕ) (hn : n ≤ (S output).length) :
    (tapeProgram M input output e).run ⟨.inr (.clean b),0,cells⟩ n =
      ⟨.inr (.clean b),(n : ℤ),cleanupCells cells (S output).reverse n⟩ := by
  induction n with
  | zero => simp [Program.run]
  | succ n ih =>
      rw [Program.run,ih (by omega)]
      have hi : n < (S output).reverse.length := by simpa using (show n < (S output).length by omega)
      have hg : (S output).reverse[n]? = some (S output).reverse[n] :=
        List.getElem?_eq_getElem hi
      have hd : (decode e (cleanupCells cells (S output).reverse n (n : ℤ))).2 output =
          some (S output).reverse[n] := by
        rw [cleanupCells_current,h.2,hg]
      simp only [Program.tick,tapeProgram,tapeTransition,hd,Direction.offset]
      have ht := cleanupCells_step cells (S output).reverse n
      rw [hg] at ht
      rw [ht]
      congr 1

/-- The output column is copied to native bit symbols in order, followed by
a blank. The head moves one step per bit and halts on the blank-writing step. -/
theorem cleanup_tape (S : K → List Bool) (cells : ℤ → Symbol a) (h : Encodes e S cells)
    (b : Bool) :
    ∃ final, (tapeProgram M input output e).run ⟨.inr (.clean b),0,cells⟩
        ((S output).length+1) = final ∧ final.control = .inl b ∧
      Program.Outputs final (S output).reverse := by
  let cells' := Function.update (cleanupCells cells (S output).reverse (S output).length)
    ((S output).length : ℤ) (.inl none)
  refine ⟨⟨.inl b,(S output).length,cells'⟩,?_,rfl,?_,?_⟩
  · rw [Program.run,cleanup_scan M input output e S cells h b _ (le_refl _)]
    have hd : (decode e (cleanupCells cells (S output).reverse (S output).length
        ((S output).length : ℤ))).2 output = none := by
      rw [cleanupCells_current,h.2,List.getElem?_eq_none (by simp)]
    simp only [Program.tick,tapeProgram,tapeTransition,hd,Direction.offset,add_zero]
    rfl
  · intro i
    have hi : i.val < (S output).length := by simpa using i.isLt
    have hne : (i.val : ℤ) ≠ ((S output).length : ℤ) := by omega
    change cells' (i.val : ℤ) = .inl (some (S output).reverse[i])
    simp [cells',Function.update_of_ne hne,cleanupCells,hi]
  · change cells' ((S output).reverse.length : ℤ) = .inl none
    simp [cells']

end GroupWL.MachinePrograms.Stacks
