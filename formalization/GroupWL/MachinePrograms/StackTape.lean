import GroupWL.MachinePrograms.Stacks

/-! A concrete multi-track, single-tape implementation of Boolean stacks.
All scans use the ordinary unit head movements of `Complexity.Machine`.
-/
namespace GroupWL.MachinePrograms.Stacks

open Complexity

abbrev Work (K : Type*) := Bool × (K → Option Bool)

def emptyWork {K : Type*} : Work K := (false, fun _ => none)

def decode {K : Type*} {a : ℕ} (e : Work K ≃ Fin a) : Symbol a → Work K
  | .inl _ => emptyWork
  | .inr x => e.symm x

def workSymbol {K : Type*} {a : ℕ} (e : Work K ≃ Fin a) (w : Work K) : Symbol a :=
  .inr (e w)

@[simp] theorem decode_workSymbol {K : Type*} {a : ℕ} (e : Work K ≃ Fin a) (w : Work K) :
    decode e (workSymbol e w) = w := e.symm_apply_apply w

@[simp] theorem decode_native {K : Type*} {a : ℕ} (e : Work K ≃ Fin a) (b : Option Bool) :
    decode e (.inl b) = emptyWork := rfl

inductive TapeControl (Q : Type*)
  | initBack | initMark | initScan | initReturn
  | normal : Q → TapeControl Q
  | go : Q → TapeControl Q
  | access : Q → TapeControl Q
  | ret : Q → TapeControl Q
  | clean : Bool → TapeControl Q
  deriving DecidableEq, Fintype

variable {K Q : Type*} [DecidableEq K] {a : ℕ}

def setColumn (e : Work K ≃ Fin a) (s : Symbol a) (k : K) (v : Option Bool) : Symbol a :=
  workSymbol e ((decode e s).1, Function.update (decode e s).2 k v)

@[simp] theorem decode_setColumn (e : Work K ≃ Fin a) (s : Symbol a) (k : K) (v : Option Bool) :
    decode e (setColumn e s k v) = ((decode e s).1, Function.update (decode e s).2 k v) := by
  simp [setColumn]

def tapeTransition (M : Machine K Q) (input output : K) (e : Work K ≃ Fin a) :
    TapeControl Q → Symbol a → (Bool ⊕ TapeControl Q) × Symbol a × Direction
  | .initBack, s => (.inr .initMark, s, .backward)
  | .initMark, _ => (.inr .initScan, workSymbol e (true, fun _ => none), .forward)
  | .initScan, .inl (some b) =>
      (.inr .initScan, workSymbol e (false, Function.update (fun _ => none) input (some b)), .forward)
  | .initScan, s => (.inr .initReturn, s, .backward)
  | .initReturn, s =>
      if (decode e s).1 then (.inr (.normal M.start), s, .stationary)
      else (.inr .initReturn, s, .backward)
  | .normal q, s => match M.instruction q with
    | .halt b => (.inr (.clean b), s, .forward)
    | _ => (.inr (.go q), s, .forward)
  | .go q, s => match M.instruction q with
    | .push k b l =>
      if ((decode e s).2 k).isNone then
        (.inr (.ret l), setColumn e s k (some b), .backward)
      else (.inr (.go q), s, .forward)
    | .pop k _ | .peek k _ =>
      if ((decode e s).2 k).isNone then (.inr (.access q), s, .backward)
      else (.inr (.go q), s, .forward)
    | .halt b => (.inl b, s, .stationary)
  | .access q, s => match M.instruction q with
    | .pop k f =>
      if (decode e s).1 then (.inr (.normal (f none)), s, .stationary)
      else (.inr (.ret (f ((decode e s).2 k))), setColumn e s k none, .backward)
    | .peek k f =>
      if (decode e s).1 then (.inr (.normal (f none)), s, .stationary)
      else (.inr (.ret (f ((decode e s).2 k))), s, .backward)
    | .push _ _ l => (.inr (.normal l), s, .stationary)
    | .halt b => (.inl b, s, .stationary)
  | .ret q, s =>
      if (decode e s).1 then (.inr (.normal q), s, .stationary)
      else (.inr (.ret q), s, .backward)
  | .clean b, s => match (decode e s).2 output with
    | none => (.inl b, .inl none, .stationary)
    | some bit => (.inr (.clean b), .inl (some bit), .forward)

def tapeProgram (M : Machine K Q) (input output : K) (e : Work K ≃ Fin a) :
    Program (TapeControl Q) a :=
  ⟨.initBack, tapeTransition M input output e⟩

/-- The bottom mark is at -1. Stack entries are stored from bottom to top in
nonnegative cells, with a separate track for every stack. Empty work cells and
ordinary blank cells are both permitted. -/
def Encodes (e : Work K ≃ Fin a) (S : K → List Bool) (cells : ℤ → Symbol a) : Prop :=
  (∀ i, (decode e (cells i)).1 = decide (i = -1)) ∧
  (∀ k (i : ℕ), (decode e (cells i)).2 k = (S k).reverse[i]?)

theorem Encodes.bottom {e : Work K ≃ Fin a} {S : K → List Bool} {cells : ℤ → Symbol a}
    (h : Encodes e S cells) : (decode e (cells (-1))).1 = true := by
  simpa using h.1 (-1)

theorem Encodes.not_bottom {e : Work K ≃ Fin a} {S : K → List Bool} {cells : ℤ → Symbol a}
    (h : Encodes e S cells) (i : ℕ) : (decode e (cells i)).1 = false := by
  simpa using h.1 (i : ℤ)

theorem Encodes.end_column {e : Work K ≃ Fin a} {S : K → List Bool} {cells : ℤ → Symbol a}
    (h : Encodes e S cells) (k : K) :
    (decode e (cells (S k).length)).2 k = none := by
  rw [h.2, List.getElem?_eq_none (by simp)]

theorem Encodes.column_isSome {e : Work K ≃ Fin a} {S : K → List Bool} {cells : ℤ → Symbol a}
    (h : Encodes e S cells) (k : K) (i : ℕ) (hi : i < (S k).length) :
    ((decode e (cells i)).2 k).isNone = false := by
  rw [h.2, List.getElem?_eq_getElem (by simpa using hi)]
  rfl

theorem Encodes.update_column {e : Work K ≃ Fin a} {S : K → List Bool} {cells : ℤ → Symbol a}
    (h : Encodes e S cells) (k : K) (i : ℕ) (v : Option Bool) (L : List Bool)
    (hL : ∀ j, L.reverse[j]? = if j = i then v else (S k).reverse[j]?) :
    Encodes e (Function.update S k L)
      (Function.update cells (i : ℤ) (setColumn e (cells i) k v)) := by
  constructor
  · intro z
    by_cases hz : z = (i : ℤ)
    · subst z
      simpa only [Function.update_self, decode_setColumn] using h.1 (i : ℤ)
    · simpa only [Function.update_of_ne hz] using h.1 z
  · intro l j
    by_cases hj : j = i
    · subst j
      rw [Function.update_self, decode_setColumn]
      simp only [Prod.snd]
      by_cases hl : l = k
      · subst l
        rw [Function.update_self, Function.update_self, hL]
        simp
      · rw [Function.update_of_ne hl, Function.update_of_ne hl]
        exact h.2 l i
    · have hj' : (j : ℤ) ≠ (i : ℤ) := by exact_mod_cast hj
      rw [Function.update_of_ne hj']
      by_cases hl : l = k
      · subst l
        rw [Function.update_self, hL, if_neg hj]
        exact h.2 k j
      · rw [Function.update_of_ne hl]
        exact h.2 l j

theorem reverse_cons_get (b : Bool) (L : List Bool) (j : ℕ) :
    (b :: L).reverse[j]? = if j = L.length then some b else L.reverse[j]? := by
  rw [List.reverse_cons]
  by_cases hj : j = L.length
  · subst j
    rw [← List.length_reverse, List.getElem?_concat_length]
    simp
  · rw [if_neg hj]
    by_cases hlt : j < L.length
    · exact List.getElem?_append_left (by simpa using hlt)
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]

theorem Encodes.push {e : Work K ≃ Fin a} {S : K → List Bool} {cells : ℤ → Symbol a}
    (h : Encodes e S cells) (k : K) (b : Bool) :
    Encodes e (Function.update S k (b :: S k))
      (Function.update cells ((S k).length : ℤ) (setColumn e (cells (S k).length) k (some b))) :=
  h.update_column k _ _ _ (reverse_cons_get b (S k))

theorem Encodes.pop {e : Work K ≃ Fin a} {S : K → List Bool} {cells : ℤ → Symbol a}
    (h : Encodes e S cells) (k : K) (b : Bool) (L : List Bool) (hk : S k = b :: L) :
    Encodes e (Function.update S k L)
      (Function.update cells (L.length : ℤ) (setColumn e (cells L.length) k none)) := by
  apply h.update_column
  intro j
  by_cases hj : j = L.length
  · subst j
    simp
  · rw [if_neg hj, hk, reverse_cons_get, if_neg hj]

theorem return_scan (M : Machine K Q) (input output : K) (e : Work K ≃ Fin a)
    (S : K → List Bool) (cells : ℤ → Symbol a) (h : Encodes e S cells) (q : Q) (n : ℕ) :
    (tapeProgram M input output e).run ⟨.inr (.ret q), (n : ℤ)-1, cells⟩ (n+1) =
      ⟨.inr (.normal q), -1, cells⟩ := by
  have hs := (tapeProgram M input output e).run_scan (.ret q) ((n : ℤ)-1) cells .backward n
    (by
      intro i hi
      have hn : (n : ℤ) - 1 + (i : ℤ) * Direction.backward.offset ≠ -1 := by
        simp only [Direction.offset]
        omega
      simp [tapeProgram, tapeTransition, h.1, hn])
  have hp : (n : ℤ)-1 + (n : ℤ) * Direction.backward.offset = -1 := by
    simp only [Direction.offset]
    ring
  rw [hp] at hs
  rw [Program.run, hs]
  simp [Program.tick, tapeProgram, tapeTransition, h.bottom, Direction.offset,
    Function.update_eq_self]

def Instruction.stack : Instruction K Q → Option K
  | .push k _ _ | .pop k _ | .peek k _ => some k
  | .halt _ => none

theorem go_scan (M : Machine K Q) (input output : K) (e : Work K ≃ Fin a)
    (S : K → List Bool) (cells : ℤ → Symbol a) (h : Encodes e S cells) (q : Q) (k : K)
    (hq : (M.instruction q).stack = some k) :
    (tapeProgram M input output e).run ⟨.inr (.go q), 0, cells⟩ (S k).length =
      ⟨.inr (.go q), (S k).length, cells⟩ := by
  have hs := (tapeProgram M input output e).run_scan (.go q) 0 cells .forward (S k).length
    (by
      intro i hi
      have ht := h.column_isSome k i hi
      cases he : M.instruction q with
      | push l b q' =>
        have hl : l = k := by simpa [he, Instruction.stack] using hq
        subst l
        simp [tapeProgram, tapeTransition, he, Direction.offset, ht]
      | pop l f =>
        have hl : l = k := by simpa [he, Instruction.stack] using hq
        subst l
        simp [tapeProgram, tapeTransition, he, Direction.offset, ht]
      | peek l f =>
        have hl : l = k := by simpa [he, Instruction.stack] using hq
        subst l
        simp [tapeProgram, tapeTransition, he, Direction.offset, ht]
      | halt b => simp [he, Instruction.stack] at hq)
  simpa [Direction.offset] using hs

end GroupWL.MachinePrograms.Stacks
