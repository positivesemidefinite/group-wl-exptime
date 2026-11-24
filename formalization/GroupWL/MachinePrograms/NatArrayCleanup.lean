import GroupWL.MachinePrograms.NatArrayEncoding
import GroupWL.MachinePrograms.StackLibrary

/-! A fixed finite scratch cleanup converts atom bodies into composable code.
All cleanup instructions and their execution costs are accounted for. -/
namespace GroupWL.MachinePrograms.NatArrayLowering

open NatArrayLanguage
open scoped BigOperators

variable {Reg Arr : Type*} [DecidableEq Reg] [DecidableEq Arr]
  [Fintype Reg] [Fintype Arr]

theorem wordSize_run_le {p : Structured.Program (StackIndex Reg Arr)}
    {S T : Structured.Store (StackIndex Reg Arr)} {t : ℕ}
    (h : Structured.Runs p S t T) : wordSize T ≤ wordSize S+t+1 := by
  have growth (n : ℕ) (c : Stacks.Config (StackIndex Reg Arr) (Structured.Label p ⊕ Unit)) :
      Stacks.size ((Stacks.step (Structured.compile p true))^[n] c) ≤ Stacks.size c+n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (Stacks.size_step _ _).trans (by omega)
  have hh := growth (t+1) (Structured.active (Structured.compile p true).start S)
  rw [Structured.compile_runs h true] at hh
  exact hh

theorem wordSize_update_empty (S : Structured.Store (StackIndex Reg Arr))
    (k : StackIndex Reg Arr) :
    wordSize (Function.update S k []) + (S k).length = wordSize S := by
  simp only [wordSize, Stacks.length_update, List.length_nil]
  rw [Finset.sum_update_of_mem (Finset.mem_univ k)]
  simp only [Finset.sdiff_singleton_eq_erase, Nat.zero_add]
  exact Finset.sum_erase_add Finset.univ (fun j => (S j).length) (Finset.mem_univ k)

def clearList : List (StackIndex Reg Arr) → Structured.Program (StackIndex Reg Arr)
  | [] => .skip
  | k::ks => .seq (Structured.clear k) (clearList ks)

def resetList : List (StackIndex Reg Arr) → Structured.Store (StackIndex Reg Arr) →
    Structured.Store (StackIndex Reg Arr)
  | [], S => S
  | k::ks, S => resetList ks (Function.update S k [])

theorem resetList_cons (k : StackIndex Reg Arr) (ks : List (StackIndex Reg Arr))
    (S : Structured.Store (StackIndex Reg Arr)) :
    resetList ks (Function.update S k []) = resetList (k::ks) S := rfl

theorem resetList_of_not_mem (ks : List (StackIndex Reg Arr))
    (S : Structured.Store (StackIndex Reg Arr)) (j : StackIndex Reg Arr) (h : j ∉ ks) :
    resetList ks S j = S j := by
  induction ks generalizing S with
  | nil => rfl
  | cons k ks ih =>
    rw [resetList, ih _ (fun hj => h (List.mem_cons_of_mem k hj))]
    exact Function.update_of_ne (fun hj => h (List.mem_cons.mpr (.inl hj))) _ _

theorem resetList_of_mem (ks : List (StackIndex Reg Arr))
    (S : Structured.Store (StackIndex Reg Arr)) (j : StackIndex Reg Arr) (h : j ∈ ks) :
    resetList ks S j = [] := by
  induction ks generalizing S with
  | nil => simp at h
  | cons k ks ih =>
    rw [resetList]
    classical
    by_cases hj : j ∈ ks
    · exact ih _ hj
    · rw [resetList_of_not_mem _ _ _ hj]
      have he : j = k := (List.mem_cons.mp h).resolve_right hj
      subst j
      exact Function.update_self ..

theorem clearList_runs (ks : List (StackIndex Reg Arr))
    (S : Structured.Store (StackIndex Reg Arr)) :
    ∃ t, t + 2*wordSize (resetList ks S) ≤ 2*wordSize S+ks.length ∧
      Structured.Runs (clearList ks) S t (resetList ks S) := by
  induction ks generalizing S with
  | nil => exact ⟨0, by simp [resetList], by simpa [clearList, resetList] using Structured.Runs.skip S⟩
  | cons k ks ih =>
    obtain ⟨t, ht, hr⟩ := ih (Function.update S k [])
    rw [resetList_cons] at ht hr
    refine ⟨2*(S k).length+1+t, ?_, .seq (Structured.clear_runs S k) hr⟩
    have hs := wordSize_update_empty S k
    simp only [List.length_cons]
    omega

def cleanup : Structured.Program (StackIndex Reg Arr) :=
  clearList (List.ofFn (scratchSlot (Reg := Reg) (Arr := Arr)))

theorem cleanup_runs (S : Structured.Store (StackIndex Reg Arr)) :
    ∃ t ≤ 2*wordSize S+16, Structured.Runs cleanup S t (resetScratch S) := by
  obtain ⟨t, ht, hr⟩ := clearList_runs
    (List.ofFn (scratchSlot (Reg := Reg) (Arr := Arr))) S
  have he : resetList (List.ofFn (scratchSlot (Reg := Reg) (Arr := Arr))) S =
      resetScratch S := by
    funext k
    rcases k with k | i
    · apply resetList_of_not_mem
      simp only [List.mem_ofFn, scratchSlot]
      simp
    · apply resetList_of_mem
      exact List.mem_ofFn.mpr ⟨i, rfl⟩
  rw [he] at ht hr
  refine ⟨t, ?_, hr⟩
  simp only [List.length_ofFn] at ht
  omega

def BodyCode.toAtomCode {a : Atom Reg Arr} (b : BodyCode a) : AtomCode a where
  program := .seq b.body cleanup
  correct := by
    intro S B hv hb ha
    obtain ⟨t, ht, T, hr, hT⟩ := b.correct S B hv hb ha
    obtain ⟨u, hu, hc⟩ := cleanup_runs T
    refine ⟨t+u, ?_, ?_⟩
    · have hg := wordSize_run_le hr
      have hs := encodeStore_size_le S
      have hpow : B+1 ≤ (B+1)^3 := by nlinarith [sq_nonneg (B+1 : ℤ)]
      have hp : (B+1)^3 ≤ (B+1)^4 := by
        simpa only [pow_succ] using Nat.le_mul_of_pos_right ((B+1)^3) (by omega : 0 < B+1)
      nlinarith
    · rw [hT.reset] at hc
      exact .seq hr hc

end GroupWL.MachinePrograms.NatArrayLowering
