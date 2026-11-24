import GroupWL.MachinePrograms.NatArrayCleanup

/-! Structural lowering of bounded natural-array executions to actual fixed
Boolean-stack programs. Every source guard is a single stack peek. -/
namespace GroupWL.MachinePrograms.NatArrayLowering

open NatArrayLanguage

variable {Reg Arr : Type*} [DecidableEq Reg] [DecidableEq Arr]
  [Fintype Reg] [Fintype Arr]

def lower (atoms : ∀ a : Atom Reg Arr, AtomCode a) :
    NatArrayLanguage.Program Reg Arr → Structured.Program (StackIndex Reg Arr)
  | .skip => .skip
  | .atom a => (atoms a).program
  | .seq p q => .seq (lower atoms p) (lower atoms q)
  | .branch r p q => .peek (scalarSlot r) (lower atoms q) (lower atoms p) (lower atoms p)
  | .while r p => .while (scalarSlot r) Option.isSome (lower atoms p)

theorem scalar_head_zero (S : Store Reg Arr) (r : Reg) (h : S.scalar r = 0) :
    (encodeStore S (scalarSlot r)).head? = none := by
  simp [h]

theorem scalar_head_nonzero (S : Store Reg Arr) (r : Reg) (h : S.scalar r ≠ 0) :
    (encodeStore S (scalarSlot r)).head? = some true := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero h
  simp [hn, List.replicate_succ]

theorem lower_runs (atoms : ∀ a : Atom Reg Arr, AtomCode a)
    {B : ℕ} {p : NatArrayLanguage.Program Reg Arr} {S T : Store Reg Arr} {t : ℕ}
    (h : NatArrayLanguage.Runs B p S t T) :
    ∃ u ≤ (10000*(B+1)^4)*t,
      Structured.Runs (lower atoms p) (encodeStore S) u (encodeStore T) := by
  have hcost : 1 ≤ 10000*(B+1)^4 := by
    have hp : 1 ≤ (B+1)^4 := one_le_pow₀ (by omega)
    omega
  induction h with
  | skip hs => exact ⟨0, by simp, Structured.Runs.skip _⟩
  | atom hv hb ha =>
    obtain ⟨u, hu, hr⟩ := (atoms _).correct _ B hv hb ha
    exact ⟨u, by simpa using hu, hr⟩
  | seq hp hq ihp ihq =>
    obtain ⟨u, hu, hrp⟩ := ihp
    obtain ⟨v, hv, hrq⟩ := ihq
    refine ⟨u+v, ?_, .seq hrp hrq⟩
    nlinarith
  | branch_nonzero hn hp ih =>
    obtain ⟨u, hu, hr⟩ := ih
    refine ⟨u+1, by nlinarith, ?_⟩
    apply Structured.Runs.peek
    simpa only [scalar_head_nonzero _ _ hn, Structured.select] using hr
  | branch_zero hz hq ih =>
    obtain ⟨u, hu, hr⟩ := ih
    refine ⟨u+1, by nlinarith, ?_⟩
    apply Structured.Runs.peek
    simpa only [scalar_head_zero _ _ hz, Structured.select] using hr
  | while_zero hz hs =>
    refine ⟨1, by simpa using hcost, ?_⟩
    exact Structured.Runs.while_false (by simp only [scalar_head_zero _ _ hz, Option.isSome_none])
  | while_nonzero hn hp hrest ihp ihr =>
    obtain ⟨u, hu, hrp⟩ := ihp
    obtain ⟨v, hv, hrr⟩ := ihr
    refine ⟨u+v+1, by nlinarith, ?_⟩
    exact Structured.Runs.while_true
      (by simp only [scalar_head_nonzero _ _ hn, Option.isSome_some]) hrp hrr

end GroupWL.MachinePrograms.NatArrayLowering
