import GroupWL.MachinePrograms.KernelToTensor
import GroupWL.MachinePrograms.NatArrayMapFrames

/-! Ports only write the receiving store, so earlier arrays survive arbitrarily many stages. -/
namespace GroupWL.MachinePrograms.NatArrayLanguage.Ports
variable {R A U V : Type} [DecidableEq R] [DecidableEq A] [DecidableEq U] [DecidableEq V]
variable [Fintype R] [Fintype A] [Fintype U] [Fintype V]

private theorem input_free (s : U → Scalar R A) (a : V → Option A) (x : A) (ls : List (U⊕V)) :
    Sum.inl x ∉ (atoms (ls.map (op s a))).arrayWrites := by
  induction ls with
  | nil => simp [atoms,sequence,Program.arrayWrites]
  | cons j ls ih =>
    change Sum.inl x ∉ (op s a j).arrayWrites ∪ (atoms (ls.map (op s a))).arrayWrites
    refine Finset.notMem_union.mpr ⟨?_,ih⟩
    cases j with
    | inl u => cases hs : s u <;> simp [op,hs,Atom.arrayWrites]
    | inr v => cases ha : a v <;> simp [op,ha,Atom.arrayWrites]

theorem array_frame (first : Program R A) (s : U → Scalar R A) (a : V → Option A)
    (second : Program U V) (x : A) (h : x ∉ first.arrayWrites) :
    Sum.inl x ∉ (thenRun first s a second).arrayWrites := by
  simpa only [thenRun,Program.arrayWrites,Program.arrayWrites_map,Finset.mem_union,not_or,
    Finset.mem_image,Sum.inl.injEq,exists_eq_right,Sum.inr_ne_inl,and_false,exists_false,
    not_false_eq_true,and_true] using And.intro h (input_free s a x Finset.univ.toList)

end GroupWL.MachinePrograms.NatArrayLanguage.Ports
