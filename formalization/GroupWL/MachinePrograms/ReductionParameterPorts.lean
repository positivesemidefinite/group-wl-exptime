import GroupWL.MachinePrograms.ReductionParameters
import GroupWL.MachinePrograms.KernelToTensor

namespace GroupWL.MachinePrograms.ReductionParameters
open NatArrayLanguage Refinement
variable {R A : Type} [DecidableEq R] [DecidableEq A] [Fintype R] [Fintype A]

def ports (r : R) : Reg → Ports.Scalar R A
  | .arity => .scalar r
  | _ => .literal 0

noncomputable def after (p : NatArrayLanguage.Program R A) (r : R) (v : Version) :
    NatArrayLanguage.Program (R⊕Reg) (A⊕Empty) :=
  Ports.thenRun p (ports r) Empty.elim (program v)

theorem after_runs (p : NatArrayLanguage.Program R A) (r : R) (v : Version)
    {n m t : ℕ} {I T : Store R A} (Q : State) (hI : I.Bounded m) (hT : T.Bounded m)
    (hQ : Q.Bounded m) (first : Runs (storageBound R A m) p I t T)
    (hr : T.scalar r=n+3) (room : 146*(n+3+1)^2≤m) :
    ∃ u ≤ t+22, ∃ P, Runs (storageBound (R⊕Reg) (A⊕Empty) m) (after p r v)
      (I.join Q) u (T.join P) ∧ P.Bounded m ∧
      P.scalar .wire = CircuitGroupReduction.wireLength n ∧
      P.scalar .frame = Parameters.frameWidth (n+3) ∧
      P.scalar .dimension = CircuitGroupReduction.dimension v (n+3) := by
  have small : ∀i k, (ports (A:=A) r i)=.literal k → k≤m := by
    intro i k; cases i <;> simp [ports] <;> omega
  obtain ⟨_,bnd⟩ := Ports.code_runs (ports r) (Empty.elim : Empty → Option A) T Q m (hT.join hQ) small
  obtain ⟨u,hu,P,hp,bP,hw,hf,hk⟩ := run v n m _ bnd hr room
  have wire := Ports.thenRun_runs p (ports r) (Empty.elim : Empty → Option A) (program v)
    I T Q P m t u hI hT hQ small first hp
  have hreg : Fintype.card Reg=6 := by decide
  exact ⟨_,by simpa [hreg] using (show t+(6+u)≤t+22 by omega),P,wire,bP,hw,hf,hk⟩
end GroupWL.MachinePrograms.ReductionParameters
