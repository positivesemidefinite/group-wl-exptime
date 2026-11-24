import GroupWL.MachinePrograms.NatArrayExecution
import GroupWL.MachinePrograms.NatArrayBudgets

/-! Operational complexity consequences of the complete concrete array
compiler, including raw input and output. -/
namespace GroupWL.MachinePrograms.NatArrayLowering

open NatArrayLanguage Complexity

variable {Reg Arr : Type*} [DecidableEq Reg] [DecidableEq Arr]
  [Fintype Reg] [Fintype Arr]

theorem computesBy_polynomial (p : NatArrayLanguage.Program Reg Arr) (input output : Arr)
    (f : BitString → BitString) (c d : ℕ)
    (h : ∀ w, ∃ B t S, B ≤ c*(w.length+1)^d ∧ t ≤ c*(w.length+1)^d ∧
      Runs B p (inputStore input w) t S ∧ S.array output = (f w).map bitNat) :
    ComputesBy (functionMachine p input output) f
      (fun n => (10*(200000*(c+1)^5+2)^2)*(n+1)^(2*(5*(d+1)+1))) := by
  apply Structured.computesBy_polynomial (functionProgram p input output)
    (scratchSlot 15) (scratchSlot 14) f (200000*(c+1)^5) (5*(d+1))
  intro w
  obtain ⟨B,t,S,hB,ht,hr,ho⟩ := h w
  obtain ⟨T,u,hu,hT,hv⟩ := functionProgram_runs hr ho
  exact ⟨T,u,hu.trans (ioBudget_le_polynomial hB ht),hT,hv⟩

theorem polynomialReduction (p : NatArrayLanguage.Program Reg Arr) (input output : Arr)
    (f : BitString → BitString) (c d : ℕ)
    (h : ∀ w, ∃ B t S, B ≤ c*(w.length+1)^d ∧ t ≤ c*(w.length+1)^d ∧
      Runs B p (inputStore input w) t S ∧ S.array output = (f w).map bitNat)
    (L U : Language) (hf : ∀w,w ∈ L ↔ f w ∈ U) : PolynomialReduction L U :=
  ⟨functionMachine p input output,f,10*(200000*(c+1)^5+2)^2,2*(5*(d+1)+1),
    computesBy_polynomial p input output f c d h,hf⟩

theorem inEXPTIME (p : NatArrayLanguage.Program Reg Arr) (input : Arr) (result : Reg)
    (L : Language) (c d : ℕ)
    (h : ∀ w, ∃ B t S, B ≤ 2^(c*(w.length+1)^d) ∧ t ≤ 2^(c*(w.length+1)^d) ∧
      Runs B p (inputStore input w) t S ∧ (S.scalar result ≠ 0 ↔ w ∈ L)) :
    InEXPTIME L := by
  apply Structured.inEXPTIME (decisionProgram p input) (scratchSlot 15)
    (scalarSlot result) Option.isSome L (5*c+23) (d+1)
  intro w
  obtain ⟨B,t,S,hB,ht,hr,hL⟩ := h w
  obtain ⟨u,hu,hT⟩ := decisionProgram_runs hr
  refine ⟨encodeStore S,u,?_,hT,?_⟩
  · apply (show u ≤ ioBudget w.length B t by unfold ioBudget; omega).trans
    exact ioBudget_le_exponential hB ht
  · simpa only [encodeStore_nonzero] using hL

end GroupWL.MachinePrograms.NatArrayLowering
