import GroupWL.MachinePrograms.StackBackend

/-! Direct clients of the stack compiler for the operational complexity classes.
The finite alphabet/control numbering is chosen once, independently of input.
-/
namespace GroupWL.MachinePrograms.Stacks

open Complexity

variable {K Q : Type*} [DecidableEq K] [Fintype K] [Fintype Q]
variable (M : Machine K Q) (input output : K)

noncomputable def compiled : Complexity.Machine :=
  (tapeProgram M input output (Fintype.equivFin (Work K))).compile

theorem computesBy (f : BitString → BitString) (B : ℕ → ℕ)
    (h : ComputesIn M input output f B) :
    ComputesBy (compiled M input output) f (simulationBudget B) :=
  computesBy_with M input output (Fintype.equivFin (Work K))
    (Fintype.equivFin (TapeControl Q)) f B h

theorem decidesBy (L : Language) (B : ℕ → ℕ)
    (h : DecidesIn M input L B) :
    DecidesBy (compiled M input output) L (simulationBudget B) :=
  decidesBy_with M input output (Fintype.equivFin (Work K))
    (Fintype.equivFin (TapeControl Q)) L B h

theorem computesBy_polynomial (f : BitString → BitString) (c d : ℕ)
    (h : ComputesIn M input output f (fun n => c*(n+1)^d)) :
    ComputesBy (compiled M input output) f
      (fun n => (10*(c+1)^2) * (n+1)^(2*(d+1))) :=
  (computesBy M input output f _ h).mono (simulationBudget_polynomial c d)

theorem decidesBy_exponential (L : Language) (c d : ℕ)
    (h : DecidesIn M input L (fun n => 2^(c*(n+1)^d))) :
    DecidesBy (compiled M input output) L (fun n => 2^((2*c+6)*(n+1)^(d+1))) :=
  (decidesBy M input output L _ h).mono (simulationBudget_exponential c d)

theorem inEXPTIME (L : Language) (c d : ℕ)
    (h : DecidesIn M input L (fun n => 2^(c*(n+1)^d))) : InEXPTIME L :=
  ⟨compiled M input input, 2*c+6, d+1, decidesBy_exponential M input input L c d h⟩

theorem polynomialReduction (f : BitString → BitString) (c d : ℕ)
    (h : ComputesIn M input output f (fun n => c*(n+1)^d)) (L S : Language)
    (hf : ∀ w, w ∈ L ↔ f w ∈ S) : PolynomialReduction L S :=
  ⟨compiled M input output, f, 10*(c+1)^2, 2*(d+1),
    computesBy_polynomial M input output f c d h, hf⟩

end GroupWL.MachinePrograms.Stacks
