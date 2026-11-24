import GroupWL.MachinePrograms.ChargedAssembly
import GroupWL.MachinePrograms.IncidencePipelineRecords

/-! Connect the computed Gaussian kernel, circuit charge word and dimensions to
the two dense tensor assemblers. Both coefficient arrays remain in the resulting store. -/
namespace GroupWL.MachinePrograms.CircuitTensorPipeline
open NatArrayLanguage ConstructiveIncidence ConstructiveCoordinates IncidenceTensor
set_option synthInstance.maxSize 65536
set_option maxRecDepth 16384

structure FinalPorts (R A : Type) where
  kernelReg : KernelProgram.Reg → R
  kernelArr : KernelProgram.Arr → A
  inputDimension : R
  outputDimension : R
  frames : R
  framePairs : A
  wlDimension : R
  charge : A

namespace FinalPorts
variable {R A : Type} (f : FinalPorts R A)
def kernel (S : Store R A) : KernelProgram.State :=
  ⟨S.scalar ∘ f.kernelReg, S.array ∘ f.kernelArr⟩

def writerScalar (p : ℕ) : ChargedWriter.Registers → Ports.Scalar R A
  | .inl (.inr .inputDim) => .scalar f.inputDimension
  | .inl (.inr .outputDim) => .scalar f.outputDimension
  | .inl (.inr .inputStride) => .scalar f.frames
  | .inl (.inr .outputStride) => .length f.framePairs
  | .inl (.inr .modulus) => .literal p
  | .inl (.inr .dimension) => .scalar f.wlDimension
  | _ => .literal 0

def scalar (p : ℕ) : ChargedAssembly.Reg → Ports.Scalar R A
  | .inl (.inl r) => .scalar (f.kernelReg r)
  | .inl (.inr r) => f.writerScalar p r
  | .inr _ => .literal 0

def array : ChargedAssembly.Arr → Option A
  | .inl (.inl a) => some (f.kernelArr a)
  | .inl (.inr (.inl ())) => some f.charge
  | _ => none

variable [DecidableEq R] [DecidableEq A] [Fintype R] [Fintype A]
noncomputable def finish (p : ℕ) (before : NatArrayLanguage.Program R A) :=
  Ports.thenRun before (f.scalar p) f.array ChargedAssembly.program
omit [DecidableEq R] [DecidableEq A] [Fintype R] [Fintype A] in
private theorem small (p M : ℕ) (hp : p≤M) (r : ChargedAssembly.Reg) (i : ℕ)
    (h : f.scalar p r = .literal i) : i≤M := by
  rcases r with (r|r)|r
  · simp [scalar] at h
  · rcases r with (r|r)|r
    · simp [scalar,writerScalar] at h; omega
    · cases r <;> simp [scalar,writerScalar] at h <;> omega
    · simp [scalar,writerScalar] at h; omega
  · simp [scalar] at h; omega

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [FiniteCode I] [FiniteCode J] (p : ℕ) [Fact p.Prime]
variable {V : J → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module (ZMod p) (V j)]
variable (sys : AffineSystem (ZMod p) I J V)
  (coordinates : ∀ j, Coordinates (ZMod p) (ReadoutRadical sys j)) (q : ℕ)
local notation "X" => FiniteCode.size (InputIndex sys coordinates q)
local notation "Z" => FiniteCode.size (OutputIndex sys coordinates q)
local notation "H" => ConstructiveTensor.operatorCoordinates sys coordinates q
local notation "Y" => ConstructiveTensor.obstructionMap sys coordinates q
local notation "C" => FiniteCode.size (Pair q)

structure Ready (hq : 0<q) (β : I → ZMod p) (k : ℕ) (T : Store R A) : Prop where
  gram : KernelProgram.Represents p (X*Z) 0 (wedgeWord p sys coordinates q hq)
    (KernelProgramCorrectness.encode (GeneratedCoordinateEntries.operatorChart
      (chosenCoordinates sys coordinates q hq) (Y hq))) (f.kernel T)
  xdim : T.scalar f.inputDimension=X
  zdim : T.scalar f.outputDimension=Z
  frames : T.scalar f.frames=q
  framePairs : (T.array f.framePairs).length=C
  dimension : T.scalar f.wlDimension=k
  charge : T.array f.charge=ChargedWriter.chargeWord p β

theorem finish_runs (before : NatArrayLanguage.Program R A) (hq : 0<q) (h₂ : 2≤q) (β : I→ZMod p) (k : ℕ)
    (S : Store (R⊕ChargedAssembly.Reg) (A⊕ChargedAssembly.Arr)) (B M prevTime : ℕ)
    (hS : S.Bounded M) (hb : 2+X+Z+q*2+C*2+p+k+FiniteCode.size I+X*X+X*X*Z≤B)
    (expr : (B+2)^(2*(ChargedWriter.term.expression ChargedWriter.sizeReg).cost)≤M) (bM : B≤M)
    (size : (X+(H hq).dimension)+(X+(H hq).dimension)*(X+(H hq).dimension)+
      (X+(H hq).dimension)*(X+(H hq).dimension)*Z≤M)
    (prev : ∃t≤prevTime,∃T,Runs (storageBound R A M) before S.left t T ∧ T.Bounded M ∧
      f.Ready p sys coordinates q hq β k T) :
    ∃t≤prevTime+(Fintype.card ChargedAssembly.Reg+Fintype.card ChargedAssembly.Arr+
      ChargedAssembly.cost (X*X*Z) ((X+(H hq).dimension)*(X+(H hq).dimension)*Z)),∃T,
      Runs (storageBound (R⊕ChargedAssembly.Reg) (A⊕ChargedAssembly.Arr) M) (f.finish p before) S t T ∧
        T.Bounded M ∧ ChargedAssembly.Output T.right
          (ConstructiveTensor.description q p sys coordinates hq AlternatingBilinearMap.zero)
          (ConstructiveTensor.description q p sys coordinates hq (epsilonCharge sys q h₂ β)) k := by
  let P := f.Ready p sys coordinates q hq β k
  let Q := fun (_ : Store R A) (T : ChargedAssembly.State) => ChargedAssembly.Output T
    (ConstructiveTensor.description q p sys coordinates hq AlternatingBilinearMap.zero)
    (ConstructiveTensor.description q p sys coordinates hq (epsilonCharge sys q h₂ β)) k
  obtain ⟨t,ht,T,run,mem,_,out⟩ := Ports.thenRun_post before (f.scalar p) f.array ChargedAssembly.program S M
    prevTime (ChargedAssembly.cost (X*X*Z) ((X+(H hq).dimension)*(X+(H hq).dimension)*Z))
    hS (f.small p M (by omega)) P Q prev (by
      intro U ready _ bounded
      let W := Ports.target (f.scalar p) f.array U
      have localInput : ChargedAssembly.Input W.left.right X Z q C p k (ChargedWriter.chargeWord p β) :=
        ⟨ready.xdim,ready.zdim,ready.frames,ready.framePairs,rfl,ready.dimension,ready.charge⟩
      obtain ⟨t,ht,T,run,bT,out⟩ := ChargedAssembly.program_runs p sys coordinates q hq h₂ β k W.left.left
        W.left.right W.right ready.gram localInput B M hb expr bM bounded.left.left bounded.left.right bounded.right size
      exact ⟨t,ht,T,by simpa only [Store.join_left_right] using run,bT,out⟩)
  exact ⟨t,ht,T,run,mem,out⟩

end FinalPorts
end GroupWL.MachinePrograms.CircuitTensorPipeline
