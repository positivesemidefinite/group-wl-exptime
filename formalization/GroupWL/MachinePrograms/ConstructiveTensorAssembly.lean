import GroupWL.MachinePrograms.EvaluationAssemblyCorrectness

/-! Specialization of the concrete assembly program to the actual incidence construction. -/
namespace GroupWL.MachinePrograms.ConstructiveTensorAssembly
open IncidenceTensor IncidenceGroup ConstructiveCoordinates EvaluationAssembly
variable (p : ℕ) [Fact p.Prime]
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [FiniteCode I] [FiniteCode J]
variable {V : J → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module (ZMod p) (V j)]
variable (A : AffineSystem (ZMod p) I J V)
  (R : ∀ j, Coordinates (ZMod p) (ReadoutRadical A j)) (q : ℕ) (hq : 0<q)
local notation "D" => Coordinates.pi (F:=ZMod p) (ConstructiveIncidence.InputIndex A R q)
local notation "E" => Coordinates.pi (F:=ZMod p) (ConstructiveIncidence.OutputIndex A R q)
local notation "Y" => MatrixEvaluationGroup.operatorSpace (LinearMap.range (ConstructiveTensor.obstructionMap A R q hq))
local notation "H" => ConstructiveTensor.operatorCoordinates A R q hq
variable (ε : AlternatingBilinearMap (ZMod p) (PaddedInput A q) (PaddedOutput A q))
local notation "εc" => twistCoordinates A q (ConstructiveIncidence.inputEquiv A R q)
    (ConstructiveIncidence.outputEquiv A R q) ε

theorem description_eq : EvaluationAssembly.description p D E Y H εc =
    ConstructiveTensor.description q p A R hq ε := rfl

def operatorEntries : List ℕ := EvaluationAssembly.operatorEntries p D E Y H
def twistEntries : List ℕ := EvaluationAssembly.twistEntries p D E εc

theorem program_runs (S : EvaluationAssembly.State) (M : ℕ) (bounded : S.Bounded M)
    (ha : S.scalar .xdim=(D).dimension) (hb : S.scalar .ydim=(H).dimension)
    (hm : S.scalar .zdim=(E).dimension) (hp : S.scalar .modulus=p)
    (hH : S.array .operators=operatorEntries p A R q hq)
    (hE : S.array .twist=twistEntries p A R q ε)
    (sizeBound : ((D).dimension+(H).dimension)+((D).dimension+(H).dimension)*((D).dimension+(H).dimension)+
      ((D).dimension+(H).dimension)*((D).dimension+(H).dimension)*(E).dimension≤M) :
    ∃t≤19*(((D).dimension+(H).dimension)*((D).dimension+(H).dimension)*(E).dimension)+9,
      ∃T,NatArrayLanguage.Runs (NatArrayLanguage.storageBound Reg Arr M) EvaluationAssembly.program S t T ∧
        T.Bounded M ∧ T.scalar .inputdim=(ConstructiveTensor.description q p A R hq ε).inputDimension ∧
        T.scalar .zdim=(ConstructiveTensor.description q p A R hq ε).outputDimension ∧
        T.array .output=TensorSerialization.coefficientList ((ConstructiveTensor.description q p A R hq ε).coefficient p) :=
  EvaluationAssembly.program_tensor_runs p D E Y H εc S M bounded ha hb hm hp hH hE sizeBound

theorem serialized_runs (S : EvaluationAssembly.State) (M : ℕ) (bounded : S.Bounded M)
    (ha : S.scalar .xdim=(D).dimension) (hb : S.scalar .ydim=(H).dimension)
    (hm : S.scalar .zdim=(E).dimension) (hp : S.scalar .modulus=p)
    (hH : S.array .operators=operatorEntries p A R q hq)
    (hE : S.array .twist=twistEntries p A R q ε)
    (sizeBound : ((D).dimension+(H).dimension)+((D).dimension+(H).dimension)*((D).dimension+(H).dimension)+
      ((D).dimension+(H).dimension)*((D).dimension+(H).dimension)*(E).dimension≤M) :
    ∃t≤10000*(NatArrayLanguage.storageBound Reg Arr M+1)^4*
        (19*(((D).dimension+(H).dimension)*((D).dimension+(H).dimension)*(E).dimension)+9)+
        3*((ConstructiveTensor.description q p A R hq ε).denseWord p).length+5,
      ∃U,Structured.Runs EvaluationAssembly.serializedProgram (NatArrayLowering.encodeStore S) t U ∧
        (U (NatArrayLowering.scratchSlot 0)).reverse=(ConstructiveTensor.description q p A R hq ε).denseWord p :=
  EvaluationAssembly.serializedProgram_runs p D E Y H εc S M bounded ha hb hm hp hH hE sizeBound

end GroupWL.MachinePrograms.ConstructiveTensorAssembly
