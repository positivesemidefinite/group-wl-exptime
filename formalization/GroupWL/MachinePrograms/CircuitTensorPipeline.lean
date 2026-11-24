import GroupWL.MachinePrograms.CircuitTensorPipelineRecords
import GroupWL.MachinePrograms.CircuitRecordPipeline
import GroupWL.MachinePrograms.IncidencePipelineMiddle
import GroupWL.MachinePrograms.ChargedBounds

/-! The circuit-to-tensor array program. The input parser is the sole reader of
the circuit word. The middle computes the charts, and the last stage materializes both tensors. -/
namespace GroupWL.MachinePrograms.CircuitTensorPipeline
open NatArrayLanguage CircuitComparisons CircuitGroupReduction AddressedCircuit ConstructiveIncidence
open CircuitRecordPipeline
open IncidencePipeline
set_option synthInstance.maxSize 65536
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option quotPrecheck false

def front : FrontPorts Frontend.Reg Frontend.Arr :=
  ⟨Frontend.horizontal,Frontend.frame,Frontend.dimension,Frontend.coefficientArray,Frontend.dimensionArray,Frontend.chargeArray⟩

def entrance : HeaderPorts Middle.Reg Middle.Arr where
  reg := Middle.headerReg
  arr := Middle.headerField
  asReg := Middle.asHeaderReg
  asArr := Middle.asHeaderField
  reg_eq _ := rfl
  arr_eq _ := rfl

abbrev SourceReg := Frontend.Reg ⊕ Middle.Reg
abbrev SourceArr := Frontend.Arr ⊕ Middle.Arr
instance : DecidableEq SourceReg := @instDecidableEqSum _ _ (inferInstance : DecidableEq Frontend.Reg) (inferInstance : DecidableEq Middle.Reg)
instance : DecidableEq SourceArr := @instDecidableEqSum _ _ (inferInstance : DecidableEq Frontend.Arr) (inferInstance : DecidableEq Middle.Arr)
noncomputable instance : Fintype SourceReg := inferInstanceAs (Fintype (Frontend.Reg ⊕ Middle.Reg))
noncomputable instance : Fintype SourceArr := inferInstanceAs (Fintype (Frontend.Arr ⊕ Middle.Arr))
abbrev Source := Store SourceReg SourceArr
noncomputable def source (p : ℕ) (v : Refinement.Version) :=
  Ports.thenRun (Frontend.program v) (entrance.scalar front) (entrance.array front) (Middle.program p)

def ends : FinalPorts SourceReg SourceArr where
  kernelReg r := .inr (Middle.kernelReg r)
  kernelArr a := .inr (Middle.kernelArr a)
  inputDimension := .inr Middle.xPort
  outputDimension := .inr Middle.zPort
  frames := .inl Frontend.frame
  framePairs := .inr Middle.pairPort
  wlDimension := .inl Frontend.dimension
  charge := .inl Frontend.chargeArray

abbrev Reg := SourceReg ⊕ ChargedAssembly.Reg
abbrev Arr := SourceArr ⊕ ChargedAssembly.Arr
instance : DecidableEq Reg := @instDecidableEqSum _ _ (inferInstance : DecidableEq SourceReg) (inferInstance : DecidableEq ChargedAssembly.Reg)
instance : DecidableEq Arr := @instDecidableEqSum _ _ (inferInstance : DecidableEq SourceArr) (inferInstance : DecidableEq ChargedAssembly.Arr)
noncomputable instance : Fintype Reg := inferInstanceAs (Fintype (SourceReg ⊕ ChargedAssembly.Reg))
noncomputable instance : Fintype Arr := inferInstanceAs (Fintype (SourceArr ⊕ ChargedAssembly.Arr))
abbrev State := Store Reg Arr
def input : Arr := .inl (.inl Frontend.inputArray)
noncomputable def program (p : ℕ) (v : Refinement.Version) : NatArrayLanguage.Program Reg Arr :=
  ends.finish p (source p v)
def output := fields SourceReg SourceArr

variable {T : Type} [FiniteCode T] {n : ℕ} (C : Circuit T (n+3)) (p : ℕ) [Fact p.Prime]
local notation "D₀" => comparisons C (ZMod p)
local notation "L₀" => wireLength n
local notation "q₀" => Parameters.frameWidth (n+3)
local notation "β₀" => ((D₀).sourceShift (rejectingConstant C (ZMod p)) : (D₀).Block L₀ → ZMod p)
local notation "A₀" => ComputableSource.affineSystem D₀ (L:=L₀)
local notation "R₀" => ConstructiveSourceTensor.radicalCoordinates D₀ L₀
local notation "X₀" => FiniteCode.size (InputIndex A₀ R₀ q₀)
local notation "Z₀" => FiniteCode.size (OutputIndex A₀ R₀ q₀)
local notation "P₀" => FiniteCode.size (IncidenceTensor.Pair q₀)
local notation "I₀" => FiniteCode.size ((D₀).Block L₀)
local instance : Fintype T := FiniteCode.fintype T
local instance : Fintype ((D₀).Block L₀) := FiniteCode.fintype _
local instance : Fintype ((D₀).Readout L₀) := FiniteCode.fintype _
local instance : DecidableEq ((D₀).Block L₀) := (FiniteCode.equiv (α:=(D₀).Block L₀)).decidableEq
local instance : DecidableEq ((D₀).Readout L₀) := (FiniteCode.equiv (α:=(D₀).Readout L₀)).decidableEq

theorem front_records (v : Refinement.Version) (S : Store Frontend.Reg Frontend.Arr)
    (out : Frontend.Output v p C S) : CircuitRecords front C p v S :=
  circuitRecords_of_layout front C p v S S.right out.records (fun _=>rfl) rfl rfl rfl out.frame_eq out.dimension_eq

theorem source_ready (v : Refinement.Version) (S : Source) (hq : 0<q₀)
    (frontDone : Frontend.Output v p C S.left) (middleDone : Middle.Output p D₀ L₀ q₀ hq S.right) :
    ends.Ready p A₀ R₀ q₀ hq β₀ (dimension v (n+3)) S := by
  have written := front_records C p v S.left frontDone
  exact ⟨middleDone.operator.gram,middleDone.operator.xdim,middleDone.operator.zdim,written.frames,
    (congrArg List.length middleDone.pairs).trans List.length_ofFn,written.dim,written.charge⟩

def time (frontTime middleTime chargeTime : ℕ) :=
  (frontTime+(Fintype.card Middle.Reg+Fintype.card Middle.Arr+middleTime))+
  (Fintype.card ChargedAssembly.Reg+Fintype.card ChargedAssembly.Arr+chargeTime)

theorem compose_runs (v : Refinement.Version) (M B frontTime middleTime : ℕ) (S : State)
    (bounded : S.Bounded M) (hq : 0<q₀)
    (frontRun : ∃t≤frontTime,∃U,Runs (storageBound Frontend.Reg Frontend.Arr M) (Frontend.program v)
      S.left.left t U ∧ U.Bounded M ∧ Frontend.Output v p C U)
    (middleRun : ∀W,W.Bounded M → IncidencePipeline.Records.Input p D₀ L₀ q₀ (Middle.readHeader W) →
      ∃t≤middleTime,∃U,Runs (storageBound Middle.Reg Middle.Arr M) (Middle.program p) W t U ∧
        U.Bounded M ∧ Middle.Output p D₀ L₀ q₀ hq U)
    (bh : 2+X₀+Z₀+q₀*2+P₀*2+p+dimension v (n+3)+I₀+X₀*X₀+X₀*X₀*Z₀≤B)
    (expr : (B+2)^(2*(ChargedWriter.term.expression ChargedWriter.sizeReg).cost)≤M) (bM : B≤M)
    (size : let x := X₀+(ConstructiveTensor.operatorCoordinates A₀ R₀ q₀ hq).dimension
            x+x*x+x*x*Z₀≤M) :
    let x := X₀+(ConstructiveTensor.operatorCoordinates A₀ R₀ q₀ hq).dimension
    ∃t≤time frontTime middleTime (ChargedAssembly.cost (X₀*X₀*Z₀) (x*x*Z₀)),∃U,
      Runs (storageBound Reg Arr M) (program p v) S t U ∧ U.Bounded M ∧
        CircuitWriterReduction.Describes p (output.read U) (ComputableCircuitReduction.baseDescription p C)
          (ComputableCircuitReduction.mateDescription p C) (dimension v (n+3)) := by
  obtain ⟨t,ht,T,run,mem,finished,mid⟩ := Ports.thenRun_post (Frontend.program v) (entrance.scalar front)
    (entrance.array front) (Middle.program p) S.left M frontTime middleTime bounded.left (entrance.small front M)
    (Frontend.Output v p C) (fun _ W => Middle.Output p D₀ L₀ q₀ hq W) frontRun (by
      intro U done _ bW
      exact middleRun _ bW (entrance.incoming front p D₀ L₀ q₀ U (front_records C p v U done).toWritten))
  obtain ⟨u,hu,W,finished,bW,hout⟩ := ends.finish_runs p A₀ R₀ q₀ (source p v) hq
    (frameWidth_ge_two (n+3)) β₀ (dimension v (n+3)) S B M
    (frontTime+(Fintype.card Middle.Reg+Fintype.card Middle.Arr+middleTime)) bounded bh expr bM size
    ⟨t,ht,T,run,mem,source_ready C p v T hq finished mid⟩
  exact ⟨u,hu,W,finished,bW,describes W _ _ _ hout⟩

end GroupWL.MachinePrograms.CircuitTensorPipeline
