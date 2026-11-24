import GroupWL.MachinePrograms.IncidencePipelineDescriptors
import GroupWL.MachinePrograms.ChargedWedgeStage
import GroupWL.MachinePrograms.IncidencePipelineFrames

/-! Executable middle of the reduction, from the six layout records to the exact operator kernel. -/
namespace GroupWL.MachinePrograms.IncidencePipeline.Middle
open NatArrayLanguage SourceLayout SourceTableEncoding ConstructiveIncidence
set_option synthInstance.maxSize 65536
set_option maxRecDepth 16384
abbrev Reg := Descriptors.Reg⊕ChargedWedgeStage.Reg
abbrev Arr := Descriptors.Arr⊕ChargedWedgeStage.Arr
abbrev State := Store Reg Arr

abbrev headerReg (r : Records.Header) : Reg := .inl (.inl (.inl (Descriptors.headerReg₀ r)))
abbrev headerField (a : Records.Field) : Arr := .inl (.inl (.inl (Descriptors.headerField₀ a)))
abbrev readHeader (S : State) := S.left.left.left.left.left.left
def asHeaderReg : Reg → Option Records.Header
  | .inl (.inl (.inl (.inl (.inl (.inl r))))) => some r
  | _ => none
def asHeaderField : Arr → Option Records.Field
  | .inl (.inl (.inl (.inl (.inl (.inl a))))) => some a
  | _ => none
abbrev pairPort : Arr := .inl (.inl (.inr Indices.pairPort))
abbrev xPort : Reg := .inr (.inl (.inl .xdim))
abbrev zPort : Reg := .inr (.inl (.inl .zdim))
abbrev kernelReg (r : KernelProgram.Reg) : Reg := .inr (.inr (.inr r))
abbrev kernelArr (a : KernelProgram.Arr) : Arr := .inr (.inr (.inr a))
abbrev gram (S : State) := S.right.right.right

def sourceR (p : ℕ) (r : ChargedWedgeStage.Reg) : Ports.Scalar Descriptors.Reg Descriptors.Arr :=
  if r=.inl (.inl .modulus) then .literal p else if r=.inl (.inl .chosenWidth) then
    .scalar (.inl (.inl Descriptors.width₀)) else .scalar (.inl (.inl Descriptors.ambient₀))
def sourceA : ChargedWedgeStage.Arr → Option Descriptors.Arr
  | .inl (.inl .u0) => some (.inr DescriptorPipeline.u0Port)
  | .inl (.inl .v0) => some (.inr DescriptorPipeline.v0Port)
  | .inl (.inl .u1) => some (.inr DescriptorPipeline.u1Port)
  | .inl (.inl .v1) => some (.inr DescriptorPipeline.v1Port)
  | .inl (.inl .second) => some (.inr DescriptorPipeline.secondPort)
  | .inl (.inl .forms) => some (.inr DescriptorPipeline.formPort)
  | .inl (.inl .lift) => some (.inl (.inl Descriptors.lift₀))
  | _ => none

noncomputable def program (p : ℕ) := Ports.thenRun (Descriptors.program p) (sourceR p) sourceA (ChargedWedgeStage.program p)

variable {X E : Type} [FiniteCode X] [FiniteCode E] {r : ℕ} (p : ℕ) [Fact p.Prime]
  (C : ComparisonData (ZMod p) X E r) (L q : ℕ)
local instance : Fintype X := FiniteCode.fintype X
local instance : Fintype E := FiniteCode.fintype E
local instance : Fintype (C.Block L) := FiniteCode.fintype _
local instance : Fintype (C.Readout L) := FiniteCode.fintype _
local instance : DecidableEq (C.Block L) := (FiniteCode.equiv (α:=C.Block L)).decidableEq
local instance : DecidableEq (C.Readout L) := (FiniteCode.equiv (α:=C.Readout L)).decidableEq
local notation "A₀" => ComputableSource.affineSystem C (L:=L)
local notation "R₀" => ConstructiveSourceTensor.radicalCoordinates C L
local notation "nv" => blockCount p C L
local notation "ni" => FiniteCode.size (OldInputIndex A₀ R₀ q)
local notation "nf" => FiniteCode.size (FormIndex A₀ R₀ q)
local notation "nx" => FiniteCode.size (InputIndex A₀ R₀ q)
local notation "nz" => FiniteCode.size (OutputIndex A₀ R₀ q)

def time (hq : 0<q) := Descriptors.time p C L q+(Fintype.card ChargedWedgeStage.Reg+Fintype.card ChargedWedgeStage.Arr+
  ChargedWedgeStage.time p ni nf (chosenCoordinates A₀ R₀ q hq).dimension nx nz)

structure Output (hq : 0<q) (T : State) : Prop where
  records : Records.Counts p C L q (readHeader T)
  pairs : T.array pairPort=FramePairEncoding.word q
  operator : ChargedWedgeStage.Output p A₀ R₀ q hq T.right

structure Room (hq : 0<q) (M : ℕ) : Prop where
  coordinates : IncidencePipeline.Room p C L q M
  pairs : q*q≤M
  descriptors : DescriptorPipeline.Room p A₀ R₀ q (nv+2) M
  wedge : ChargedWedgeStage.Room p A₀ R₀ q hq M

theorem program_runs (hdim : ∀t,C.dim t≤2) (hq : 0<q) (M : ℕ) (room : Room p C L q hq M)
    (S : State) (bounded : S.Bounded M) (h : Records.Input p C L q (readHeader S)) :
    ∃t≤time p C L q hq,∃T,Runs (storageBound Reg Arr M) (program p) S t T ∧ T.Bounded M ∧
      T.array (headerField .charge)=S.array (headerField .charge) ∧ Output p C L q hq T := by
  let Out := fun W : Descriptors.State => Descriptors.IndexedOutput p C L q hq W.left ∧
    DescriptorPipeline.CanonicalOutput p A₀ R₀ q W.right
  have desc := Descriptors.program_runs p C L q hdim hq M room.coordinates room.pairs room.descriptors S.left bounded.left h
  obtain ⟨t,ht,T,run,hT,old,op⟩ := Ports.thenRun_post (Descriptors.program p) (sourceR p) sourceA
    (ChargedWedgeStage.program p) S M (Descriptors.time p C L q) _ bounded (by
      intro i k he
      unfold sourceR at he
      split at he
      · cases he
        have := room.coordinates.recordField
        omega
      · split at he <;> contradiction)
    Out (fun _ W => ChargedWedgeStage.Output p A₀ R₀ q hq W) desc (by
      intro U hU _ B
      exact ChargedWedgeStage.program_runs p A₀ R₀ q hq M _ B ⟨hU.1.coordinates.ambient,hU.1.coordinates.width,rfl,
        hU.2.u0,hU.2.v0,hU.2.u1,hU.2.v1,hU.2.second,hU.2.matrix,hU.1.coordinates.lift⟩ room.wedge)
  refine ⟨t,ht,T,run,hT,?_,old.1.records.metadata,old.1.pairs,op⟩
  apply run.array_eq_of_not_mem
  apply Ports.array_frame
  apply Ports.array_frame
  apply Ports.array_frame
  apply Ports.array_frame
  apply Ports.array_frame
  apply Ports.array_frame
  decide

end GroupWL.MachinePrograms.IncidencePipeline.Middle
