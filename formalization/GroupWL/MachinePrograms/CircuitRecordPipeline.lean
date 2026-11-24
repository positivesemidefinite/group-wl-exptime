import GroupWL.MachinePrograms.CircuitRecordPipelineMetadata
import GroupWL.MachinePrograms.ReductionParameterPorts
import GroupWL.MachinePrograms.LayoutRecordCorrectness

/-! Circuit words produce all source equation, readout-dimension and rejecting-charge records. -/
namespace GroupWL.MachinePrograms.CircuitRecordPipeline.Frontend
open NatArrayLanguage AddressedCircuit CircuitDescription CircuitMetadataValues CircuitComparisons Refinement
open NatArrayLowering (bitNat)
open CircuitMetadataExpressions (Field)
set_option synthInstance.maxSize 65536
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

abbrev ParamReg := Metadata.Reg ⊕ ReductionParameters.Reg
abbrev ParamArr := Metadata.Arr ⊕ Empty
abbrev Reg := ParamReg ⊕ LayoutRecordPrograms.Reg
abbrev Arr := ParamArr ⊕ LayoutRecordPrograms.Arr
abbrev inputArray : Arr := .inl (.inl Metadata.inputArray)
abbrev coordinates : Reg := .inl (.inl Metadata.arity)
abbrev wire : Reg := .inl (.inr .wire)
abbrev frame : Reg := .inl (.inr .frame)
abbrev dimension : Reg := .inl (.inr .dimension)
abbrev horizontal : Reg := .inr (LayoutRecordPrograms.oldr (LayoutIncidencePrograms.hreg .count))
def coefficientArray (a : SourceCoefficients.Arr) : Arr := .inr (LayoutRecordPrograms.coefficientArray a)
abbrev dimensionArray : Arr := .inr LayoutRecordPrograms.dimensionArray
abbrev chargeArray : Arr := .inr LayoutRecordPrograms.chargeArray

abbrev ty : LayoutRecordPrograms.Reg := LayoutRecordPrograms.oldr (LayoutIncidencePrograms.nr .types)
abbrev co : LayoutRecordPrograms.Reg := LayoutRecordPrograms.oldr (LayoutIncidencePrograms.nr .comparisons)
abbrev wi : LayoutRecordPrograms.Reg := LayoutRecordPrograms.oldr (LayoutIncidencePrograms.nr .width)
abbrev le : LayoutRecordPrograms.Reg := LayoutRecordPrograms.oldr (LayoutIncidencePrograms.lr (LinkLabels.lr .length))
abbrev sp : LayoutRecordPrograms.Reg := LayoutRecordPrograms.cr (.inl .special)
abbrev tmp : LayoutRecordPrograms.Reg := LayoutRecordPrograms.oldr (LayoutIncidencePrograms.nr .one)

def recordScalars (i : LayoutRecordPrograms.Reg) : Ports.Scalar ParamReg ParamArr :=
  if i=ty then .scalar (.inl Metadata.typeCount)
  else if i=co then .scalar (.inl Metadata.comparisonCount)
  else if i=wi then .scalar (.inl Metadata.arity)
  else if i=le then .scalar (.inr .wire)
  else if i=sp then .scalar (.inl Metadata.comparisonCount)
  else .literal 0

abbrev dom : LayoutRecordPrograms.Arr := LayoutRecordPrograms.olda (.inl (.inl (.inl (.inl (.inl .domain)))))
abbrev so : LayoutRecordPrograms.Arr := LayoutRecordPrograms.olda (.inl (.inr (LinkNodes.wa .source)))
abbrev ta : LayoutRecordPrograms.Arr := LayoutRecordPrograms.olda (.inl (.inr (LinkNodes.wa .target)))
abbrev pe : LayoutRecordPrograms.Arr := LayoutRecordPrograms.olda (LayoutIncidencePrograms.qa .permutation)
abbrev sf : LayoutRecordPrograms.Arr := .inl (.inr (.inr (.inl (.inl .forms))))
abbrev tf : LayoutRecordPrograms.Arr := .inl (.inr (.inr (.inr (.inl .forms))))
abbrev dim : LayoutRecordPrograms.Arr := .inr (.inl (.inl (.inl .input)))

def recordArrays (i : LayoutRecordPrograms.Arr) : Option ParamArr :=
  if i=dom then some (.inl (Metadata.output .domain)) else
  if i=so then some (.inl (Metadata.output .source)) else
  if i=ta then some (.inl (Metadata.output .target)) else
  if i=pe then some (.inl (Metadata.output .permutation)) else
  if i=sf then some (.inl (Metadata.output .sourceForm)) else
  if i=tf then some (.inl (Metadata.output .targetForm)) else
  if i=dim then some (.inl (Metadata.output .dimension)) else none

def rejectingIndex : List (Atom LayoutRecordPrograms.Reg LayoutRecordPrograms.Arr) :=
  [.const tmp 3,.binary .sub sp sp tmp]

def records := NatArrayLanguage.Program.seq (atoms rejectingIndex) LayoutRecordPrograms.program
noncomputable def program (v : Version) : NatArrayLanguage.Program Reg Arr :=
  Ports.thenRun (ReductionParameters.after Metadata.program Metadata.arity v) recordScalars recordArrays records

private theorem recordLiteral (i : LayoutRecordPrograms.Reg) (k M : ℕ) (h : recordScalars i=.literal k) : k≤M := by
  unfold recordScalars at h
  split_ifs at h; cases h;omega

variable {T : Type} [FiniteCode T] {n : ℕ}
structure Output (v : Version) (p : ℕ) [Fact p.Prime] (C : Circuit T (n+3)) (S : Store Reg Arr) : Prop where
  arity_eq : S.scalar coordinates=n+3
  wire_eq : S.scalar wire=CircuitGroupReduction.wireLength n
  frame_eq : S.scalar frame=Parameters.frameWidth (n+3)
  dimension_eq : S.scalar dimension=CircuitGroupReduction.dimension v (n+3)
  records : LayoutRecordPrograms.Output (ComparisonMetadata.ofComparison p (comparisons C (ZMod p)))
    (CircuitGroupReduction.wireLength n) (FiniteCode.size (Comparison C)-3) S.right

private theorem records_runs (p : ℕ) [Fact p.Prime] (C : Circuit T (n+3)) (P : Store ParamReg ParamArr)
    (M : ℕ) (hp : Metadata.Output C P.left) (hw : P.right.scalar .wire=CircuitGroupReduction.wireLength n)
    (hs : (Ports.target recordScalars recordArrays P).Bounded M)
    (capacity : LayoutRecordPrograms.budget (ofCircuit C).table (CircuitGroupReduction.wireLength n)≤M) :
    ∃t≤2+(2000*M+500),∃U,Runs (storageBound LayoutRecordPrograms.Reg LayoutRecordPrograms.Arr M)
      records (Ports.target recordScalars recordArrays P) t U ∧ U.Bounded M ∧
      LayoutRecordPrograms.Output (ComparisonMetadata.ofComparison p (comparisons C (ZMod p)))
        (CircuitGroupReduction.wireLength n) (FiniteCode.size (Comparison C)-3) U := by
  let L := CircuitGroupReduction.wireLength n
  let D := (ofCircuit C).table
  have hd : D=ComparisonMetadata.ofComparison p (comparisons C (ZMod p)) := table_correct C p
  have hE : D.comparisons=FiniteCode.size (Comparison C) := congrArg ComparisonMetadata.Table.comparisons hd
  have valid : LayoutIncidencePrograms.Valid D := hd ▸ LayoutIncidencePrograms.comparison_valid p _
  obtain ⟨room,copies,size,links,blocks⟩ := LayoutRecordPrograms.budget_room D L valid
  have room' : LayoutIncidencePrograms.Room D L M := by
    rcases room with ⟨a,b,c,d,e,f,g⟩
    exact ⟨a.trans capacity,b.trans capacity,c.trans capacity,d.trans capacity,e.trans capacity,f.trans capacity,g.trans capacity⟩
  let X := Ports.target recordScalars recordArrays P
  have special : X.scalar sp=D.comparisons := hp.comparisons
  have hsize : D.comparisons≤M := special ▸ hs.1 sp
  have ok : ValidAtoms M rejectingIndex X := by
    have four := room'.four
    simp [rejectingIndex,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,Store.setScalar,BinaryOp.eval,special]
    omega
  obtain ⟨start,hU⟩ := atoms_runs hs rejectingIndex ok
  let U := applyAtoms rejectingIndex X
  have inp : LayoutIncidencePrograms.Input D L U.left.left :=
    ⟨⟨hp.types,hp.comparisons,hp.coordinates,hw,hp.arrays .domain⟩,hp.arrays .source,hp.arrays .target,hp.arrays .permutation⟩
  have qs : U.right.right.left.scalar .special = FiniteCode.size (Comparison C)-3 := by
    change ((X.setScalar tmp 3).scalar sp - (X.setScalar tmp 3).scalar tmp) = _
    change X.scalar sp - 3 = _
    rw [special,hE]
  have sl : D.sourceForm.length=2*D.comparisons := by rw [hd]; change (ComparisonMetadata.sourceForm p (comparisons C (ZMod p))).length = 2*FiniteCode.size (Comparison C); rw [ComparisonMetadata.sourceForm_length];omega
  have tl : D.targetForm.length=2*D.comparisons := by rw [hd]; change (ComparisonMetadata.targetForm p (comparisons C (ZMod p))).length = 2*FiniteCode.size (Comparison C); rw [ComparisonMetadata.targetForm_length];omega
  obtain ⟨t,ht,V,run,b,out⟩ := LayoutRecordPrograms.program_runs D L (FiniteCode.size (Comparison C)-3) M U hU inp
    (hp.arrays .sourceForm) (hp.arrays .targetForm) (hp.arrays .dimension) qs (by rw [hE];omega)
    valid room' (by simp [L,CircuitGroupReduction.wireLength]) (copies.trans capacity) (size.trans capacity)
    (links.trans capacity) (blocks.trans capacity) (by change 0<n+3;omega) sl tl
  exact ⟨2+t,Nat.add_le_add_left ht _,V,start.seq run,b,hd ▸ out⟩

noncomputable def time (n s B M : ℕ) := Metadata.time n s B + 22 + (Fintype.card LayoutRecordPrograms.Reg+Fintype.card LayoutRecordPrograms.Arr+(2+(2000*M+500)))

theorem program_runs (v : Version) (p : ℕ) [Fact p.Prime] (C : Circuit T (n+3))
    (S : Store Reg Arr) (B M : ℕ) (hs : S.Bounded B) (hBM : B≤M)
    (room : 6≤B) (hparse : 3*(circuitWord C).length+5≤B)
    (sizes : ∀f,fieldSize (ofCircuit C) f≤B) (budget : ∀f,(B+2)^(2*((CircuitMetadataExpressions.entry f).expression CircuitMetadataExpressions.sizeRegister).cost)≤M)
    (parameters : 146*(n+3+1)^2≤M)
    (capacity : LayoutRecordPrograms.budget (ofCircuit C).table (CircuitGroupReduction.wireLength n)≤M)
    (input : S.array inputArray=(circuitWord C).map bitNat) :
    ∃t≤time (circuitWord C).length (FiniteCode.size T) B M,∃U,
      Runs (storageBound Reg Arr M) (program v) S t U ∧ U.Bounded M ∧ Output v p C U := by
  have bs := Metadata.bounded_mono hs hBM
  obtain ⟨t,ht,P,first,bP,outP⟩ := Metadata.program_runs C S.left.left B M hs.left.left hBM room hparse sizes budget input
  obtain ⟨u,hu,Q,param,bQ,hwire,hframe,hk⟩ := ReductionParameters.after_runs Metadata.program Metadata.arity v S.left.right bs.left.left bP bs.left.right first outP.coordinates parameters
  rw [Store.join_left_right] at param
  have bound := bP.join bQ
  have store := Ports.code_runs recordScalars recordArrays (P.join Q) S.right M (bound.join bs.right) (fun i k h=>recordLiteral i k M h)
  obtain ⟨w,hw,W,last,bW,outW⟩ := records_runs p C (P.join Q) M outP hwire store.2 capacity
  have run := Ports.thenRun_runs (ReductionParameters.after Metadata.program Metadata.arity v) recordScalars recordArrays records
    S.left (P.join Q) S.right W M u w bs.left bound bs.right (fun i k h=>recordLiteral i k M h) param last
  rw [Store.join_left_right] at run
  exact ⟨_,Nat.add_le_add (hu.trans (Nat.add_le_add_right ht _)) (Nat.add_le_add_left hw _),_,run,bound.join bW,outP.coordinates,hwire,hframe,hk,outW⟩
end GroupWL.MachinePrograms.CircuitRecordPipeline.Frontend
