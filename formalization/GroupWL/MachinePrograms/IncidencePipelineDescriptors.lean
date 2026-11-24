import GroupWL.MachinePrograms.IncidencePipelineIndices
import GroupWL.MachinePrograms.DescriptorPipeline

/-! One bounded machine from the numerical layout records to the ordinary forms, chosen lift,
and all five obstruction descriptors. -/
namespace GroupWL.MachinePrograms.IncidencePipeline.Descriptors
open NatArrayLanguage SourceLayout SourceTableEncoding ConstructiveIncidence
set_option synthInstance.maxSize 65536
set_option maxRecDepth 16384

abbrev headerReg₀ (r : Records.Header) : PrefixReg := .inl (.inl (.inl r))
abbrev headerField₀ (a : Records.Field) : PrefixArr := .inl (.inl (.inl a))
abbrev ambient₀ : PrefixReg := .inr (.inr (.inr (.inr (KernelProgram.wr .ambient))))
abbrev width₀ : PrefixReg := .inr (.inr (.inr (.inr (KernelProgram.wr .width))))
abbrev lift₀ : PrefixArr := .inr (.inr (.inr (.inr (KernelProgram.wa .lift))))
abbrev radicals₀ : PrefixArr := .inr (.inl (.inr .output))
abbrev dimensions₀ : PrefixArr := .inr (.inr (.inl (.inl .output)))
abbrev offsets₀ : PrefixArr := .inr (.inr (.inl (.inr (.inr .ranks))))

def idxReg (_ : Indices.Reg) : Ports.Scalar PrefixReg PrefixArr := .scalar (headerReg₀ .frames)
def idxArr : Indices.Arr → Option PrefixArr
  | .inl (.inl .input) => some (.inl Records.scopePort)
  | _ => none

abbrev IReg := PrefixReg⊕Indices.Reg
abbrev IArr := PrefixArr⊕Indices.Arr
abbrev IState := Store IReg IArr
noncomputable def indexed (p : ℕ) := Ports.thenRun (prefixProgram p) idxReg idxArr Indices.program

def idxTime (p b r n q : ℕ) := prefixTime p b r n +
  (Fintype.card Indices.Reg+Fintype.card Indices.Arr+Indices.time (b*r) q)

def sourceR : DescriptorPipeline.Reg → IReg
  | .inl (.inl (.inl .blocks)) => .inl (headerReg₀ .blocks)
  | .inl (.inl (.inl .readouts)) => .inl (headerReg₀ .readouts)
  | .inl (.inl (.inl .oldInput)) => .inl ambient₀
  | .inl (.inl (.inl .two)) => .inl (headerReg₀ .two)
  | _ => .inl (headerReg₀ .frames)

def sourceA : DescriptorPipeline.Arr → Option IArr
  | .inl (.inl (.inl .dimensions)) => some (.inl dimensions₀)
  | .inl (.inl (.inl .offsets)) => some (.inl offsets₀)
  | .inl (.inl (.inl .radicals)) => some (.inl radicals₀)
  | .inl (.inl (.inl .pairs)) => some (.inr Indices.pairPort)
  | .inl (.inl (.inl .incidences)) => some (.inr Indices.edgePort)
  | _ => none

def capStep : Atom DescriptorPipeline.Reg DescriptorPipeline.Arr :=
  .binary .add (DescriptorPipeline.inputReg .cap) (DescriptorPipeline.inputReg .blocks) (DescriptorPipeline.inputReg .two)

abbrev Reg := IReg⊕DescriptorPipeline.Reg
abbrev Arr := IArr⊕DescriptorPipeline.Arr
abbrev State := Store Reg Arr
noncomputable def program (p : ℕ) := Ports.thenRun (indexed p) (fun i => .scalar (sourceR i)) sourceA
  (.seq (.atom capStep) DescriptorPipeline.program)

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
local notation "rs" => radicalTable p C L
local notation "nv" => blockCount p C L
local notation "nr" => readoutCount p C L
local notation "ni" => FiniteCode.size (OldInputIndex A₀ R₀ q)
local notation "D₀" => DescriptorPipeline.layout p A₀ R₀ q (nv+2) rs

structure IndexedOutput (hq : 0<q) (S : IState) : Prop where
  records : Records.Output p C L q S.left.left
  coordinates : IncidencePipeline.Output p C L q hq S.left.right
  edges : S.right.array Indices.edgePort=edgeIncidences A₀
  pairs : S.right.array Indices.pairPort=FramePairEncoding.word q

theorem indexed_runs (hdim : ∀t,C.dim t≤2) (hq : 0<q) (hr : 0<nr) (M : ℕ)
    (room : Room p C L q M) (pairs : q*q≤M) (S : IState) (bounded : S.Bounded M)
    (input : Records.Input p C L q S.left.left.left.left) :
    ∃t ≤ idxTime p nv nr ni q,∃T,Runs (storageBound IReg IArr M) (indexed p) S t T ∧
      T.Bounded M ∧ IndexedOutput p C L q hq T := by
  obtain ⟨j,hj,W,run,hW,hPrev,he,hp⟩ := Ports.thenRun_post (prefixProgram p) idxReg idxArr Indices.program
    S M (prefixTime p nv nr ni) (Indices.time (nv*nr) q) bounded (by intro i k h;cases h)
    (fun U => Records.Output p C L q U.left ∧ IncidencePipeline.Output p C L q hq U.right)
    (fun _ U => U.array Indices.edgePort=edgeIncidences A₀ ∧ U.array Indices.pairPort=FramePairEncoding.word q)
    (prefix_runs p C L q hdim hq hr M room S.left bounded.left input) (by
      intro U h _ B
      obtain ⟨k,hk,T,rT,bT,edge,pair⟩ := Indices.program_runs (scopeTable p C L) q M _ B hq
        (by have := room.radControl;omega) pairs h.1.scope h.1.metadata.frames
      have len : (scopeTable p C L).length=nv*nr := List.length_ofFn
      rw [len] at hk
      have eq : RangeSelection.selected (scopeTable p C L)=edgeIncidences A₀ := by
        unfold RangeSelection.selected
        rw [len,←incidenceWord_selected p C L]
        rfl
      exact ⟨k,hk,T,rT,bT,edge.trans eq,pair⟩)
  exact ⟨j,hj,W,run,hW,hPrev.1,hPrev.2,he,hp⟩

def time := idxTime p nv nr ni q+(Fintype.card DescriptorPipeline.Reg+Fintype.card DescriptorPipeline.Arr+
  (1+DescriptorPipeline.cost D₀))

theorem program_runs (hdim : ∀t,C.dim t≤2) (hq : 0<q) (M : ℕ) (room : Room p C L q M) (pairRoom : q*q≤M)
    (dr : DescriptorPipeline.Room p A₀ R₀ q (nv+2) M)
    (S : State) (bounded : S.Bounded M) (input : Records.Input p C L q S.left.left.left.left.left) :
    ∃t≤time p C L q,∃T,Runs (storageBound Reg Arr M) (program p) S t T ∧
      T.Bounded M ∧ IndexedOutput p C L q hq T.left ∧ DescriptorPipeline.CanonicalOutput p A₀ R₀ q T.right := by
  apply Ports.thenRun_post (indexed p) (fun i => .scalar (sourceR i)) sourceA
    (.seq (.atom capStep) DescriptorPipeline.program) S M (idxTime p nv nr ni q) (1+DescriptorPipeline.cost D₀)
    bounded (by intro i k h;cases h) (IndexedOutput p C L q hq) (fun _ T => DescriptorPipeline.CanonicalOutput p A₀ R₀ q T)
  · exact indexed_runs p C L q hdim hq dr.readouts M room pairRoom S.left bounded.left input
  · intro U h _ B
    let P := Ports.target (fun i => .scalar (sourceR i)) sourceA U
    let W := capStep.apply P
    have hb : P.scalar (DescriptorPipeline.inputReg .blocks)=nv := h.records.metadata.blockCount
    have ht : P.scalar (DescriptorPipeline.inputReg .two)=2 := h.records.metadata.two
    have small : capStep.SmallResult M P := by
      simp only [capStep,Atom.SmallResult,BinaryOp.eval,hb,ht]
      have := room.radControl
      omega
    have bound := Atom.apply_bounded B capStep small
    have wire := atom_runs B capStep trivial small
    have inp : DescriptorPipeline.Input D₀ (DescriptorPipeline.inputState W) :=
      ⟨h.records.metadata.frames,by change P.scalar (DescriptorPipeline.inputReg .blocks)+P.scalar (DescriptorPipeline.inputReg .two)=nv+2;rw [hb,ht],
       h.records.metadata.blockCount,h.records.metadata.readouts,h.coordinates.ambient,h.coordinates.dimensions,
       h.coordinates.offsets,h.pairs,h.edges,h.coordinates.radicals⟩
    obtain ⟨t,ht,T,run,hT,_,hout⟩ := DescriptorPipeline.program_runs p A₀ R₀ q (nv+2) rs M dr
      (by exact SourceRadicalTables.collect_length _ _ _ _ _ _ _) (radicalTable_spec p C L hdim)
      (SourceRadicalTables.collect_values _ _ _ _ _ _ _ (Fact.out : p.Prime).one_lt) W bound inp
    exact ⟨1+t,by omega,T,wire.seq run,hT,hout⟩

end GroupWL.MachinePrograms.IncidencePipeline.Descriptors
