import GroupWL.MachinePrograms.IncidencePipeline
import GroupWL.MachinePrograms.KernelToTensor
import GroupWL.MachinePrograms.LayoutRecordCorrectness

/-! Source records to packaged incidence and coefficient words and the canonical chosen coordinates. -/
namespace GroupWL.MachinePrograms.NatArrayLanguage.Ports
variable {R A U V : Type} [DecidableEq R] [DecidableEq A] [DecidableEq U] [DecidableEq V]
variable [Fintype R] [Fintype A] [Fintype U] [Fintype V]

/-- Compose two bounded clients with a literal/copy/length-only wiring program. -/
theorem thenRun_post (first : Program R A) (s : U → Scalar R A) (a : V → Option A)
    (second : Program U V) (S : Store (R⊕U) (A⊕V)) (M t u : ℕ) (bounded : S.Bounded M)
    (small : ∀i k,s i = .literal k → k≤M) (P : Store R A → Prop) (Q : Store R A → Store U V → Prop)
    (run₁ : ∃j≤t,∃T,Runs (storageBound R A M) first S.left j T ∧ T.Bounded M ∧ P T)
    (run₂ : ∀T,P T → T.Bounded M → (target s a T).Bounded M →
        ∃j≤u,∃W,Runs (storageBound U V M) second (target s a T) j W ∧ W.Bounded M ∧ Q T W) :
    ∃j≤t+(Fintype.card U+Fintype.card V+u),∃T,
      Runs (storageBound (R⊕U) (A⊕V) M) (thenRun first s a second) S j T ∧ T.Bounded M ∧
      P T.left ∧ Q T.left T.right := by
  obtain ⟨i,hi,W,r₁,hW,hP⟩ := run₁
  obtain ⟨_,hV⟩ := code_runs s a W S.right M (hW.join bounded.right) small
  obtain ⟨j,hj,Y,r₂,hY,hQ⟩ := run₂ W hP hW hV
  have h := thenRun_runs first s a second S.left W S.right Y M i j bounded.left hW bounded.right small r₁ r₂
  exact ⟨i+(Fintype.card U+Fintype.card V+j),by omega,W.join Y,by simpa only [Store.join_left_right] using h,hW.join hY,hP,hQ⟩

end GroupWL.MachinePrograms.NatArrayLanguage.Ports

namespace GroupWL.MachinePrograms.IncidencePipeline.Records
open NatArrayLanguage SourceTableEncoding SourceLayout
set_option synthInstance.maxSize 16384
set_option maxRecDepth 16384

inductive Header where | horizontal | frames | blocks | readouts | cells | twice | two
  deriving DecidableEq,Fintype
inductive Field where | record (a : SourceCoefficients.Arr) | dimensions | charge
  deriving DecidableEq,Fintype

abbrev HeaderStore := Store Header Field
def countOps : List (Atom Header Field) := [
  .arrayLength .blocks .charge,.arrayLength .readouts .dimensions,
  .binary .mul .cells .blocks .readouts,.const .two 2,.binary .mul .twice .cells .two]

def coeffScalar (p : ℕ) : SourceCoefficientTable.Reg → Ports.Scalar Header Field
  | .inl .horizontal => .scalar .horizontal
  | .inl .modulus => .literal p
  | .inr .readouts => .scalar .readouts
  | .inr .two => .scalar .two
  | .inr .total => .scalar .twice
  | _ => .literal 0

def coeffArray : SourceCoefficientTable.Arr → Option Field
  | .inl a => some (.record a)
  | _ => none

abbrev CReg := Header⊕SourceCoefficientTable.Reg
abbrev CArr := Field⊕SourceCoefficientTable.Arr
noncomputable def coeffProgram (p : ℕ) := Ports.thenRun (atoms countOps) (coeffScalar p) coeffArray SourceCoefficientTable.program

def scopeScalar : SourceIncidenceTable.Reg → Ports.Scalar CReg CArr
  | .inl .horizontal => .scalar (.inl .horizontal)
  | .inr .readouts => .scalar (.inl .readouts)
  | .inr .total => .scalar (.inl .cells)
  | _ => .literal 0

def which : SourceIncidence.Arr → SourceCoefficients.Arr
  | .left => .left | .right => .right | .before => .before | .after => .after

def scopeArray : SourceIncidenceTable.Arr → Option CArr
  | .inl a => some (.inl (.record (which a)))
  | _ => none

abbrev Reg := CReg⊕SourceIncidenceTable.Reg
abbrev Arr := CArr⊕SourceIncidenceTable.Arr
abbrev State := Store Reg Arr
noncomputable def program (p : ℕ) := Ports.thenRun (coeffProgram p) scopeScalar scopeArray SourceIncidenceTable.program

def time (b r : ℕ) := 5+(Fintype.card SourceCoefficientTable.Reg+Fintype.card SourceCoefficientTable.Arr+(b*r*2*34+6))+
  (Fintype.card SourceIncidenceTable.Reg+Fintype.card SourceIncidenceTable.Arr+(b*r*21+6))

variable {X E : Type} [FiniteCode X] [FiniteCode E] {r : ℕ} (p : ℕ) [Fact p.Prime]
  (C : ComparisonData (ZMod p) X E r) (L q : ℕ)

local notation "nv" => blockCount p C L
local notation "nr" => readoutCount p C L

structure Input (S : HeaderStore) : Prop where
  records : ∀a,S.array (.record a)=coefficientData p C L a
  dimension : S.array .dimensions=readoutDimensions p C L
  blocks : (S.array .charge).length=nv
  horizontal : S.scalar .horizontal=horizontalCount p C L
  frames : S.scalar .frames=q

structure Counts (S : HeaderStore) : Prop extends Input p C L q S where
  blockCount : S.scalar .blocks=nv
  readouts : S.scalar .readouts=nr
  cells : S.scalar .cells=nv*nr
  twice : S.scalar .twice=nv*nr*2
  two : S.scalar .two=2

theorem counts_run (M : ℕ) (S : HeaderStore) (bounded : S.Bounded M) (h : Input p C L q S)
    (room : nv*nr*2≤M) (small : 2≤M) :
    ∃t≤5,∃T,Runs (storageBound Header Field M) (atoms countOps) S t T ∧ T.Bounded M ∧ Counts p C L q T := by
  have dr : (S.array .dimensions).length=nr := h.dimension ▸ List.length_ofFn
  have cells : nv*nr≤M := by omega
  obtain ⟨run,B⟩ := atoms_runs bounded countOps (by
    simp [countOps,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,Store.setScalar,BinaryOp.eval,
      dr,h.blocks,room,cells,small])
  refine ⟨5,le_rfl,_,run,B,⟨⟨h.records,h.dimension,h.blocks,?_,?_⟩,?_,?_,?_,?_,?_⟩⟩ <;>
    simp [countOps,applyAtoms,Atom.apply,Store.setScalar,BinaryOp.eval,h.horizontal,h.frames,dr,h.blocks]

omit [Fact p.Prime] in
private theorem coeffSmall (M : ℕ) (hp : p≤M) : ∀i k,coeffScalar p i = .literal k → k≤M := by
  rintro (a|b) k h
  · cases a <;> simp_all [coeffScalar] <;> omega
  · cases b <;> simp_all [coeffScalar] <;> omega

private theorem scopeSmall (M : ℕ) : ∀i k,scopeScalar i = .literal k → k≤M := by
  rintro (a|b) k h
  · cases a <;> simp_all [scopeScalar] <;> omega
  · cases b <;> simp_all [scopeScalar] <;> omega

def scopePort : Arr := .inr (.inr ())
def coeffPort : Arr := .inl (.inr (.inr ()))

structure Output (S : State) : Prop where
  metadata : Counts p C L q S.left.left
  scope : S.array scopePort=scopeTable p C L
  coefficients : S.array coeffPort=coefficientTable p C L

theorem program_runs (M : ℕ) (S : State) (bounded : S.Bounded M) (input : Input p C L q S.left.left)
    (positive : 0<nr) (room : nv*nr*2≤M) (fieldRoom : 6*p+4≤M) :
    ∃t≤time nv nr,∃T,Runs (storageBound Reg Arr M) (program p) S t T ∧ T.Bounded M ∧ Output p C L q T := by
  have coeffs := Ports.thenRun_post (atoms countOps) (coeffScalar p) coeffArray SourceCoefficientTable.program
    S.left M 5 (nv*nr*2*34+6) bounded.left (coeffSmall p M (by omega))
    (Counts p C L q) (fun _ W => W.array (.inr ())=coefficientTable p C L)
    (counts_run p C L q M S.left.left bounded.left.left input room (by omega))
    (by
      intro T h _ B
      let P := Ports.target (coeffScalar p) coeffArray T
      have ready : SourceCoefficientTable.Ready (coefficientData p C L) (horizontalCount p C L) p nv nr P :=
        ⟨funext h.records,h.horizontal,rfl,h.readouts,h.two,h.twice⟩
      obtain ⟨t,ht,W,run,hW,_,hw⟩ := SourceCoefficientTable.program_runs (coefficientData p C L)
        (horizontalCount p C L) p nv nr M positive fieldRoom (coefficientData_valid p C L) P ready B
      exact ⟨t,ht,W,run,hW,hw⟩)
  obtain ⟨t,ht,T,run,hT,hHeader,hScope⟩ := Ports.thenRun_post (coeffProgram p) scopeScalar scopeArray
    SourceIncidenceTable.program S M _ (nv*nr*21+6) bounded (scopeSmall M)
    (fun W => Counts p C L q W.left ∧ W.right.array (.inr ())=coefficientTable p C L)
    (fun _ W => W.array (.inr ())=scopeTable p C L) coeffs (by
      intro T h _ B
      let P := Ports.target scopeScalar scopeArray T
      have ready : SourceIncidenceTable.Ready (incidenceData p C L) (horizontalCount p C L) nv nr P :=
        ⟨by funext a; cases a <;> exact h.1.records _,h.1.horizontal,h.1.readouts,h.1.cells⟩
      obtain ⟨t,ht,W,run,hW,_,hw⟩ := SourceIncidenceTable.program_runs (incidenceData p C L)
        (horizontalCount p C L) nv nr M positive (by omega) (incidenceData_valid p C L) P ready B
      exact ⟨t,ht,W,run,hW,hw⟩)
  exact ⟨t,ht,T,run,hT,hHeader.1,hScope,hHeader.2⟩

end GroupWL.MachinePrograms.IncidencePipeline.Records

namespace GroupWL.MachinePrograms.IncidencePipeline
open NatArrayLanguage SourceLayout SourceTableEncoding ConstructiveIncidence
set_option synthInstance.maxSize 16384
set_option maxRecDepth 16384

def coordSource : Reg → Records.Reg
  | .inl (.inr .blocks) => .inl (.inl .blocks)
  | .inl (.inr .readouts) => .inl (.inl .readouts)
  | _ => .inl (.inl .frames)

def coordArray : Arr → Option Records.Arr
  | .inl (.inr .scope) => some Records.scopePort
  | .inl (.inr .coefficients) => some Records.coeffPort
  | .inl (.inr .dimensions) => some (.inl (.inl .dimensions))
  | _ => none

abbrev PrefixReg := Records.Reg⊕Reg
abbrev PrefixArr := Records.Arr⊕Arr
abbrev PrefixState := Store PrefixReg PrefixArr
noncomputable def prefixProgram (p : ℕ) : NatArrayLanguage.Program PrefixReg PrefixArr :=
  Ports.thenRun (Records.program p) (fun i => .scalar (coordSource i)) coordArray (coordinates p)

def prefixTime (p b r n : ℕ) := Records.time b r+(Fintype.card Reg+Fintype.card Arr+time p b r n)

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
local notation "nr" => readoutCount p C L
local notation "ni" => FiniteCode.size (OldInputIndex A₀ R₀ q)

structure Room (M : ℕ) : Prop where
  recordField : 6*p+4≤M
  recordCells : nv*nr*2≤M
  radControl : 2*nv+2≤M
  fieldRoom : p*p+p≤M
  radSquare : nv*nv≤M
  radTable : nv*nr*nv≤M
  sizeRoom : (nv+nr)*(nv+2)*q≤M
  selectorRoom : (nv+nr)*ni≤M
  chosenRoom : ni*ni≤M

theorem prefix_runs (hdim : ∀t,C.dim t≤2) (hq : 0<q) (hr : 0<nr) (M : ℕ) (room : Room p C L q M)
    (S : PrefixState) (bounded : S.Bounded M) (input : Records.Input p C L q S.left.left.left) :
    ∃t≤prefixTime p nv nr ni,∃T,Runs (storageBound PrefixReg PrefixArr M) (prefixProgram p) S t T ∧
      T.Bounded M ∧ Records.Output p C L q T.left ∧ Output p C L q hq T.right := by
  apply Ports.thenRun_post (Records.program p) (fun i => .scalar (coordSource i)) coordArray (coordinates p)
    S M (Records.time nv nr) (time p nv nr ni) bounded (by intro i k h; cases h)
    (Records.Output p C L q) (fun _ T => Output p C L q hq T)
  · exact Records.program_runs p C L q M S.left bounded.left input hr room.recordCells room.recordField
  · intro W h _ B
    exact coordinates_runs p C L q hdim hq M room.radControl room.fieldRoom room.radSquare room.radTable
      room.sizeRoom room.selectorRoom room.chosenRoom _ B
      ⟨h.scope,h.coefficients,h.metadata.dimension,h.metadata.blockCount,h.metadata.readouts,h.metadata.frames⟩

/-- The exact six records, dimensions and charge emitted by the layout producer suffice for the prefix. -/
theorem records_from_layout (selected : ℕ) (U : LayoutRecordPrograms.State)
    (h : LayoutRecordPrograms.Output (ComparisonMetadata.ofComparison p C) L selected U)
    (S : Records.HeaderStore) (recordPorts : ∀a,S.array (.record a)=U.array (LayoutRecordPrograms.coefficientArray a))
    (dimensionPort : S.array .dimensions=U.array LayoutRecordPrograms.dimensionArray)
    (chargePort : S.array .charge=U.array LayoutRecordPrograms.chargeArray)
    (horizontalPort : S.scalar .horizontal=U.scalar (LayoutRecordPrograms.oldr (LayoutIncidencePrograms.hreg .count)))
    (frames : S.scalar .frames=q) : Records.Input p C L q S := by
  refine ⟨fun a => (recordPorts a).trans (h.coefficients p C L selected a),
    dimensionPort.trans (h.dimension_correct p C L selected),?_,?_,frames⟩
  · rw [chargePort,h.charge_correct p C L selected]
    exact List.length_ofFn
  · exact horizontalPort.trans (h.forms.incidence.metadata.ranks.horizontalCount.trans (LayoutMetadata.horizontalCount_correct p C L))

end GroupWL.MachinePrograms.IncidencePipeline
