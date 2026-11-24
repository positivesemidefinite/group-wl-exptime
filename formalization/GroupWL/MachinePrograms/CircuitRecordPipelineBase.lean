import GroupWL.MachinePrograms.CircuitRecordPipelineDecode

/-! Register initialization for circuit metadata table sizes. -/
namespace GroupWL.MachinePrograms.CircuitRecordPipeline
open NatArrayLanguage AddressedCircuit CircuitMetadataValues CircuitComparisonCodes CircuitDescription
open CircuitMetadataExpressions (Field Input)
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 2000000

abbrev sr (a : CircuitMetadataExpressions.Reg) : BaseReg := .inl a
abbrev fr (a : Field) : BaseReg := .inr a

def countAtoms : List (Atom BaseReg Input) := [
  .const (sr .one) 2, .const (sr .zero) 3,
  .binary .add (sr .index) (sr .edges) (sr .tests),
  .binary .add (sr .index) (sr .index) (sr .coordinates),
  .binary .add (sr .index) (sr .index) (sr .ports),
  .binary .add (sr .index) (sr .index) (sr .ports),
  .binary .add (sr .index) (sr .index) (sr .one),
  .binary .add (fr .dimension) (sr .types) (sr .one),
  .binary .add (fr .dimension) (fr .dimension) (sr .index),
  .binary .mul (fr .source) (sr .index) (sr .zero),
  .binary .add (fr .source) (sr .seeds) (fr .source),
  .copy (fr .target) (fr .source),
  .binary .mul (fr .sourceForm) (fr .source) (sr .one),
  .copy (fr .targetForm) (fr .sourceForm),
  .binary .mul (fr .permutation) (fr .source) (sr .coordinates),
  .binary .mul (fr .domain) (fr .permutation) (sr .one)]

def rawArr : Input → Decode.Arr
  | .kinds => .inl (.inl (CircuitParserStages.wa .kinds))
  | .schemas => .inl (.inl (CircuitParserStages.wa .schemas))
  | .seeds => .inl (.inl (CircuitParserStages.wa .seeds))
  | .tests => .inl (.inl (CircuitParserStages.wa .tests))
  | .owners => .inl (.inr Packed.output)
  | .ports => .inr Packed.output

abbrev parseReg (r : CircuitParserStages.WorkReg) : Decode.Reg := .inl (.inl (CircuitParserStages.wr r))
def rawScalar : BaseReg → Ports.Scalar Decode.Reg Decode.Arr
  | .inl .types => .scalar (parseReg .types)
  | .inl .coordinates => .scalar (parseReg .coordinates)
  | .inl .edges => .scalar (parseReg .edges)
  | .inl .seeds => .scalar (parseReg .seeds)
  | .inl .tests => .scalar (parseReg .tests)
  | .inl .ports => .length (rawArr .ports)
  | .inl .lKinds => .length (rawArr .kinds)
  | .inl .lSchemas => .length (rawArr .schemas)
  | .inl .lSeeds => .length (rawArr .seeds)
  | .inl .lTests => .length (rawArr .tests)
  | .inl .lOwners => .length (rawArr .owners)
  | .inl .lPorts => .length (rawArr .ports)
  | _ => .literal 0

variable {T : Type} [FiniteCode T] {r : ℕ}

def raw (P : Store Decode.Reg Decode.Arr) : Base := Ports.target rawScalar (some ∘ rawArr) P

theorem raw_data (C : Circuit T r) {P} (out : Decode.Output C P) :
    CircuitMetadataExpressions.readData (baseData (raw P))=ofCircuit C := by
  have hp := out.parsed
  have hv : (P.array (rawArr .ports)).length=portCount C := out.ports ▸ packed_length C .port
  unfold CircuitMetadataExpressions.readData baseData raw Ports.target ofCircuit
  congr 1 <;> first | exact hp.metadata.types | exact hp.metadata.coordinates | exact hp.metadata.edges | exact hp.metadata.seeds | exact hp.metadata.tests | exact hv | exact hp.kinds | exact hp.schemas | exact hp.seeds | exact hp.tests | exact out.owners | exact out.ports

theorem raw_lengths (P : Store Decode.Reg Decode.Arr) (a : Input) :
    (raw P).scalar (.inl (CircuitMetadataExpressions.sizeRegister a))=((raw P).array a).length := by
  cases a <;> rfl

theorem count_runs (D : Data) (S : Base) (B M : ℕ) (bS : S.Bounded B)
    (room : 6≤B) (data : CircuitMetadataExpressions.readData (baseData S)=D)
    (lens : ∀a,S.scalar (sr (CircuitMetadataExpressions.sizeRegister a))=(S.array a).length)
    (size : ∀f,fieldSize D f≤B) (budget : ∀f,(B+2)^(2*((CircuitMetadataExpressions.entry f).expression CircuitMetadataExpressions.sizeRegister).cost)≤M) :
    Runs (storageBound BaseReg Input B) (atoms countAtoms) S 16 (applyAtoms countAtoms S) ∧
      (applyAtoms countAtoms S).Bounded B ∧ Prepared D B M (applyAtoms countAtoms S) := by
  subst D
  have bd := size .dimension
  have bs := size .source
  have bf := size .sourceForm
  have bp := size .permutation
  have ba := size .domain
  simp only [fieldSize,Data.connections,Data.realTypes,Data.comparisons,CircuitMetadataExpressions.readData,baseData] at bd bs bf bp ba
  have valid : ValidAtoms B countAtoms S := by
    simp [countAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar,sr,fr]
    omega
  obtain ⟨run,bU⟩ := atoms_runs bS countAtoms valid
  let U := applyAtoms countAtoms S
  have hdata : CircuitMetadataExpressions.readData (baseData U)=CircuitMetadataExpressions.readData (baseData S) := rfl
  refine ⟨run,bU,hdata,?_,?_,room,fun i _ => bU.1 _,bU.2.2,size,budget⟩
  · intro a; cases a <;> exact lens _
  · intro f
    cases f <;> simp [countAtoms,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,sr,fr,fieldSize,Data.connections,
      Data.realTypes,Data.comparisons,CircuitMetadataExpressions.readData,baseData]

end GroupWL.MachinePrograms.CircuitRecordPipeline
