import GroupWL.GateCoordinateEncoding
import GroupWL.MachinePrograms.CircuitRecordEntries
import GroupWL.ComparisonMetadata

/-! Numeric formulas for the circuit-to-comparison metadata construction. -/
namespace GroupWL.CircuitMetadataValues
open CircuitComparisons AddressedCircuit MachinePrograms.CircuitRecordParser

structure Data where
  types : ℕ
  coordinates : ℕ
  edges : ℕ
  seeds : ℕ
  tests : ℕ
  ports : ℕ
  kinds : List ℕ
  schemas : List ℕ
  seedRequests : List ℕ
  testRequests : List ℕ
  owners : List ℕ
  portNumbers : List ℕ

def ofCircuit {T : Type} [FiniteCode T] {r : ℕ} (C : Circuit T r) : Data where
  types := FiniteCode.size T
  coordinates := r
  edges := C.edges
  seeds := C.seedCount
  tests := C.testCount
  ports := CircuitComparisonCodes.portCount C
  kinds := CircuitComparisonCodes.kinds C
  schemas := (schemaRecords C).map Token.value
  seedRequests := (seedRecords C).map Token.value
  testRequests := (testRecords C).map Token.value
  owners := CircuitComparisonCodes.packed C .owner
  portNumbers := CircuitComparisonCodes.packed C .port

namespace Data

def connections (D : Data) : ℕ := D.edges+D.tests+D.coordinates+D.ports+D.ports+2
def realTypes (D : Data) : ℕ := D.types+2+D.connections
def comparisons (D : Data) : ℕ := D.seeds+D.connections*3
def schemaStride (D : Data) : ℕ := 3+3*D.coordinates
def requestStride (D : Data) : ℕ := 1+2*D.coordinates

def connectionCase (D : Data) (i : ℕ) : ℕ × ℕ :=
  if i<D.edges then (0,i) else
  let i := i-D.edges
  if i<D.tests then (1,i) else
  let i := i-D.tests
  if i<D.coordinates then (2,i) else
  let i := i-D.coordinates
  if i<D.ports then (3,i) else
  let i := i-D.ports
  if i<D.ports then (4,i) else (5,i-D.ports)

def sourceGate (D : Data) (kind index : ℕ) : ℕ :=
  if kind=0 then D.schemas[index*D.schemaStride]?.getD 0
  else D.testRequests[index*D.requestStride]?.getD 0

def connectionSource (D : Data) (i : ℕ) : ℕ :=
  let (kind,index) := D.connectionCase i
  if kind<2 then D.sourceGate kind index
  else if kind=4 then D.owners[index]?.getD 0 else D.types

def connectionTarget (D : Data) (i : ℕ) : ℕ :=
  let (kind,index) := D.connectionCase i
  if kind=0 then D.schemas[index*D.schemaStride+1]?.getD 0
  else if kind=3 ∨ kind=4 then D.owners[index]?.getD 0 else D.types

def gateOutput (D : Data) (gate k : ℕ) : ℕ :=
  if k=0 then 1 else D.kinds[gate]?.getD 0

def connectionSourceForm (D : Data) (i k : ℕ) : ℕ :=
  let (kind,index) := D.connectionCase i
  if kind<2 then D.gateOutput (D.sourceGate kind index) k
  else if kind=4 then if k=D.portNumbers[index]?.getD 0 then 1 else 0
  else if k=0 then 1 else 0

def connectionTargetForm (D : Data) (i k : ℕ) : ℕ :=
  let (kind,index) := D.connectionCase i
  if kind=0 then
    let gate := D.schemas[index*D.schemaStride+1]?.getD 0
    let port := D.schemas[index*D.schemaStride+2]?.getD 0
    if k=D.kinds[gate]?.getD 0*port then 1 else 0
  else if kind=3 ∨ kind=4 then if k=D.portNumbers[index]?.getD 0 then 1 else 0
  else if k=0 then 1 else 0

def connectionDomain (D : Data) (i coordinate bit : ℕ) : ℕ :=
  let (kind,index) := D.connectionCase i
  if kind=0 then D.schemas[index*D.schemaStride+3+2*coordinate+bit]?.getD 0
  else if kind=1 then D.testRequests[index*D.requestStride+1+2*coordinate+bit]?.getD 0
  else 1

def connectionPermutation (D : Data) (i coordinate : ℕ) : ℕ :=
  let (kind,index) := D.connectionCase i
  if kind=0 then D.schemas[index*D.schemaStride+3+2*D.coordinates+coordinate]?.getD 0
  else if kind=2 then if coordinate=index then 1 else 0 else 0

def dimension (D : Data) (i : ℕ) : ℕ :=
  if i<D.types then 1+D.kinds[i]?.getD 0
  else if i<D.types+2 then 1 else 2

def source (D : Data) (i : ℕ) : ℕ :=
  if i<D.seeds then D.seedRequests[i*D.requestStride]?.getD 0 else
  let index := (i-D.seeds)/3
  if (i-D.seeds)%3=0 then D.types+2+index else D.connectionSource index

def target (D : Data) (i : ℕ) : ℕ :=
  if i<D.seeds then D.types+1 else
  let index := (i-D.seeds)/3
  if (i-D.seeds)%3=0 then D.connectionTarget index else D.types+2+index

def sourceForm (D : Data) (i k : ℕ) : ℕ :=
  if i<D.seeds then D.gateOutput (D.seedRequests[i*D.requestStride]?.getD 0) k else
  let index := (i-D.seeds)/3
  if (i-D.seeds)%3=0 then 1 else D.connectionSourceForm index k

def targetForm (D : Data) (i k : ℕ) : ℕ :=
  if i<D.seeds then 0 else
  let index := (i-D.seeds)/3
  if (i-D.seeds)%3=0 then D.connectionTargetForm index k
  else if k=(i-D.seeds)%3-1 then 1 else 0

def domain (D : Data) (i coordinate bit : ℕ) : ℕ :=
  if i<D.seeds then D.seedRequests[i*D.requestStride+1+2*coordinate+bit]?.getD 0
  else D.connectionDomain ((i-D.seeds)/3) coordinate bit

def permutation (D : Data) (i coordinate : ℕ) : ℕ :=
  if i<D.seeds then 0 else
  if (i-D.seeds)%3=0 then D.connectionPermutation ((i-D.seeds)/3) coordinate else 0

def table (D : Data) : ComparisonMetadata.Table where
  types := D.realTypes
  comparisons := D.comparisons
  coordinates := D.coordinates
  dimensions := List.ofFn (fun i : Fin D.realTypes => D.dimension i)
  source := List.ofFn (fun i : Fin D.comparisons => D.source i)
  target := List.ofFn (fun i : Fin D.comparisons => D.target i)
  sourceForm := (List.ofFn (fun i : Fin D.comparisons => List.ofFn (fun k : Fin 2 => D.sourceForm i k))).flatten
  targetForm := (List.ofFn (fun i : Fin D.comparisons => List.ofFn (fun k : Fin 2 => D.targetForm i k))).flatten
  domain := MachinePrograms.EvaluationAssembly.entries3 (fun (i : Fin D.comparisons) (j : Fin D.coordinates) (a : Fin 2) => D.domain i j a)
  permutation := (List.ofFn (fun i : Fin D.comparisons => List.ofFn (fun j : Fin D.coordinates => D.permutation i j))).flatten

end Data
end GroupWL.CircuitMetadataValues
