import GroupWL.ComparisonMetadata
import GroupWL.MachinePrograms.FilterRanks
import GroupWL.MachinePrograms.RectangleFlags

/-! Explicit natural indices for the private wires and their square records. -/
namespace GroupWL.LayoutMetadata
open ComparisonMetadata

def nodeCount (C : Table) (L : ℕ) : ℕ := C.types+C.comparisons*(L+1)
def linkCount (C : Table) (L : ℕ) : ℕ := C.comparisons+C.comparisons*L+C.comparisons
def linkComparison (C : Table) (L l : ℕ) : ℕ :=
  if l<C.comparisons then l
  else if l<C.comparisons+C.comparisons*L then (l-C.comparisons)/L
  else l-(C.comparisons+C.comparisons*L)
def leftNode (C : Table) (L l : ℕ) : ℕ :=
  if l<C.comparisons then C.source[l]?.getD 0
  else if l<C.comparisons+C.comparisons*L then
    C.types+(l-C.comparisons)/L*(L+1)+(l-C.comparisons)%L
  else C.types+(l-(C.comparisons+C.comparisons*L))*(L+1)+L
def rightNode (C : Table) (L l : ℕ) : ℕ :=
  if l<C.comparisons then C.types+l*(L+1)
  else if l<C.comparisons+C.comparisons*L then
    C.types+(l-C.comparisons)/L*(L+1)+(l-C.comparisons)%L+1
  else C.target[l-(C.comparisons+C.comparisons*L)]?.getD 0
def nodeLabel (C : Table) (L index : ℕ) : ℕ :=
  let node := index/2/C.coordinates
  let coordinate := index/2%C.coordinates
  let a := index%2
  if node<C.types then 1
  else C.domain[2*((node-C.types)/(L+1)*C.coordinates+coordinate)+a]?.getD 0
def linkLabel (C : Table) (L index : ℕ) : ℕ :=
  let link := index/2/C.coordinates
  let coordinate := index/2%C.coordinates
  C.domain[2*(linkComparison C L link*C.coordinates+coordinate)+index%2]?.getD 0
def nodeLabels (C : Table) (L : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin (nodeCount C L*C.coordinates*2) => nodeLabel C L i)
def linkLabels (C : Table) (L : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin (linkCount C L*C.coordinates*2) => linkLabel C L i)
def horizontalFlags (C : Table) (L : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin (nodeCount C L*C.coordinates*4) =>
    MachinePrograms.RectangleFlags.entry (nodeLabels C L) C.coordinates i)
def squareFlags (C : Table) (L : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin (linkCount C L*C.coordinates*4) =>
    MachinePrograms.RectangleFlags.entry (linkLabels C L) C.coordinates i)
def horizontalCount (C : Table) (L : ℕ) : ℕ :=
  MachinePrograms.FilterRanks.count (horizontalFlags C L) (horizontalFlags C L).length
def verticalCount (C : Table) (L : ℕ) : ℕ :=
  MachinePrograms.FilterRanks.count (linkLabels C L) (linkLabels C L).length
def squareCount (C : Table) (L : ℕ) : ℕ :=
  MachinePrograms.FilterRanks.count (squareFlags C L) (squareFlags C L).length
def horizontalRank (C : Table) (L key : ℕ) : ℕ := MachinePrograms.FilterRanks.count (horizontalFlags C L) key
def verticalRank (C : Table) (L key : ℕ) : ℕ := MachinePrograms.FilterRanks.count (linkLabels C L) key
def squareRank (C : Table) (L key : ℕ) : ℕ := MachinePrograms.FilterRanks.count (squareFlags C L) key
def rightLabel (C : Table) (L l i a : ℕ) : ℕ :=
  if l<C.comparisons+C.comparisons*L then a
  else if C.permutation[(linkComparison C L l)*C.coordinates+i]?.getD 0=0 then a else 1-a
def horizontalKey (C : Table) (node coordinate a b : ℕ) : ℕ := 4*(node*C.coordinates+coordinate)+2*a+b
def verticalKey (C : Table) (link coordinate a : ℕ) : ℕ := 2*(link*C.coordinates+coordinate)+a
def squareLeft (C : Table) (L key : ℕ) : ℕ :=
  horizontalRank C L (horizontalKey C (leftNode C L (key/4/C.coordinates))
    (key/4%C.coordinates) (key%4/2) (key%4%2))
def squareRight (C : Table) (L key : ℕ) : ℕ :=
  let l := key/4/C.coordinates
  let i := key/4%C.coordinates
  horizontalRank C L (horizontalKey C (rightNode C L l) i
    (rightLabel C L l i (key%4/2)) (rightLabel C L l ((i+1)%C.coordinates) (key%4%2)))
def squareBefore (C : Table) (L key : ℕ) : ℕ :=
  horizontalCount C L+verticalRank C L
    (verticalKey C (key/4/C.coordinates) (key/4%C.coordinates) (key%4/2))
def squareAfter (C : Table) (L key : ℕ) : ℕ :=
  horizontalCount C L+verticalRank C L
    (verticalKey C (key/4/C.coordinates) ((key/4%C.coordinates+1)%C.coordinates) (key%4%2))
def leftForm (C : Table) (L l k : ℕ) : ℕ :=
  if l<C.comparisons then C.sourceForm[2*l+k]?.getD 0 else if k=0 then 1 else 0
def rightForm (C : Table) (L l k : ℕ) : ℕ :=
  if l<C.comparisons+C.comparisons*L then (if k=0 then 1 else 0)
  else C.targetForm[2*(linkComparison C L l)+k]?.getD 0
def nodeDimension (C : Table) (L node : ℕ) : ℕ :=
  if node<C.types then C.dimensions[node]?.getD 0 else 1

def squareCharge (C : Table) (L chargedComparison key : ℕ) : ℕ :=
  if key/4/C.coordinates=C.comparisons+C.comparisons*L+chargedComparison ∧
    key/4%C.coordinates+1=C.coordinates then 1 else 0

end GroupWL.LayoutMetadata
