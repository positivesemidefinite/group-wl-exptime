import GroupWL.MachinePrograms.GadgetPairTables
import GroupWL.MachinePrograms.GadgetSelectionBuilder
import GroupWL.MachinePrograms.GraphWLCoreCorrectness
import GroupWL.MachinePrograms.NeighborWLCore
import GroupWL.MachinePrograms.TupleDimensions

/-! Closed finite syntax for the complete Version-III table algorithm.
The component execution theorems are proved in the imported modules;
the execution theorem for this final staging composition remains to be supplied. -/
namespace GroupWL.MachinePrograms.GraphWLTableProgram
open NatArrayLanguage
abbrev Reg := Fin 3 ⊕ (GadgetPairTables.Reg ⊕ (TupleDimensions.Reg ⊕ (GadgetSelectionBuilder.Reg ⊕
  (GraphWLCore.Reg ⊕ (DisjointGraphTable.Reg ⊕ NeighborWLCore.Reg)))))
abbrev Arr := Unit ⊕ (GadgetPairTables.Arr ⊕ (TupleDimensions.Arr ⊕ (GadgetSelectionBuilder.Arr ⊕
  (GraphWLCore.Arr ⊕ (DisjointGraphTable.Arr ⊕ NeighborWLCore.Arr)))))
abbrev Code := NatArrayLanguage.Program Reg Arr
set_option synthInstance.maxSize 16384
set_option maxRecDepth 8192
instance : DecidableEq Reg := inferInstance
instance : DecidableEq Arr := inferInstance
instance : Fintype Reg := inferInstance
instance : Fintype Arr := inferInstance

def control (r : Fin 3) : Reg := .inl r
def gadgets (r : GadgetPairTables.Reg) : Reg := .inr (.inl r)
def gadgetArray (a : GadgetPairTables.Arr) : Arr := .inr (.inl a)
def dimensions (r : TupleDimensions.Reg) : Reg := .inr (.inr (.inl r))
def dimensionArray (a : TupleDimensions.Arr) : Arr := .inr (.inr (.inl a))
def selection (r : GadgetSelectionBuilder.Reg) : Reg := .inr (.inr (.inr (.inl r)))
def selected (a : GadgetSelectionBuilder.Arr) : Arr := .inr (.inr (.inr (.inl a)))
def graph (r : GraphWLCore.Reg) : Reg := .inr (.inr (.inr (.inr (.inl r))))
def graphArray (a : GraphWLCore.Arr) : Arr := .inr (.inr (.inr (.inr (.inl a))))
def union (r : DisjointGraphTable.Reg) : Reg := .inr (.inr (.inr (.inr (.inr (.inl r)))))
def unionArray (a : DisjointGraphTable.Arr) : Arr := .inr (.inr (.inr (.inr (.inr (.inl a)))))
def neighbor (r : NeighborWLCore.Reg) : Reg := .inr (.inr (.inr (.inr (.inr (.inr r)))))
def neighborArray (a : NeighborWLCore.Arr) : Arr := .inr (.inr (.inr (.inr (.inr (.inr a)))))

def prepareDimensions : List (Atom Reg Arr) := [
  .copy (dimensions 0) (gadgets (.inl (.inr 5))),.copy (dimensions 1) (gadgets (.inr (.inr 5))),
  .copy (dimensions 2) (control 0)]
def prepareSelection : List (Atom Reg Arr) := [
  .copy (selection (.inl (.inl 0))) (gadgets (.inl (.inl 0))),
  .copy (selection (.inl (.inl 1))) (dimensions 0),
  .copy (selection (.inl (.inr 0))) (control 0),.const (selection (.inl (.inr 1))) 0,
  .copy (selection (.inr 0)) (gadgets (.inr (.inl 0))),
  .copy (selection (.inr 1)) (dimensions 1),.copy (selection (.inr 2)) (dimensions 8)]
def prepareGraph : List (Atom Reg Arr) := [
  .copy (graph (GraphWLCore.wl .leftCount)) (dimensions 0),
  .copy (graph (GraphWLCore.wl .rightCount)) (dimensions 1),
  .copy (graph (GraphWLCore.wl .arity)) (control 0),
  .copyArray (graphArray (GraphWLCore.array .fanouts)) (gadgetArray (.inl (.inr ()))),
  .copyArray (graphArray (GraphWLCore.array .targets)) (gadgetArray (.inr (.inr ()))),
  .copyArray (graphArray (GraphWLCore.array .leftSelection)) (selected (.inr ())),
  .copyArray (graphArray (GraphWLCore.array .rightSelection)) (selected (.inl (.inr ())))]
def prepareUnion : List (Atom Reg Arr) := [
  .copy (union 0) (dimensions 0),.copy (union 1) (dimensions 1),
  .copyArray (unionArray 0) (gadgetArray (.inl (.inr ()))),
  .copyArray (unionArray 1) (gadgetArray (.inr (.inr ())))]
def prepareNeighbor : List (Atom Reg Arr) := [
  .copy (neighbor (.inl (.inl 0))) (union 2),
  .copyArray (neighborArray (.inl (.inl ()))) (unionArray 2),
  .copyArray (neighborArray (.inr .leftSelection)) (selected (.inr ())),
  .copyArray (neighborArray (.inr .rightSelection)) (selected (.inl (.inr ())))]

def tuples : Code := .seq (atoms prepareGraph) (.seq (GraphWLCore.decide.map graph graphArray)
  (.atom (.copy (control 2) (graph (GraphWLCore.wl .result)))))
def neighbors : Code := .seq (atoms prepareUnion)
  (.seq (DisjointGraphTable.generate.map union unionArray)
    (.seq (atoms prepareNeighbor) (.seq (NeighborWLCore.decide.map neighbor neighborArray)
      (.atom (.copy (control 2) (neighbor (.inr .result)))))))

/-- Input: arity at `control 0`; both group tables/orders in the gadget pair slots.
Output: acceptance at `control 2`. -/
def decide : Code := NatArrayLanguage.sequence [
  GadgetPairTables.generate.map gadgets gadgetArray,
  atoms prepareDimensions,TupleDimensions.program.map dimensions dimensionArray,
  atoms prepareSelection,GadgetSelectionBuilder.generate.map selection selected,
  atoms [.const (control 1) 1,.binary .eq (control 1) (control 0) (control 1)],
  .branch (control 1) neighbors tuples]

end GroupWL.MachinePrograms.GraphWLTableProgram
