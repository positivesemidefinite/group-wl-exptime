import GroupWL.MachinePrograms.NatArrayLoops
import GroupWL.IndexedRefinement

/-! Explicit finite-register program for the indexed refinement matrices.
All neighbor tables and both relation matrices are stored in concrete arrays.
The correctness proof is developed against IndexedRefinement.refine. -/
namespace GroupWL.MachinePrograms.IndexedWL

open NatArrayLanguage

inductive Reg where
  | n | arity | width | zero | one | square | vectorLimit
  | round | roundTodo | row | rowTodo | column | columnTodo
  | value | valueTodo | slot | slotTodo | coordinate | coordinateTodo
  | decodeValue | quotient | digit
  | rowBase | slotBase | targetIndex | targetCode | matrixIndex | cellIndex
  | fanout | matched | entry | leftCount | rightCount | flag | temp
  | selectionSize | selectionIndex | selectionTodo | selected | result
  deriving DecidableEq, Fintype

inductive Arr where
  | matrix | nextMatrix | fanouts | targets | vector | leftSelection | rightSelection
  deriving DecidableEq, Fintype

abbrev Code := Program Reg Arr

def atom (a : Atom Reg Arr) : Code := .atom a

/-- Counted ascending loop. The one register is initialized to one by the
whole program. Every loop has its own displayed countdown register. -/
def loop (index remaining limit : Reg) (body : Code) : Code := sequence [
  atom (.copy remaining limit),
  atom (.const index 0),
  .while remaining (sequence [
    body,
    atom (.binary .add index index .one),
    atom (.binary .sub remaining remaining .one)])]

/-- Decode one vector index into its fixed-length little-endian coordinates. -/
def decodeVector : Code := sequence [
  atom (.copy .decodeValue .value),
  loop .coordinate .coordinateTodo .arity (sequence [
    atom (.divmod .quotient .digit .decodeValue .n),
    atom (.write .vector .coordinate .digit),
    atom (.copy .decodeValue .quotient)])]

/-- Count replacement vectors at one row which match the stored vector. -/
def countAt (row destination : Reg) : Code := sequence [
  atom (.const destination 0),
  atom (.read .fanout .fanouts row),
  atom (.binary .mul .rowBase .width row),
  atom (.binary .mul .rowBase .arity .rowBase),
  loop .slot .slotTodo .fanout (sequence [
    atom (.const .matched 1),
    atom (.binary .mul .slotBase .arity .slot),
    atom (.binary .add .slotBase .rowBase .slotBase),
    loop .coordinate .coordinateTodo .arity (sequence [
      atom (.binary .add .targetIndex .slotBase .coordinate),
      atom (.read .targetCode .targets .targetIndex),
      atom (.read .digit .vector .coordinate),
      atom (.binary .mul .matrixIndex .n .digit),
      atom (.binary .add .matrixIndex .targetCode .matrixIndex),
      atom (.read .temp .matrix .matrixIndex),
      atom (.binary .mul .matched .matched .temp)]),
    atom (.binary .add destination destination .matched)])]

def nextCell : Code := sequence [
  atom (.binary .mul .cellIndex .n .row),
  atom (.binary .add .cellIndex .column .cellIndex),
  atom (.read .entry .matrix .cellIndex),
  loop .value .valueTodo .vectorLimit (
    .branch .entry (sequence [
      decodeVector,
      countAt .row .leftCount,
      countAt .column .rightCount,
      atom (.binary .eq .flag .leftCount .rightCount),
      atom (.binary .mul .entry .entry .flag)]) .skip),
  atom (.write .nextMatrix .cellIndex .entry)]

/-- One materialized matrix round. Reads use only the old matrix and writes
use only the next matrix until the complete round is finished. -/
def round : Code := sequence [
  loop .row .rowTodo .n (loop .column .columnTodo .n nextCell),
  atom (.copyArray .matrix .nextMatrix)]

/-- The fixed finite program runs precisely n^2 refinement rounds. -/
def refinement : Code := sequence [
  atom (.const .zero 0),
  atom (.const .one 1),
  atom (.binary .mul .square .n .n),
  atom (.const .vectorLimit 1),
  loop .coordinate .coordinateTodo .arity
    (atom (.binary .mul .vectorLimit .vectorLimit .n)),
  atom (.allocate .vector .arity .zero),
  atom (.allocate .nextMatrix .square .zero),
  loop .round .roundTodo .square round]

/-- Count one row of the final relation on a designated vertex selection. -/
def selectedCount (selection : Arr) (destination : Reg) : Code := sequence [
  atom (.const destination 0),
  atom (.arrayLength .selectionSize selection),
  atom (.binary .mul .rowBase .n .row),
  loop .selectionIndex .selectionTodo .selectionSize (sequence [
    atom (.read .selected selection .selectionIndex),
    atom (.binary .add .matrixIndex .selected .rowBase),
    atom (.read .temp .matrix .matrixIndex),
    atom (.binary .add destination destination .temp)])]

def histogram : Code := sequence [
  atom (.const .result 1),
  loop .row .rowTodo .n (sequence [
    selectedCount .leftSelection .leftCount,
    selectedCount .rightSelection .rightCount,
    atom (.binary .eq .flag .leftCount .rightCount),
    atom (.binary .mul .result .result .flag)])]

/-- The complete array refinement client, leaving its Boolean answer in
`result`. Input data consist only of unary scalars and finite Nat arrays. -/
def decide : Code := .seq refinement histogram

end GroupWL.MachinePrograms.IndexedWL

