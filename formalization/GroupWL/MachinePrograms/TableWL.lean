import GroupWL.MachinePrograms.WordMatrixDefinitions
import GroupWL.MachinePrograms.InitialMatrixSemantics
import GroupWL.MachinePrograms.GroupTupleArrays
import GroupWL.MachinePrograms.TupleDimensions
import GroupWL.MachinePrograms.IndexedWLCost

/-! The complete table-level I/II WL program. Input consists of two group
multiplication tables, their orders, and the tuple arity. -/
namespace GroupWL.MachinePrograms.TableWL
open NatArrayLanguage
abbrev Reg := (WordMatrixPrograms.Reg ⊕ GroupTupleArrays.Reg) ⊕ TupleDimensions.Reg
abbrev Arr := (WordMatrixPrograms.Arr ⊕ GroupTupleArrays.Arr) ⊕ TupleDimensions.Arr
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr
set_option synthInstance.maxSize 4096
set_option maxRecDepth 8192

instance : DecidableEq Reg := inferInstanceAs (DecidableEq ((WordMatrixPrograms.Reg ⊕ GroupTupleArrays.Reg) ⊕ TupleDimensions.Reg))
instance : DecidableEq Arr := inferInstanceAs (DecidableEq ((WordMatrixPrograms.Arr ⊕ GroupTupleArrays.Arr) ⊕ TupleDimensions.Arr))
instance : Fintype Reg := inferInstanceAs (Fintype ((WordMatrixPrograms.Reg ⊕ GroupTupleArrays.Reg) ⊕ TupleDimensions.Reg))
instance : Fintype Arr := inferInstanceAs (Fintype ((WordMatrixPrograms.Arr ⊕ GroupTupleArrays.Arr) ⊕ TupleDimensions.Arr))

def wl (r : IndexedWL.Reg) : Reg := .inl (.inl (WordMatrixPrograms.wl r))
def array (a : IndexedWL.Arr) : Arr := .inl (.inl (WordMatrixPrograms.array a))
def dimensions (r : TupleDimensions.Reg) : Reg := .inr r
def target (r : GroupTargetBuilder.Reg) : Reg := .inl (.inr (GroupTupleArrays.target r))
def selection (r : GroupSelectionBuilder.Reg) : Reg := .inl (.inr (GroupTupleArrays.selection r))

def prepareDimensions : List (Atom Reg Arr) := [
  .copy (dimensions 0) (wl .leftCount),.copy (dimensions 1) (wl .rightCount),.copy (dimensions 2) (wl .arity)]

def prepareTables : List (Atom Reg Arr) := [
  .copy (wl .vectorLimit) (dimensions 8),.copy (wl .square) (dimensions 10),
  .copy (target (.inl 0)) (dimensions 0),.copy (target (.inr 0)) (dimensions 1),
  .copy (target (.inl 11)) (dimensions 2),.copy (target (.inl 12)) (dimensions 11),
  .copy (selection (.inl 0)) (dimensions 8),.copy (selection (.inr ())) (dimensions 9)]

def matrixProgram (word : Bool) : NatArrayLanguage.Program WordMatrixPrograms.Reg WordMatrixPrograms.Arr :=
  if word then WordMatrixPrograms.build else InitialMatrixPrograms.build.map Sum.inl Sum.inl

def prepareWL : List (Atom Reg Arr) := [
  .copy (wl .n) (dimensions 10),.copy (wl .width) (dimensions 11),
  .copyArray (array .targets) (.inl (.inr (.inl (.inl (.inr 2))))),
  .copyArray (array .fanouts) (.inl (.inr (.inl (.inr (.inr 2))))),
  .copyArray (array .leftSelection) (.inl (.inr (.inr (.inr ())))),
  .copyArray (array .rightSelection) (.inl (.inr (.inr (.inl ()))))]

def setup (word : Bool) : Code := .seq (atoms prepareDimensions)
  (.seq (TupleDimensions.program.map Sum.inr Sum.inr)
    (.seq (atoms prepareTables)
      (.seq (((matrixProgram word).map Sum.inl Sum.inl).map Sum.inl Sum.inl)
        (.seq ((GroupTupleArrays.generate.map Sum.inr Sum.inr).map Sum.inl Sum.inl)
          (atoms prepareWL)))))

def decide (word : Bool) : Code := .seq (setup word) (IndexedWL.decide.map wl array)

end GroupWL.MachinePrograms.TableWL
