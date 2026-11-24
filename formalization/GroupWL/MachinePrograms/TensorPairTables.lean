import GroupWL.MachinePrograms.EquivalenceParsing
import GroupWL.MachinePrograms.TensorCodedGroup
import GroupWL.MachinePrograms.TableWLCorrectness
import GroupWL.MachinePrograms.TensorClamp
import GroupWL.TensorVersionCaps

/-! Convert both parsed tensors to actual group tables and clamp the tuple dimension. -/
namespace GroupWL.MachinePrograms.TensorPairTables
open NatArrayLanguage
abbrev Reg := EquivalenceParsing.Reg ⊕ (TensorGroupProgram.Reg ⊕ TableWL.Reg)
abbrev Arr := EquivalenceParsing.Arr ⊕ (TensorGroupProgram.Arr ⊕ TableWL.Arr)
abbrev State := Store Reg Arr
abbrev Code := NatArrayLanguage.Program Reg Arr
set_option maxRecDepth 8192
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
instance : DecidableEq Reg := inferInstance
instance : DecidableEq Arr := inferInstance
instance : Fintype Reg := inferInstance
instance : Fintype Arr := inferInstance

def parser (r : EquivalenceParsing.Reg) : Reg := .inl r
def raw (a : EquivalenceParsing.Arr) : Arr := .inl a
def tensor (r : TensorGroupProgram.Reg) : Reg := .inr (.inl r)
def data (a : TensorGroupProgram.Arr) : Arr := .inr (.inl a)
def wl (r : TableWL.Reg) : Reg := .inr (.inr r)
def array (a : TableWL.Arr) : Arr := .inr (.inr a)

def load (p : ℕ) (second : Bool) : List (Atom Reg Arr) := [
  .const (tensor (TensorGroupProgram.l .modulus)) p,
  .copy (tensor (TensorGroupProgram.l .inputDimension))
    (parser (if second then EquivalenceParsing.r 11 else .inr 0)),
  .copy (tensor (TensorGroupProgram.l .outputDimension))
    (parser (if second then EquivalenceParsing.r 12 else .inr 1)),
  .copyArray (data (.inl .coefficients)) (raw (if second then EquivalenceParsing.output else EquivalenceParsing.saved))]

def save (second : Bool) : List (Atom Reg Arr) := [
  .copy (wl (TableWL.wl (if second then .rightCount else .leftCount))) (tensor (TensorGroupProgram.a .order)),
  .copyArray (array (TableWL.array (if second then .targets else .fanouts))) (data (.inr ()))]

def clampRegisters : Fin 7 ↪ Reg := ⟨![wl (TableWL.dimensions 0),wl (TableWL.dimensions 1),wl (TableWL.wl .arity),
  wl (TableWL.dimensions 3),wl (TableWL.dimensions 4),wl (TableWL.dimensions 5),wl (TableWL.dimensions 6)],by decide +kernel⟩
def prepareClamp : List (Atom Reg Arr) := [
  .copy (clampRegisters 0) (parser (.inr 0)),.copy (clampRegisters 1) (parser (.inr 1)),
  .copy (clampRegisters 2) (parser (EquivalenceParsing.r 2))]

def materialize (p : ℕ) [Fact p.Prime] : Code :=
  ((TensorGroupProgram.materialize ((2:ZMod p)⁻¹).val).map Sum.inl Sum.inl).map Sum.inr Sum.inr

def oneTable (p : ℕ) [Fact p.Prime] (second : Bool) : Code :=
  .seq (atoms (load p second)) (.seq (materialize p) (atoms (save second)))

def program (p : ℕ) [Fact p.Prime] : Code := .seq (oneTable p false)
  (.seq (oneTable p true) (.seq (atoms prepareClamp) (TensorClamp.program clampRegisters)))

structure Parsed (p : ℕ) [Fact p.Prime] (S : State) (T U : Statement.TensorDescription p) (k : ℕ) : Prop where
  first : EquivalenceParsing.EncodesFirst p S.left T
  second : IdentificationParsing.EncodesTensor p S.left.left U
  arity : S.scalar (parser (EquivalenceParsing.r 2))=k

theorem oneTable_runs (p : ℕ) [Fact p.Prime] (second : Bool)
    (S : State) (B : ℕ) (T : Statement.TensorDescription p) (bounded : S.Bounded B)
    (hn : S.scalar (parser (if second then EquivalenceParsing.r 11 else .inr 0))=T.inputDimension)
    (hm : S.scalar (parser (if second then EquivalenceParsing.r 12 else .inr 1))=T.outputDimension)
    (hc : S.array (raw (if second then EquivalenceParsing.output else EquivalenceParsing.saved))=
      TensorSerialization.coefficientList (T.coefficient p))
    (room : p^3+3*p≤B) (dimension : T.inputDimension+T.outputDimension≤B)
    (power : (p^(T.inputDimension+T.outputDimension))^2≤B) :
    ∃t≤TensorGroupProgram.tableCost p T.inputDimension T.outputDimension+6,∃V,
      Runs (storageBound Reg Arr B) (oneTable p second) S t V ∧ V.Bounded B ∧ V.left=S.left ∧
      V.scalar (wl (TableWL.wl (if second then .rightCount else .leftCount)))=p^(T.inputDimension+T.outputDimension) ∧
      V.array (array (TableWL.array (if second then .targets else .fanouts)))=
        GroupInitial.tableWord (TensorGroupProgram.codedMul p T) ∧
      (∀r,r≠TableWL.wl (if second then .rightCount else .leftCount) → V.right.right.scalar r=S.right.right.scalar r) ∧
      (∀a,a≠TableWL.array (if second then .targets else .fanouts) → V.right.right.array a=S.right.right.array a) := by
  have hp : p≤B := by omega
  obtain ⟨first,hA⟩ := atoms_runs bounded (load p second) (by
    simp [load,ValidAtoms,Atom.Valid,Atom.SmallResult,hp])
  let A := applyAtoms (load p second) S
  have mod : A.right.left.scalar (TensorGroupProgram.l .modulus)=p := by
    simp [A,applyAtoms,load,Atom.apply,Store.right,Store.left,Store.setScalar,Store.setArray,tensor,data,raw,parser,TensorGroupProgram.l]
  have an : A.right.left.scalar (TensorGroupProgram.l .inputDimension)=T.inputDimension := by
    simpa [A,applyAtoms,load,Atom.apply,Store.right,Store.left,Store.setScalar,Store.setArray,tensor,data,raw,parser,TensorGroupProgram.l] using hn
  have am : A.right.left.scalar (TensorGroupProgram.l .outputDimension)=T.outputDimension := by
    simpa [A,applyAtoms,load,Atom.apply,Store.right,Store.left,Store.setScalar,Store.setArray,tensor,data,raw,parser,TensorGroupProgram.l] using hm
  have ac : A.right.left.array (.inl .coefficients)=TensorSerialization.coefficientList (T.coefficient p) := by
    simpa [A,applyAtoms,load,Atom.apply,Store.right,Store.left,Store.setScalar,Store.setArray,tensor,data,raw,parser] using hc
  obtain ⟨t,ht,U,build,hU,order,out⟩ := TensorGroupProgram.materialize_tensor_runs p A.right.left B T
    hA.right.left mod an am ac room dimension power
  let C := A.left.join (U.join A.right.right)
  have build' := (build.left_bounded hA.right).right_bounded hA
  have hC : C.Bounded B := hA.left.join (hU.join hA.right.right)
  obtain ⟨last,hV⟩ := atoms_runs hC (save second) (by simp [save,ValidAtoms,Atom.Valid,Atom.SmallResult])
  let V := applyAtoms (save second) C
  refine ⟨4+(t+2),by omega,V,.seq first (.seq build' last),hV,?_,?_,?_,?_,?_⟩
  · apply Store.ext <;> intro x <;>
      simp [V,C,A,applyAtoms,save,load,Atom.apply,Store.left,Store.setScalar,Store.setArray,wl,array,tensor,data,raw,parser]
  · simpa [V,C,applyAtoms,save,Atom.apply,Store.setScalar,Store.setArray,wl,array,tensor,data] using order
  · simpa [V,C,applyAtoms,save,Atom.apply,Store.setScalar,Store.setArray,wl,array,tensor,data] using out
  · intro r hr
    simp [V,C,A,applyAtoms,save,load,Atom.apply,Store.right,Store.setScalar,Store.setArray,wl,array,tensor,data,raw,parser,hr]
  · intro a ha
    simp [V,C,A,applyAtoms,save,load,Atom.apply,Store.right,Store.setScalar,Store.setArray,wl,array,tensor,data,raw,parser,ha]


theorem program_runs (p : ℕ) [Fact p.Prime] (S : State) (B : ℕ)
    (T U : Statement.TensorDescription p) (k : ℕ) (bounded : S.Bounded B) (parsed : Parsed p S T U k)
    (room : p^3+3*p≤B) (dimensionT : T.inputDimension+T.outputDimension+10≤B)
    (dimensionU : U.inputDimension+U.outputDimension≤B)
    (powerT : (p^(T.inputDimension+T.outputDimension))^2≤B)
    (powerU : (p^(U.inputDimension+U.outputDimension))^2≤B) :
    ∃t≤TensorGroupProgram.tableCost p T.inputDimension T.outputDimension+
      TensorGroupProgram.tableCost p U.inputDimension U.outputDimension+21,∃V,
      Runs (storageBound Reg Arr B) (program p) S t V ∧ V.Bounded B ∧
      TableWL.Input (k:=min k T.wlCap) (GroupInitial.encodedMul (TensorGroupCode.groupEquiv p T))
        (GroupInitial.encodedMul (TensorGroupCode.groupEquiv p U)) B V.right.right := by
  obtain ⟨t,ht,A,first,hA,aframe,aorder,atable,_,_⟩ := oneTable_runs p false S B T bounded
    parsed.first.1 parsed.first.2.1 parsed.first.2.2 room (by omega) powerT
  have second : IdentificationParsing.EncodesTensor p A.left.left U := by
    rw [aframe]
    exact parsed.second
  obtain ⟨u,hu,C,last,hC,cframe,corder,ctable,cscalar,carray⟩ := oneTable_runs p true A B U hA
    second.1 second.2.1 second.2.2 room dimensionU powerU
  have firstData : EquivalenceParsing.EncodesFirst p C.left T := by rw [cframe,aframe];exact parsed.first
  have ck : C.scalar (parser (EquivalenceParsing.r 2))=k := by
    change C.left.scalar (EquivalenceParsing.r 2)=k
    rw [cframe,aframe]
    exact parsed.arity
  have leftOrder : C.right.right.scalar (TableWL.wl .leftCount)=p^(T.inputDimension+T.outputDimension) :=
    (cscalar _ (by decide)).trans aorder
  have leftTable : C.right.right.array (TableWL.array .fanouts)=
      GroupInitial.tableWord (TensorGroupProgram.codedMul p T) := (carray _ (by decide)).trans atable
  obtain ⟨prepare,hD⟩ := atoms_runs hC prepareClamp (by simp [prepareClamp,ValidAtoms,Atom.Valid,Atom.SmallResult])
  let D := applyAtoms prepareClamp C
  have dn : D.scalar (clampRegisters 0)=T.inputDimension := by
    simpa [D,applyAtoms,prepareClamp,Atom.apply,Store.setScalar,clampRegisters,wl,parser,Store.left] using firstData.1
  have dm : D.scalar (clampRegisters 1)=T.outputDimension := by
    simpa [D,applyAtoms,prepareClamp,Atom.apply,Store.setScalar,clampRegisters,wl,parser,Store.left] using firstData.2.1
  have dk : D.scalar (clampRegisters 2)=k := by
    simpa [D,applyAtoms,prepareClamp,Atom.apply,Store.setScalar,clampRegisters,wl,parser] using ck
  obtain ⟨v,hv,V,clamp,hV,arity⟩ := TensorClamp.program_runs clampRegisters D B T.inputDimension T.outputDimension k
    hD dn dm dk dimensionT
  have final := Runs.seq prepare clamp
  have lf : V.right.right.scalar (TableWL.wl .leftCount)=C.right.right.scalar (TableWL.wl .leftCount) :=
    final.scalar_eq_of_not_mem (wl (TableWL.wl .leftCount)) (by decide +kernel)
  have rf : V.right.right.scalar (TableWL.wl .rightCount)=C.right.right.scalar (TableWL.wl .rightCount) :=
    final.scalar_eq_of_not_mem (wl (TableWL.wl .rightCount)) (by decide +kernel)
  have la : V.right.right.array (TableWL.array .fanouts)=C.right.right.array (TableWL.array .fanouts) :=
    final.array_eq_of_not_mem (array (TableWL.array .fanouts)) (by decide +kernel)
  have ra : V.right.right.array (TableWL.array .targets)=C.right.right.array (TableWL.array .targets) :=
    final.array_eq_of_not_mem (array (TableWL.array .targets)) (by decide +kernel)
  refine ⟨t+(u+(3+v)),by omega,V,.seq first (.seq last final),hV,?_,?_,?_,?_,?_,?_⟩
  · exact hV.right.right
  · exact lf.trans leftOrder
  · exact rf.trans corder
  · exact arity
  · exact la.trans leftTable
  · exact ra.trans ctable

end GroupWL.MachinePrograms.TensorPairTables
