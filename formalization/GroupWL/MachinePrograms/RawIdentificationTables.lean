import GroupWL.MachinePrograms.IdentificationTableClient
import GroupWL.MachinePrograms.IdentificationParsing
import GroupWL.MachinePrograms.TensorGroupInterface
import GroupWL.MachinePrograms.TensorPairTables

/-! Concrete single-tensor frontend for the complete table identification client. -/
namespace GroupWL.MachinePrograms.RawIdentificationTables
open NatArrayLanguage
set_option maxHeartbeats 2000000
set_option maxRecDepth 16000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
abbrev Reg := ValidatedTensorProgram.Reg ⊕ (TensorGroupProgram.Reg ⊕ IdentificationTableClient.Reg)
abbrev Arr := ValidatedTensorProgram.Arr ⊕ (TensorGroupProgram.Arr ⊕ IdentificationTableClient.Arr)
abbrev State := Store Reg Arr
abbrev Code := NatArrayLanguage.Program Reg Arr
instance : DecidableEq Reg := inferInstance
instance : DecidableEq Arr := inferInstance
instance : Fintype Reg := inferInstance
instance : Fintype Arr := inferInstance

def parser (r : Fin 13) : Reg := .inl (ValidatedTensorProgram.r r)
def tensor (r : TensorGroupProgram.Reg) : Reg := .inr (.inl r)
def client (r : IdentificationTableClient.Reg) : Reg := .inr (.inr r)
def source (r : IdentificationCandidate.InputReg) : Reg := client (IdentificationTableClient.source r)
def sourceArray (a : IdentificationCandidate.InputArr) : Arr := .inr (.inr (IdentificationTableClient.sourceArray a))
def result : Reg := client IdentificationTableClient.result

def prepare (p : ℕ) : List (Atom Reg Arr) := [
  .const (tensor (TensorGroupProgram.l .modulus)) p,
  .copy (tensor (TensorGroupProgram.l .inputDimension)) (parser 11),
  .copy (tensor (TensorGroupProgram.l .outputDimension)) (parser 12),
  .copyArray (.inr (.inl (.inl .coefficients))) (.inl ValidatedTensorProgram.output),
  .binary .add (source .dimension) (parser 11) (parser 12),
  .copy (source .arity) (parser 2)]
def clampRegs : Fin 7 ↪ Reg :=
  ⟨![tensor (TensorGroupProgram.l .inputDimension),tensor (TensorGroupProgram.l .outputDimension),source .arity,
    tensor (TensorGroupProgram.a .half),tensor (TensorGroupProgram.a .dimension),
    tensor (TensorGroupProgram.a .order),tensor (TensorGroupProgram.a .flag)],by decide⟩
def finish : List (Atom Reg Arr) := [
  .copy (source .order) (tensor (TensorGroupProgram.a .order)),
  .copyArray (sourceArray .table) (.inr (.inl (.inr ())))]
def tables (p : ℕ) [Fact p.Prime] : Code := .seq (atoms (prepare p))
  (.seq (TensorClamp.program clampRegs)
    (.seq ((TensorGroupProgram.materialize ((2:ZMod p)⁻¹).val).map Sum.inl Sum.inl |>.map Sum.inr Sum.inr)
      (atoms finish)))
def program (p : ℕ) [Fact p.Prime] (word : Bool) : Code := .seq (tables p)
  ((IdentificationTableClient.identify p word).map Sum.inr Sum.inr |>.map Sum.inr Sum.inr)

theorem tables_runs (p : ℕ) [Fact p.Prime] (S : State) (B : ℕ) (T : Statement.TensorDescription p) (k : ℕ)
    (hb : S.Bounded B) (enc : IdentificationParsing.EncodesTensor p S.left T)
    (hk : S.scalar (parser 2)=k) (field : p^3+3*p≤B)
    (cap : T.inputDimension+T.outputDimension+10≤B)
    (power : (p^(T.inputDimension+T.outputDimension))^2≤B) :
    ∃t≤TensorGroupProgram.tableCost p T.inputDimension T.outputDimension+14,∃U,
      Runs (storageBound Reg Arr B) (tables p) S t U ∧ U.Bounded B ∧
      U.scalar (source .dimension)=T.inputDimension+T.outputDimension ∧
      U.scalar (source .order)=p^(T.inputDimension+T.outputDimension) ∧
      U.scalar (source .arity)=min k T.wlCap ∧
      U.array (sourceArray .table)=GroupInitial.tableWord (TensorGroupProgram.codedMul p T) := by
  have hp : p≤B := by omega
  obtain ⟨prep,hA⟩ := atoms_runs hb (prepare p)
    (by
      simp [prepare,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar,parser,tensor,source,client,hp]
      change S.left.scalar (ValidatedTensorProgram.r 11)+S.left.scalar (ValidatedTensorProgram.r 12)≤B
      rw [enc.1,enc.2.1];omega)
  let A := applyAtoms (prepare p) S
  have fields : A.scalar (tensor (TensorGroupProgram.l .modulus))=p ∧
      A.scalar (tensor (TensorGroupProgram.l .inputDimension))=T.inputDimension ∧
      A.scalar (tensor (TensorGroupProgram.l .outputDimension))=T.outputDimension ∧
      A.array (.inr (.inl (.inl .coefficients)))=TensorSerialization.coefficientList (T.coefficient p) ∧
      A.scalar (source .dimension)=T.inputDimension+T.outputDimension ∧ A.scalar (source .arity)=k := by
    simp [A,applyAtoms,prepare,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,tensor,source,client,parser,
      TensorGroupProgram.l,IdentificationTableClient.source]
    exact ⟨enc.1,enc.2.1,enc.2.2,congrArg₂ (·+·) enc.1 enc.2.1,hk⟩
  obtain ⟨u,hu,C,clamp,hC,arity⟩ := TensorClamp.program_runs clampRegs A B T.inputDimension T.outputDimension k hA
    fields.2.1 fields.2.2.1 fields.2.2.2.2.2 cap
  have preserve (r : Reg) (hr : r∉(TensorClamp.program clampRegs : Code).scalarWrites) : C.scalar r=A.scalar r :=
    clamp.scalar_eq_of_not_mem r hr
  have cp : C.right.left.scalar (TensorGroupProgram.l .modulus)=p :=
    (preserve _ (by decide)).trans fields.1
  have cn : C.right.left.scalar (TensorGroupProgram.l .inputDimension)=T.inputDimension :=
    (preserve _ (by decide)).trans fields.2.1
  have cm : C.right.left.scalar (TensorGroupProgram.l .outputDimension)=T.outputDimension :=
    (preserve _ (by decide)).trans fields.2.2.1
  have cc : C.right.left.array (.inl .coefficients)=TensorSerialization.coefficientList (T.coefficient p) :=
    (clamp.array_eq_of_not_mem _ (by decide)).trans fields.2.2.2.1
  have cd : C.scalar (source .dimension)=T.inputDimension+T.outputDimension :=
    (preserve _ (by decide)).trans fields.2.2.2.2.1
  obtain ⟨v,hv,V,materialize,hV,order,table⟩ := TensorGroupProgram.materialize_tensor_runs p C.right.left B T hC.right.left
    cp cn cm cc field (by omega) power
  let W := C.left.join (V.join C.right.right)
  have hW : W.Bounded B := hC.left.join (hV.join hC.right.right)
  obtain ⟨last,hU⟩ := atoms_runs hW finish
    (by simp [finish,ValidAtoms,Atom.Valid,Atom.SmallResult])
  let U := applyAtoms finish W
  refine ⟨6+(u+(v+2)),by omega,U,.seq prep (.seq clamp (.seq ((materialize.left_bounded hC.right).right_bounded hC) last)),hU,?_,?_,?_,?_⟩
  · simpa [U,W,applyAtoms,finish,Atom.apply,Store.setScalar,Store.setArray,source,client,sourceArray,IdentificationTableClient.source] using cd
  · simpa [U,W,applyAtoms,finish,Atom.apply,Store.setScalar,Store.setArray,source,client,sourceArray,tensor,IdentificationTableClient.source] using order
  · simpa [U,W,applyAtoms,finish,Atom.apply,Store.setScalar,Store.setArray,source,client,sourceArray,clampRegs,IdentificationTableClient.source,Statement.TensorDescription.wlCap] using arity
  · simpa [U,W,applyAtoms,finish,Atom.apply,Store.setScalar,Store.setArray,sourceArray] using table

theorem program_runs (p : ℕ) [Fact p.Prime] [NeZero (2:ZMod p)] (word : Bool) (S : State) (B : ℕ)
    (T : Statement.TensorDescription p) (k : ℕ) (hkpos : k≠0)
    (hb : S.Bounded B) (enc : IdentificationParsing.EncodesTensor p S.left T)
    (hk : S.scalar (parser 2)=k) (field : p^3+3*p≤B)
    (cap : T.inputDimension+T.outputDimension+10≤B)
    (hroom : ((p^(T.inputDimension+T.outputDimension))*(p^(T.inputDimension+T.outputDimension)))*
      ((p^(T.inputDimension+T.outputDimension))*(p^(T.inputDimension+T.outputDimension)))≤B)
    (hpow : (p^(T.inputDimension+T.outputDimension))^(T.inputDimension+T.outputDimension)≤B)
    (hcube : (T.inputDimension+T.outputDimension)^3≤B)
    (hcount : p^((T.inputDimension+T.outputDimension)^3)≤B)
    (matrixRoom : InitialMatrixPrograms.Room (p^(T.inputDimension+T.outputDimension))
      (p^(T.inputDimension+T.outputDimension)) (min k T.wlCap) B)
    (room : IndexedWL.Room ((p^(T.inputDimension+T.outputDimension))^(min k T.wlCap)+
      (p^(T.inputDimension+T.outputDimension))^(min k T.wlCap)) (min k T.wlCap)
      (p^(T.inputDimension+T.outputDimension)) B) :
    ∃t≤TensorGroupProgram.tableCost p T.inputDimension T.outputDimension+14+
      IdentificationTableClient.cost p (T.inputDimension+T.outputDimension) B,∃U,
      Runs (storageBound Reg Arr B) (program p word) S t U ∧ U.Bounded B ∧
      U.scalar result≤1 ∧
      (U.scalar result=1 ↔ Refinement.Identifies (IdentificationTest.version word) k T.Carrier) := by
  have power : (p^(T.inputDimension+T.outputDimension))^2≤B := by
    simpa only [pow_two] using (Nat.le_mul_self _).trans hroom
  obtain ⟨t,ht,A,tablesRun,hA,dimension,order,arity,table⟩ := tables_runs p S B T k hb enc hk field cap power
  have positive : min k T.wlCap≠0 := by unfold Statement.TensorDescription.wlCap;omega
  obtain ⟨u,hu,V,identifyRun,hV,bit,out⟩ := IdentificationTableClient.identify_runs word
    (TensorGroupCode.groupEquiv p T) (TensorGroupProgram.codedEquiv_one_val p T) positive
    A.right.right hA.right.right dimension order arity table hroom hpow (by omega) hcube hcount matrixRoom room
  let U := A.left.join (A.right.left.join V)
  have run := (identifyRun.right_bounded hA.right).right_bounded hA
  refine ⟨t+u,by omega,U,.seq tablesRun run,hA.left.join (hA.right.left.join hV),bit,?_⟩
  exact out.trans (Statement.identification_clamp T (IdentificationTest.version word) k).symm

end GroupWL.MachinePrograms.RawIdentificationTables
