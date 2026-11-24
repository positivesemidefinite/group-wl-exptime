import GroupWL.MachinePrograms.ValidatedTensorProgram
import GroupWL.MachinePrograms.DimensionProgram
import GroupWL.InputParsing

/-! Complete raw identification-input parsing as a fixed array program. -/
namespace GroupWL.MachinePrograms.IdentificationParsing
open NatArrayLanguage
open NatArrayLowering (bitNat)
open ValidatedTensorProgram (Reg Arr State Code r input output)
set_option maxRecDepth 4096

def dimensionRegs : Fin 9 ↪ Reg := (Fin.castLEEmb (by decide)).trans r

def dimension (e : Statement.DimensionEncoding) : Code := DimensionParser.program e dimensionRegs input

def initializeInput : List (Atom Reg Arr) := [.arrayLength (r 1) input,.const (r 0) 0,.const (r 3) 1]

def program (p : ℕ) (e : Statement.DimensionEncoding) : Code := .seq (atoms initializeInput)
  (.seq (ValidatedTensorProgram.program p) (.branch (r 3) (dimension e) .skip))

def EncodesTensor (p : ℕ) [Fact p.Prime] (S : State) (T : Statement.TensorDescription p) : Prop :=
  S.scalar (r 11)=T.inputDimension ∧ S.scalar (r 12)=T.outputDimension ∧
    S.array output=TensorSerialization.coefficientList (T.coefficient p)

theorem dimension_tensor_frame (p : ℕ) [Fact p.Prime] {S T : State}
    {e : Statement.DimensionEncoding} {B t : ℕ} (run : Runs B (dimension e) S t T)
    (tensor : Statement.TensorDescription p) (enc : EncodesTensor p S tensor) : EncodesTensor p T tensor := by
  have scalar : ∀ (i : Fin 13), 9 ≤ i.val → T.scalar (r i)=S.scalar (r i) := by
    intro i hi
    apply run.scalar_eq_of_not_mem
    cases e <;>
      simp [dimension,DimensionParser.program,DimensionParser.firstBit,DimensionParser.suffixLoop,
        DimensionParser.bitStep,atoms,NatArrayLanguage.sequence,Program.scalarWrites,Atom.scalarWrites,
        dimensionRegs,Function.Embedding.trans_apply,r.injective.eq_iff]
      <;> (repeat' constructor) <;> intro h <;> subst i <;> norm_num at hi
  have array : T.array output=S.array output := by
    apply run.array_eq_of_not_mem
    cases e <;>
      simp [dimension,DimensionParser.program,DimensionParser.firstBit,DimensionParser.suffixLoop,
        DimensionParser.bitStep,atoms,NatArrayLanguage.sequence,Program.arrayWrites,Atom.arrayWrites]
  exact ⟨(scalar 11 (by decide)).trans enc.1,(scalar 12 (by decide)).trans enc.2.1,array.trans enc.2.2⟩

theorem initializeInput_runs (S : State) (w : List Bool) (M : ℕ) (bounded : S.Bounded M)
    (room : 1≤M) (inputEq : S.array input=w.map bitNat) :
    Runs (storageBound Reg Arr M) (atoms initializeInput) S 3 (applyAtoms initializeInput S) ∧
      (applyAtoms initializeInput S).Bounded M ∧
      (applyAtoms initializeInput S).scalar (r 0)=0 ∧
      (applyAtoms initializeInput S).scalar (r 1)=w.length ∧
      (applyAtoms initializeInput S).scalar (r 3)=1 ∧
      (applyAtoms initializeInput S).array input=w.map bitNat := by
  obtain ⟨run,hT⟩ := atoms_runs bounded initializeInput
    (by simp [initializeInput,ValidAtoms,Atom.Valid,Atom.SmallResult,room])
  exact ⟨run,hT,by simp [initializeInput,applyAtoms,Atom.apply,Store.setScalar,r],
    by simp [initializeInput,applyAtoms,Atom.apply,Store.setScalar,r,inputEq],
    by simp [initializeInput,applyAtoms,Atom.apply,Store.setScalar,r],inputEq⟩

def parseCost (p N : ℕ) : ℕ := ValidatedTensorProgram.scanCost p N+6*N+16

theorem program_runs (p : ℕ) [Fact p.Prime] (e : Statement.DimensionEncoding)
    (S : State) (w : List Bool) (M : ℕ) (bounded : S.Bounded M)
    (room : (w.length+1)^3≤M) (fieldRoom : p^3+p≤M)
    (powerRoom : p^w.length≤M) (binaryRoom : 2^(w.length+1)≤M)
    (inputEq : S.array input=w.map bitNat) :
    ∃T t,t≤parseCost p w.length ∧ Runs (storageBound Reg Arr M) (program p e) S t T ∧
      T.Bounded M ∧ T.scalar (r 3)≤1 ∧ T.array input=w.map bitNat ∧
      match Statement.readIdentification p e w with
      | none => T.scalar (r 3)=0
      | some (tensor,k) => T.scalar (r 3)=1 ∧ T.scalar (r 2)=k ∧ EncodesTensor p T tensor := by
  have hp : 0<p := (Fact.out : p.Prime).pos
  have h2 : 2≤M := (pow_le_pow_right' (by decide : 1≤2) (by omega : 1≤w.length+1)).trans binaryRoom
  obtain ⟨initRun,hV,vpos,vlen,vvalid,vinput⟩ := initializeInput_runs S w M bounded (by omega) inputEq
  let V := applyAtoms initializeInput S
  obtain ⟨U,u,hu,scan,hU,upos,ulen,uvalid,uinput,spec⟩ :=
    ValidatedTensorProgram.program_runs p V w 0 M hV room fieldRoom powerRoom vpos (by omega) vlen vvalid vinput
  simp only [List.drop_zero] at spec
  cases parsed : Statement.readTensor p w with
  | none =>
    have uz : U.scalar (r 3)=0 := by simpa only [parsed] using spec
    refine ⟨U,3+(u+1),by unfold parseCost;omega,
      .seq initRun (.seq scan (.branch_zero uz (.skip (Store.size_le_of_bounded hU)))),hU,uvalid,uinput,?_⟩
    simpa [Statement.readIdentification,parsed] using uz
  | some val =>
    rcases val with ⟨tensor,tail⟩
    have hs : U.scalar (r 3)=1 ∧ U.scalar (r 11)=tensor.inputDimension ∧
        U.scalar (r 12)=tensor.outputDimension ∧
        U.array output=TensorSerialization.coefficientList (tensor.coefficient p) ∧
        w.drop (U.scalar (r 0))=tail := by simpa only [parsed] using spec
    obtain ⟨T,t,ht,last,hT,tpos,tlen,tvalid,tinput,dims⟩ := DimensionParser.program_runs e dimensionRegs input U w
      (U.scalar (r 0)) M hU h2 rfl ulen uinput upos binaryRoom
    have dimRun : Runs (storageBound Reg Arr M) (dimension e) U t T := last
    change T.scalar (r 3)≤1 at tvalid
    change Statement.readDimension e (w.drop (U.scalar (r 0)))=
      if T.scalar (r 3)=0 then none else some (T.scalar (r 2)) at dims
    rw [hs.2.2.2.2] at dims
    have enc : EncodesTensor p T tensor := dimension_tensor_frame p dimRun tensor
      ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1⟩
    refine ⟨T,3+(u+(t+1)),by unfold parseCost;omega,
      .seq initRun (.seq scan (.branch_nonzero (by omega) dimRun)),hT,tvalid,tinput,?_⟩
    by_cases hz : T.scalar (r 3)=0
    · simp [Statement.readIdentification,parsed,dims,hz]
    · have hone : T.scalar (r 3)=1 := by omega
      simpa [Statement.readIdentification,parsed,dims,hz] using And.intro hone enc

end GroupWL.MachinePrograms.IdentificationParsing
