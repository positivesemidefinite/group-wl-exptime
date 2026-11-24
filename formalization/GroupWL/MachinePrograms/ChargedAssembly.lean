import GroupWL.MachinePrograms.ChargedWriterCorrectness
import GroupWL.MachinePrograms.KernelToTensor

/-! The Gaussian kernel and the circuit charge vector are used by both tensor assemblers. -/
set_option synthInstance.maxSize 65536
set_option maxRecDepth 16384
namespace GroupWL.MachinePrograms.ChargedAssembly
open NatArrayLanguage NatArrayExpressions IncidenceTensor ConstructiveCoordinates ConstructiveIncidence
open ChargedWriter

abbrev R₀ := KernelProgram.Reg ⊕ ChargedWriter.Registers
abbrev A₀ := KernelProgram.Arr ⊕ ChargedWriter.Arr
abbrev R₂ := EvaluationAssembly.Reg ⊕ EvaluationAssembly.Reg
abbrev A₂ := EvaluationAssembly.Arr ⊕ EvaluationAssembly.Arr
abbrev Reg := R₀ ⊕ R₂
abbrev Arr := A₀ ⊕ A₂
abbrev State := Store Reg Arr
abbrev wreg (r : Parameter) : ChargedWriter.Registers := .inl (.inr r)
abbrev countReg : ChargedWriter.Registers := .inl (.inl 0)
abbrev twoReg : ChargedWriter.Registers := .inl (.inl 4)

def prep : List (Atom ChargedWriter.Registers ChargedWriter.Arr) := [
  .const twoReg 2, .binary .mul (wreg .inputStride) (wreg .inputStride) twoReg,
  .binary .mul (wreg .outputStride) (wreg .outputStride) twoReg,
  .arrayLength (wreg .rows) (.inl ()),
  .binary .mul countReg (wreg .inputDim) (wreg .inputDim),
  .binary .mul countReg countReg (wreg .outputDim)]

def settings (X Z q c p k rows : ℕ) : Parameter → ℕ
  | .inputDim => X | .outputDim => Z | .inputStride => q*2 | .outputStride => c*2
  | .modulus => p | .rows => rows | .dimension => k

structure Input (W : ChargedWriter.State) (X Z q c p k : ℕ) (charges : List ℕ) : Prop where
  x : W.scalar (wreg .inputDim)=X
  z : W.scalar (wreg .outputDim)=Z
  q : W.scalar (wreg .inputStride)=q
  c : W.scalar (wreg .outputStride)=c
  p : W.scalar (wreg .modulus)=p
  k : W.scalar (wreg .dimension)=k
  charges : W.array (.inl ())=charges

def sourceProgram : NatArrayLanguage.Program R₀ A₀ :=
  ((.seq (atoms prep) ChargedWriter.program : NatArrayLanguage.Program ChargedWriter.Registers ChargedWriter.Arr).map Sum.inr Sum.inr)

theorem prep_runs (W : ChargedWriter.State) (X Z q c p k M : ℕ) (charges : List ℕ)
    (hw : W.Bounded M) (hi : Input W X Z q c p k charges)
    (hm : 2≤M) (hq : q*2≤M) (hc : c*2≤M) (hs : X*X≤M) (hn : X*X*Z≤M) :
    let U := applyAtoms prep W
    Runs (storageBound ChargedWriter.Registers ChargedWriter.Arr M) (atoms prep) W 6 U ∧ U.Bounded M ∧
    Frame (settings X Z q c p k charges.length) charges (inputs U) ∧ U.scalar countReg=X*X*Z := by
  have valid : ValidAtoms M prep W := by
    simp [prep,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar,
      wreg,twoReg,countReg,hi.x,hi.z,hi.q,hi.c,hm,hq,hc,hs,hn]
  obtain ⟨run,bounded⟩ := atoms_runs hw prep valid
  refine ⟨run,bounded,⟨?_,?_⟩,?_⟩
  · intro r
    cases r <;> simp [prep,applyAtoms,Atom.apply,BinaryOp.eval,inputs,Store.setScalar,settings,
      wreg,twoReg,countReg,hi.x,hi.z,hi.q,hi.c,hi.p,hi.k,hi.charges]
  · exact hi.charges
  · simp [prep,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,hi.x,hi.z,wreg,twoReg,countReg]

def scalarPort (r : EvaluationAssembly.Reg) : Ports.Scalar R₀ A₀ :=
  match r with
  | .xdim => .scalar (.inr (wreg .inputDim))
  | .zdim => .scalar (.inr (wreg .outputDim))
  | .modulus => .scalar (.inl (KernelProgram.wr .modulus))
  | .ydim => .scalar (.inl (KernelProgram.wr .width))
  | _ => .literal 0

def scalarPorts : R₂ → Ports.Scalar R₀ A₀ := Sum.elim scalarPort scalarPort
def arrayPorts : A₂ → Option A₀
  | .inl .operators | .inr .operators => some (.inl (KernelProgram.wa .lift))
  | .inr .twist => some (.inr (.inr ()))
  | _ => none

def assemblers : NatArrayLanguage.Program R₂ A₂ :=
  .seq ((.seq (atoms ReuseKernel.zeroPrep) EvaluationAssembly.program :
    EvaluationAssembly.Code).map Sum.inl Sum.inl) (EvaluationAssembly.program.map Sum.inr Sum.inr)
noncomputable def program : NatArrayLanguage.Program Reg Arr := Ports.thenRun sourceProgram scalarPorts arrayPorts assemblers

structure Output {p : ℕ} [Fact p.Prime] (S : State) (T U : Statement.TensorDescription p) (k : ℕ) : Prop where
  x : S.right.left.scalar .inputdim=T.inputDimension
  z : S.right.left.scalar .zdim=T.outputDimension
  coefficients : S.right.left.array .output=TensorSerialization.coefficientList (T.coefficient p)
  x' : S.right.right.scalar .inputdim=U.inputDimension
  z' : S.right.right.scalar .zdim=U.outputDimension
  coefficients' : S.right.right.array .output=TensorSerialization.coefficientList (U.coefficient p)
  dimension : S.left.right.scalar (wreg .dimension)=k

def cost (n N : ℕ) : ℕ := 6+n*(expr.cost+4)+6+
  (Fintype.card R₂+Fintype.card A₂)+38*N+22

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [FiniteCode I] [FiniteCode J] (p : ℕ) [Fact p.Prime]
variable {V : J → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module (ZMod p) (V j)]
variable (A : AffineSystem (ZMod p) I J V)
  (R : ∀ j, Coordinates (ZMod p) (ReadoutRadical A j)) (q : ℕ)
local notation "X" => FiniteCode.size (InputIndex A R q)
local notation "Z" => FiniteCode.size (OutputIndex A R q)
local notation "H" => ConstructiveTensor.operatorCoordinates A R q
local notation "Y" => ConstructiveTensor.obstructionMap A R q
local notation "C" => FiniteCode.size (Pair q)
local notation "desc" => ConstructiveTensor.description q p A R

theorem program_runs_square (hq : 0<q) (h₂ : 2≤q) (β : I → ZMod p) (k : ℕ)
    (K : KernelProgram.State) (W : ChargedWriter.State) (E : Store R₂ A₂)
    (ready : KernelProgram.Represents p (X*Z) 0 (wedgeWord p A R q hq)
      (KernelProgramCorrectness.encode (GeneratedCoordinateEntries.operatorChart
        (chosenCoordinates A R q hq) (Y hq))) K)
    (hi : Input W X Z q C p k (chargeWord p β)) (B M : ℕ)
    (hb : 2+X+Z+q*2+C*2+p+k+FiniteCode.size I+X*X+X*X*Z≤B)
    (budget : B*B+2≤M) (bM : B≤M)
    (hK : K.Bounded M) (hW : W.Bounded M) (hE : E.Bounded M)
    (hsize : (X+(H hq).dimension)+(X+(H hq).dimension)*(X+(H hq).dimension)+
      (X+(H hq).dimension)*(X+(H hq).dimension)*Z≤M) :
    ∃t≤cost (X*X*Z) ((X+(H hq).dimension)*(X+(H hq).dimension)*Z),∃S,
      Runs (storageBound Reg Arr M) program ((K.join W).join E) t S ∧ S.Bounded M ∧
      Output S (desc hq AlternatingBilinearMap.zero) (desc hq (epsilonCharge A q h₂ β)) k := by
  let d := settings X Z q C p k (chargeWord p β).length
  have hm (r : Parameter) : d r≤B := by
    cases r <;> simp only [d,settings,chargeWord_length] <;> omega
  have vals : ∀v∈chargeWord p β,v≤B := by
    intro v hv
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hv
    have hp := ZMod.val_lt (β (FiniteCode.equiv.symm i))
    omega
  obtain ⟨rp,bp,frame,cnt⟩ := prep_runs W X Z q C p k M _ hW hi (by omega) (by omega)
    (by omega) (by omega) (by omega)
  obtain ⟨t,ht,U,run,bU,hU,hlist⟩ := ChargedWriter.program_runs_square d (chargeWord p β)
    (applyAtoms prep W) B M (X*X*Z) (by omega) (by omega) hm vals rfl budget bp frame cnt
  have twist : U.array (.inr ())=ConstructiveTensorAssembly.twistEntries p A R q (epsilonCharge A q h₂ β) :=
    hlist.trans (positions_eq_twist p A R q h₂ β)
  let P := K.join U
  have src := (rp.seq run).right_bounded (hK.join hW)
  have targetB := (Ports.code_runs scalarPorts arrayPorts P E M ((hK.join bU).join hE) (by
    intro r n hl
    cases r with
    | inl r => cases r <;> simp [scalarPorts,scalarPort] at hl <;> omega
    | inr r => cases r <;> simp [scalarPorts,scalarPort] at hl <;> omega)).2
  let T := Ports.target scalarPorts arrayPorts P
  have hx : U.scalar (wreg .inputDim)=X := hU.scalar .inputDim
  have hz : U.scalar (wreg .outputDim)=Z := hU.scalar .outputDim
  obtain ⟨a,ha,F,rF,bF,xF,zF,cF⟩ := ReuseKernel.baseFromKernel p A R q hq K ready T.left M targetB.left
    hx hz rfl ready.modulus rfl hsize
  have op : T.right.array .operators=ConstructiveTensorAssembly.operatorEntries p A R q hq := by
    change K.array (KernelProgram.wa .lift)=_
    rw [ready.lift,ReuseKernel.operatorArray]; rfl
  obtain ⟨b,hb',G,rG,bG,xG,zG,cG⟩ := ConstructiveTensorAssembly.program_runs p A R q hq
    (epsilonCharge A q h₂ β) T.right M targetB.right hx ready.width hz ready.modulus op twist hsize
  have middle := (rF.left_bounded targetB).seq (rG.right_bounded (S:=F.join T.right) (bF.join targetB.right))
  have small : ∀r n,scalarPorts r = .literal n → n≤M := by
    intro r n hl
    cases r with
    | inl r => cases r <;> simp [scalarPorts,scalarPort] at hl <;> omega
    | inr r => cases r <;> simp [scalarPorts,scalarPort] at hl <;> omega
  have all := Ports.thenRun_runs sourceProgram scalarPorts arrayPorts assemblers (K.join W)
    P E (F.join G) M (6+t) (a+b) (hK.join hW) (hK.join bU) hE small src middle
  refine ⟨_,?_,_,all,(hK.join bU).join (bF.join bG),⟨xF,zF,cF,xG,zG,cG,hU.scalar .dimension⟩⟩
  change b≤19*((X+(H hq).dimension)*(X+(H hq).dimension)*Z)+9 at hb'
  unfold cost
  omega

theorem program_runs (hq : 0<q) (h₂ : 2≤q) (β : I → ZMod p) (k : ℕ)
    (K : KernelProgram.State) (W : ChargedWriter.State) (E : Store R₂ A₂)
    (ready : KernelProgram.Represents p (X*Z) 0 (wedgeWord p A R q hq)
      (KernelProgramCorrectness.encode (GeneratedCoordinateEntries.operatorChart
        (chosenCoordinates A R q hq) (Y hq))) K)
    (hi : Input W X Z q C p k (chargeWord p β)) (B M : ℕ)
    (hb : 2+X+Z+q*2+C*2+p+k+FiniteCode.size I+X*X+X*X*Z≤B)
    (budget : (B+2)^(2*(term.expression sizeReg).cost)≤M) (bM : B≤M)
    (hK : K.Bounded M) (hW : W.Bounded M) (hE : E.Bounded M)
    (hsize : (X+(H hq).dimension)+(X+(H hq).dimension)*(X+(H hq).dimension)+
      (X+(H hq).dimension)*(X+(H hq).dimension)*Z≤M) :
    ∃t≤cost (X*X*Z) ((X+(H hq).dimension)*(X+(H hq).dimension)*Z),∃S,
      Runs (storageBound Reg Arr M) program ((K.join W).join E) t S ∧ S.Bounded M ∧
      Output S (desc hq AlternatingBilinearMap.zero) (desc hq (epsilonCharge A q h₂ β)) k := by
  have exponent : 2≤2*(term.expression sizeReg).cost := by decide
  have b : (B+2)^2≤M := (Nat.pow_le_pow_right (by omega) exponent).trans budget
  exact program_runs_square p A R q hq h₂ β k K W E ready hi B M hb (by nlinarith) bM hK hW hE hsize

end GroupWL.MachinePrograms.ChargedAssembly
