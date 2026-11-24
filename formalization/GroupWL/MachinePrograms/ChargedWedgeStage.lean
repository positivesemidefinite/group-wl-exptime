import GroupWL.MachinePrograms.IncidencePipelineRecords
import GroupWL.WedgeOperatorClient
import GroupWL.FormMatrixComposition

/-! Compute the chosen form values and both padded dimensions, then run the global Gaussian kernel. -/
namespace GroupWL.MachinePrograms.ChargedWedgeStage
open NatArrayLanguage ConstructiveIncidence IncidenceTensor ConstructiveCoordinates
set_option synthInstance.maxSize 65536
set_option maxRecDepth 16384

inductive Header where
  | oldInput | chosenWidth | modulus | oldOutput | xdim | zdim | formLength | nForms | divisor | rem | zero | total
  deriving DecidableEq, Fintype
inductive Field where | u0 | v0 | u1 | v1 | second | forms | lift deriving DecidableEq, Fintype
abbrev Base := Store Header Field
abbrev MR := Header ⊕ MatrixArithmetic.Reg
abbrev MA := Field ⊕ MatrixArithmetic.Arr
abbrev Reg := MR ⊕ WedgeKernel.Reg
abbrev Arr := MA ⊕ WedgeKernel.Arr
abbrev State := Store Reg Arr

def prep : List (Atom Header Field) := [
  .arrayLength .oldOutput .u0, .binary .add .xdim .oldInput .oldOutput,
  .binary .add .zdim .oldOutput .xdim, .arrayLength .formLength .forms, .const .zero 0,
  .binary .eq .divisor .oldInput .zero, .binary .add .divisor .oldInput .divisor,
  .divmod .nForms .rem .formLength .divisor,
  .binary .mul .total .xdim .zdim, .binary .mul .total .chosenWidth .total]

def matScalar : MatrixArithmetic.Reg → Ports.Scalar Header Field
  | .rows => .scalar .nForms | .inner => .scalar .oldInput | .cols => .scalar .chosenWidth
  | .modulus => .scalar .modulus | _ => .literal 0
def matArray : MatrixArithmetic.Arr → Option Field
  | .left => some .forms | .right => some .lift | _ => none

def wedgeReg : WedgeConstraints.Reg → Option Header
  | .total => some .total | .modulus => some .modulus | .input => some .xdim | .output => some .zdim
  | .oldInput => some .oldInput | .oldOutput => some .oldOutput | .width => some .chosenWidth | _ => none
def wedgeScalar : WedgeKernel.Reg → Ports.Scalar MR MA
  | .inl (.inl r) => match wedgeReg r with
    | some k => .scalar (.inl k)
    | none => .literal 0
  | _ => .literal 0
def wedgeArray : WedgeKernel.Arr → Option MA
  | .inl .u0 => some (.inl .u0) | .inl .v0 => some (.inl .v0)
  | .inl .u1 => some (.inl .u1) | .inl .v1 => some (.inl .v1)
  | .inl .second => some (.inl .second) | .inl .forms => some (.inl .forms)
  | .inl .chosen => some (.inr .output) | _ => none

noncomputable def multiply : NatArrayLanguage.Program MR MA := Ports.thenRun (atoms prep) matScalar matArray MatrixArithmetic.multiply
noncomputable def program (p : ℕ) : NatArrayLanguage.Program Reg Arr :=
  Ports.thenRun multiply wedgeScalar wedgeArray (WedgeKernel.program p)

def time (p n f w x z : ℕ) := 10+(Fintype.card MatrixArithmetic.Reg+Fintype.card MatrixArithmetic.Arr+
  (f*w*(12*n+9)+7))+(Fintype.card WedgeKernel.Reg+Fintype.card WedgeKernel.Arr+
    (w*x*z*(WedgeConstraints.expression.cost+4)+10+220*(w+x*z+p+1)^4))

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [FiniteCode I] [FiniteCode J] (p : ℕ) [Fact p.Prime]
variable {V : J → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module (ZMod p) (V j)]
variable (A : AffineSystem (ZMod p) I J V)
  (R : ∀ j, Coordinates (ZMod p) (ReadoutRadical A j)) (q : ℕ)
local notation "X" => FiniteCode.size (InputIndex A R q)
local notation "Z" => FiniteCode.size (OutputIndex A R q)
local notation "N" => FiniteCode.size (OldInputIndex A R q)
local notation "O" => FiniteCode.size (OldOutputIndex A R q)
local notation "F" => FiniteCode.size (FormIndex A R q)
local notation "Width" => (chosenCoordinates A R q)
local notation "D" => wedgeDescriptors p A R q

structure Input (hq : 0<q) (S : Base) : Prop where
  oldInput : S.scalar .oldInput=N
  width : S.scalar .chosenWidth=(Width hq).dimension
  modulus : S.scalar .modulus=p
  u0 : S.array .u0=(D).u0
  v0 : S.array .v0=(D).v0
  u1 : S.array .u1=(D).u1
  v1 : S.array .v1=(D).v1
  second : S.array .second=(D).second
  forms : S.array .forms=formMatrix p A R q
  lift : S.array .lift=MatrixEncoding.word (CachedElimination.ofLinear (chosenChart A R q hq).lift)

structure Prepared (hq : 0<q) (S : Base) : Prop extends Input p A R q hq S where
  oldOutput : S.scalar .oldOutput=O
  xdim : S.scalar .xdim=X
  zdim : S.scalar .zdim=Z
  formCount : S.scalar .nForms=F
  length : S.scalar .total=(Width hq).dimension*X*Z

structure Room (hq : 0<q) (M : ℕ) : Prop where
  field : p*p+2*p≤M
  zdim : Z≤M
  ambient : X*Z≤M
  square : (X*Z)^2≤M
  chosen : F*(Width hq).dimension≤M
  entries : (Width hq).dimension*X*Z≤M

structure Output (hq : 0<q) (T : State) : Prop where
  xdim : T.left.left.scalar .xdim=X
  zdim : T.left.left.scalar .zdim=Z
  gram : KernelProgram.Represents p (X*Z) 0 (wedgeWord p A R q hq)
    (KernelProgramCorrectness.encode (GeneratedCoordinateEntries.operatorChart (chosenCoordinates A R q hq)
      (ConstructiveTensor.obstructionMap A R q hq))) T.right.right

omit [Fintype J] [DecidableEq I] in
private theorem noForms (h : N=0) : F=0 := by
  by_contra ne
  let f : FormIndex A R q := FiniteCode.equiv.symm ⟨0,Nat.pos_of_ne_zero ne⟩
  have project : FormIndex A R q → OldInputIndex A R q := fun
    | .inl a => a
    | .inr (e,a,_) => ⟨.inl e.val.1,(a,none)⟩
  have hi := (FiniteCode.equiv (project f)).isLt
  omega

theorem prep_runs (hq : 0<q) (M : ℕ) (W : Base) (bW : W.Bounded M)
    (h : Input p A R q hq W) (room : Room p A R q hq M) :
    ∃t≤10,∃U,Runs (storageBound Header Field M) (atoms prep) W t U ∧ U.Bounded M ∧
      Prepared p A R q hq U := by
  have hu : (W.array .u0).length=O := h.u0 ▸ List.length_ofFn
  have hf : (W.array .forms).length=F*N := h.forms ▸ MatrixEncoding.word_length _
  have fN : F*N≤M := hf ▸ bW.2.1 .forms
  have nM : N≤M := h.oldInput ▸ bW.1 .oldInput
  have xz : N+O=X := rfl
  have zz : O+X=Z := rfl
  have zM := room.zdim
  have aM := room.ambient
  have eM := room.entries
  have pM := room.field
  have hp := (Fact.out : p.Prime).one_lt
  let d := N+(if N=0 then 1 else 0)
  have hd : 0<d ∧ d≤M := by dsimp [d]; split_ifs <;> omega
  have rows : F*N/d=F := by
    by_cases h0 : N=0
    · rw [noForms p A R q h0]
      simp
    · simp [d,h0,Nat.mul_div_cancel _ (Nat.pos_of_ne_zero h0)]
  have size : (Width hq).dimension*(X*Z)≤M := by simpa only [←Nat.mul_assoc] using eM
  have valid : ValidAtoms M prep W := by
    simp only [prep,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar,
      Function.update_apply,reduceCtorEq,if_false,if_true,h.oldInput,h.width,hu,hf,xz,zz]
    dsimp only [d] at hd
    simp only [Nat.zero_le, true_and, and_true]
    exact ⟨by omega,zM,by split_ifs <;> omega,hd.2,⟨by decide,hd.1⟩,aM,size⟩
  obtain ⟨run,bU⟩ := atoms_runs bW prep valid
  refine ⟨10,le_rfl,_,run,bU,⟨⟨?_,?_,?_,h.u0,h.v0,h.u1,h.v1,h.second,h.forms,h.lift⟩,?_,?_,?_,?_,?_⟩⟩
  all_goals simp [prep,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,h.oldInput,h.width,h.modulus,
    hu,hf,xz,zz,←Nat.mul_assoc] <;> exact rows

private theorem matSmall (M : ℕ) (r : MatrixArithmetic.Reg) (n : ℕ) (h : matScalar r=.literal n) :
    n≤M := by cases r <;> simp [matScalar] at h <;> omega
private theorem wedgeSmall (M : ℕ) (r : WedgeKernel.Reg) (n : ℕ) (h : wedgeScalar r=.literal n) :
    n≤M := by
  rcases r with (r|r)|r
  · cases r <;> simp [wedgeScalar,wedgeReg] at h <;> omega
  · simp [wedgeScalar] at h; omega
  · simp [wedgeScalar] at h; omega

theorem program_runs (hq : 0<q) (M : ℕ) (S : State) (bounded : S.Bounded M)
    (h : Input p A R q hq S.left.left) (room : Room p A R q hq M) :
    ∃t≤time p N F (Width hq).dimension X Z,∃T,Runs (storageBound Reg Arr M)
      (program p) S t T ∧ T.Bounded M ∧ Output p A R q hq T := by
  have field := room.field
  obtain ⟨t,ht,U,run,bU,pre,chosen⟩ := Ports.thenRun_post (atoms prep) matScalar matArray
    MatrixArithmetic.multiply S.left M 10 (F*(Width hq).dimension*(12*N+9)+7)
    bounded.left (matSmall M) (Prepared p A R q hq)
    (fun _ T => T.array .output=chosenFormMatrix p A R q hq)
    (prep_runs p A R q hq M S.left.left bounded.left.left h room) (by
      intro P hP _ bT
      rw [chosenFormMatrix_product]
      exact MatrixEncoding.multiply_word_runs _ _ _ M bT hP.formCount hP.oldInput hP.width hP.modulus
        hP.forms hP.lift (by omega) room.chosen)
  let Post := fun (T : Store MR MA) => Prepared p A R q hq T.left ∧ T.right.array .output=chosenFormMatrix p A R q hq
  obtain ⟨s,hs,T,run',bT,c,gram⟩ := Ports.thenRun_post multiply wedgeScalar wedgeArray
    (WedgeKernel.program p) S M (10+(Fintype.card MatrixArithmetic.Reg+Fintype.card MatrixArithmetic.Arr+
      (F*(Width hq).dimension*(12*N+9)+7)))
    ((Width hq).dimension*X*Z*(WedgeConstraints.expression.cost+4)+10+220*((Width hq).dimension+X*Z+p+1)^4)
    bounded (wedgeSmall M) Post (fun _ W => KernelProgram.Represents p (X*Z) 0 (wedgeWord p A R q hq)
      (KernelProgramCorrectness.encode (GeneratedCoordinateEntries.operatorChart (Width hq)
        (ConstructiveTensor.obstructionMap A R q hq))) W.right)
    ⟨t,ht,U,run,bU,pre,chosen⟩ (by
      intro P hP _ bW
      let W := Ports.target wedgeScalar wedgeArray P
      have ready : WedgeConstraints.Ready D (formMatrix p A R q) (chosenFormMatrix p A R q hq)
        p N O (Width hq).dimension X Z (NatArrayExpressions.inputs W.left) :=
        ⟨hP.1.modulus,hP.1.oldInput,hP.1.oldOutput,hP.1.width,hP.1.xdim,hP.1.zdim,
          hP.1.u0,hP.1.v0,hP.1.u1,hP.1.v1,hP.1.second,hP.1.forms,hP.2⟩
      exact wedgeOperator_runs p A R q hq M room.field room.ambient room.square W bW ready hP.1.length)
  exact ⟨s,hs,T,run',bT,⟨c.1.xdim,c.1.zdim,gram⟩⟩

end GroupWL.MachinePrograms.ChargedWedgeStage
