import GroupWL.MachinePrograms.CircuitTensorPipelineFinish
import GroupWL.MachinePrograms.CircuitOutputWriter
import GroupWL.ComputableCircuitReduction

namespace GroupWL.MachinePrograms.CircuitTensorPipeline
open NatArrayLanguage

/-- Physical output locations of the circuit layout and parameter programs. -/
structure FrontPorts (R A : Type) where
  horizontal : R
  frames : R
  dimension : R
  coefficients : SourceCoefficients.Arr → A
  readouts : A
  charge : A

/-- Location of the initial header inside the combined incidence and wedge program. -/
structure HeaderPorts (U V : Type) where
  reg : IncidencePipeline.Records.Header → U
  arr : IncidencePipeline.Records.Field → V
  asReg : U → Option IncidencePipeline.Records.Header
  asArr : V → Option IncidencePipeline.Records.Field
  reg_eq : ∀ r, asReg (reg r) = some r
  arr_eq : ∀ a, asArr (arr a) = some a

namespace HeaderPorts
variable {R A U V : Type} (h : HeaderPorts U V) (f : FrontPorts R A)
def read (S : Store U V) : IncidencePipeline.Records.HeaderStore :=
  ⟨S.scalar ∘ h.reg, S.array ∘ h.arr⟩

def scalar (r : U) : Ports.Scalar R A :=
  match h.asReg r with
  | some .horizontal => .scalar f.horizontal
  | some .frames => .scalar f.frames
  | _ => .literal 0

def array (a : V) : Option A :=
  match h.asArr a with
  | some (.record a) => some (f.coefficients a)
  | some .dimensions => some f.readouts
  | some .charge => some f.charge
  | none => none

theorem small (M : ℕ) (r : U) (v : ℕ) (hv : h.scalar f r = .literal v) : v≤M := by
  unfold scalar at hv
  split at hv <;> simp_all <;> omega

@[simp] theorem record (S : Store R A) (a : SourceCoefficients.Arr) :
    (h.read (Ports.target (h.scalar f) (h.array f) S)).array (.record a)=S.array (f.coefficients a) := by
  simp [read,Ports.target,array,h.arr_eq]
@[simp] theorem dimensions (S : Store R A) :
    (h.read (Ports.target (h.scalar f) (h.array f) S)).array .dimensions=S.array f.readouts := by
  simp [read,Ports.target,array,h.arr_eq]
@[simp] theorem charge (S : Store R A) :
    (h.read (Ports.target (h.scalar f) (h.array f) S)).array .charge=S.array f.charge := by
  simp [read,Ports.target,array,h.arr_eq]
@[simp] theorem horizontal (S : Store R A) :
    (h.read (Ports.target (h.scalar f) (h.array f) S)).scalar .horizontal=S.scalar f.horizontal := by
  simp [read,Ports.target,scalar,h.reg_eq]
@[simp] theorem frames (S : Store R A) :
    (h.read (Ports.target (h.scalar f) (h.array f) S)).scalar .frames=S.scalar f.frames := by
  simp [read,Ports.target,scalar,h.reg_eq]

variable {X E : Type} [FiniteCode X] [FiniteCode E] {r : ℕ} (p : ℕ) [Fact p.Prime]
  (C : SourceLayout.ComparisonData (ZMod p) X E r) (L q : ℕ)

structure Written (S : Store R A) : Prop where
  coefficients : ∀a,S.array (f.coefficients a)=SourceTableEncoding.coefficientData p C L a
  readouts : S.array f.readouts=SourceTableEncoding.readoutDimensions p C L
  blocks : (S.array f.charge).length=SourceTableEncoding.blockCount p C L
  horizontal : S.scalar f.horizontal=SourceTableEncoding.horizontalCount p C L
  frames : S.scalar f.frames=q

theorem incoming (S : Store R A) (out : Written f p C L q S) :
    IncidencePipeline.Records.Input p C L q (h.read (Ports.target (h.scalar f) (h.array f) S)) := by
  exact ⟨fun a=>(h.record f S a).trans (out.coefficients a),
    (h.dimensions f S).trans out.readouts, by rw [h.charge f S];exact out.blocks,
    (h.horizontal f S).trans out.horizontal,(h.frames f S).trans out.frames⟩

end HeaderPorts

def fields (R A : Type) : CircuitWriterReduction.Fields (R ⊕ ChargedAssembly.Reg) (A ⊕ ChargedAssembly.Arr) where
  scalar
    | .input₁ => .inr (.inr (.inl .inputdim))
    | .input₂ => .inr (.inr (.inr .inputdim))
    | .output₁ => .inr (.inr (.inl .zdim))
    | .output₂ => .inr (.inr (.inr .zdim))
    | .dimension => .inr (.inl (.inr (ChargedAssembly.wreg .dimension)))
  array
    | .coefficients₁ => .inr (.inr (.inl .output))
    | .coefficients₂ => .inr (.inr (.inr .output))

theorem describes {R A : Type} {p : ℕ} [Fact p.Prime] (S : Store (R⊕ChargedAssembly.Reg) (A⊕ChargedAssembly.Arr))
    (T U : Statement.TensorDescription p) (k : ℕ) (out : ChargedAssembly.Output S.right T U k) :
    CircuitWriterReduction.Describes p ((fields R A).read S) T U k :=
  ⟨out.x,out.z,out.coefficients,out.x',out.z',out.coefficients',out.dimension⟩

end GroupWL.MachinePrograms.CircuitTensorPipeline
