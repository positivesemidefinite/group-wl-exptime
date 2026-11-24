import GroupWL.AddressedCircuit
import GroupWL.SourceLayout.Images

/-! The explicit comparison gadget attached to an addressed monotone circuit.
Circuit schemas are never expanded into their address cube. -/

namespace GroupWL.CircuitComparisons

open AddressedCircuit SourceLayout

variable {T : Type*} {r : ℕ} (C : Circuit T r)

def gateDim (t : T) : ℕ := if C.kind t = .scalar then 1 else 2

def firstCoordinate (t : T) : Fin (gateDim C t) :=
  ⟨0, by unfold gateDim; split <;> omega⟩

def portCoordinate (t : T) (b : Bool) : Fin (gateDim C t) :=
  if h : C.kind t = .scalar then ⟨0, by simp [gateDim, h]⟩
  else ⟨if b then 1 else 0, by simp only [gateDim, h, ↓reduceIte]; split <;> omega⟩

inductive Primary (T : Type*) where
  | gate : T → Primary T
  | broadcast : Primary T
  | dummy : Primary T
  deriving DecidableEq, Fintype

def primaryDim : Primary T → ℕ
  | .gate t => gateDim C t
  | .broadcast => 1
  | .dummy => 1

/-- Each constructor is a succinct directed connection and will get one
private two-coordinate buffer. Seed comparisons are separately direct. -/
inductive Connection where
  | circuit : Fin C.edges → Connection
  | test : Fin C.testCount → Connection
  | flip : Fin r → Connection
  | broadcast : (t : T) → Fin (gateDim C t) → Connection
  | identity : (t : T) → Fin (gateDim C t) → Connection
  | broadcastIdentity : Bool → Connection
  deriving DecidableEq, Fintype

namespace Connection

def source : Connection C → Primary T
  | .circuit e => .gate (C.schema e).source
  | .test k => .gate (C.test k).gate
  | .flip _ => .broadcast
  | .broadcast _ _ => .broadcast
  | .identity t _ => .gate t
  | .broadcastIdentity _ => .broadcast

def target : Connection C → Primary T
  | .circuit e => .gate (C.schema e).target
  | .test _ => .broadcast
  | .flip _ => .broadcast
  | .broadcast t _ => .gate t
  | .identity t _ => .gate t
  | .broadcastIdentity _ => .broadcast

def domain : Connection C → ProductDomain r
  | .circuit e => (C.schema e).domain
  | .test k => (C.test k).domain
  | .flip _ => ProductDomain.full r
  | .broadcast _ _ => ProductDomain.full r
  | .identity _ _ => ProductDomain.full r
  | .broadcastIdentity _ => ProductDomain.full r

def permutation : Connection C → AddressMap r
  | .circuit e => (C.schema e).permutation
  | .flip i => fun j => if j = i then Equiv.swap false true else Equiv.refl Bool
  | _ => AddressMap.identity r

end Connection

abbrev RealType := Primary T ⊕ Connection C

def dimension : RealType C → ℕ
  | .inl t => primaryDim C t
  | .inr _ => 2

inductive Comparison where
  | seed : Fin C.seedCount → Comparison
  | copy : Connection C → Bool → Comparison
  | sum : Connection C → Comparison
  deriving DecidableEq, Fintype

variable (F : Type*) [Field F]

def gateInput (t : T) (b : Bool) : (Fin (gateDim C t) → F) →ₗ[F] F :=
  LinearMap.proj (portCoordinate C t b)

def gateOutput (t : T) : (Fin (gateDim C t) → F) →ₗ[F] F :=
  if C.kind t = .scalar then gateInput C F t false
  else gateInput C F t false + gateInput C F t true

def Connection.sourceForm : (e : Connection C) →
    (Fin (primaryDim C (e.source C)) → F) →ₗ[F] F
  | .circuit e => gateOutput C F (C.schema e).source
  | .test k => gateOutput C F (C.test k).gate
  | .flip _ => LinearMap.proj (0 : Fin 1)
  | .broadcast _ _ => LinearMap.proj (0 : Fin 1)
  | .identity t j => LinearMap.proj j
  | .broadcastIdentity _ => LinearMap.proj (0 : Fin 1)

def Connection.targetForm : (e : Connection C) →
    (Fin (primaryDim C (e.target C)) → F) →ₗ[F] F
  | .circuit e => gateInput C F (C.schema e).target (C.schema e).port
  | .test _ => LinearMap.proj (0 : Fin 1)
  | .flip _ => LinearMap.proj (0 : Fin 1)
  | .broadcast t j => LinearMap.proj j
  | .identity t j => LinearMap.proj j
  | .broadcastIdentity _ => LinearMap.proj (0 : Fin 1)

namespace Comparison

def source : Comparison C → RealType C
  | .seed k => .inl (.gate (C.seed k).gate)
  | .copy e _ => .inl (e.source C)
  | .sum e => .inr e

def target : Comparison C → RealType C
  | .seed _ => .inl .dummy
  | .copy e _ => .inr e
  | .sum e => .inl (e.target C)

def domain : Comparison C → ProductDomain r
  | .seed k => (C.seed k).domain
  | .copy e _ => e.domain C
  | .sum e => e.domain C

def permutation : Comparison C → AddressMap r
  | .sum e => e.permutation C
  | _ => AddressMap.identity r

def sourceForm : (e : Comparison C) → (Fin (dimension C (e.source C)) → F) →ₗ[F] F
  | .seed k => gateOutput C F (C.seed k).gate
  | .copy e _ => e.sourceForm C F
  | .sum _ => (LinearMap.proj (0 : Fin 2) : (Fin 2 → F) →ₗ[F] F) + LinearMap.proj 1

def targetForm : (e : Comparison C) → (Fin (dimension C (e.target C)) → F) →ₗ[F] F
  | .seed _ => 0
  | .copy _ b => LinearMap.proj (if b then (1 : Fin 2) else 0)
  | .sum e => e.targetForm C F

end Comparison

/-- The actual comparison instance, before the private scalar wires and
site-and-square layout supplied by `ComparisonData.affineSystem`. -/
def comparisons : ComparisonData F (RealType C) (Comparison C) r where
  dim := dimension C
  source := Comparison.source C
  target := Comparison.target C
  domain e := (e.domain C).coordinate
  domain_nonempty e := (e.domain C).nonempty
  permutation := Comparison.permutation C
  sourceForm := Comparison.sourceForm C F
  targetForm := Comparison.targetForm C F

/-- The two broadcast self-connections disagree only on the third comparison
of the second copy. This is the explicit rejecting charge. -/
def rejectingConstant : Comparison C → F
  | .sum (.broadcastIdentity true) => 1
  | _ => 0

theorem dimension_pos (t : RealType C) : 0 < dimension C t := by
  rcases t with t | e
  · cases t with
    | gate t => change 0 < gateDim C t; unfold gateDim; split <;> omega
    | broadcast => exact Nat.zero_lt_succ 0
    | dummy => exact Nat.zero_lt_succ 0
  · exact Nat.zero_lt_succ 1

theorem dimension_le_two (t : RealType C) : dimension C t ≤ 2 := by
  rcases t with t | e
  · cases t with
    | gate t => change gateDim C t ≤ 2; unfold gateDim; split <;> omega
    | broadcast => exact Nat.le_succ 1
    | dummy => exact Nat.le_succ 1
  · exact le_rfl

end GroupWL.CircuitComparisons
