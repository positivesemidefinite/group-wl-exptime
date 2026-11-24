import GroupWL.ConstructiveCoordinates
import GroupWL.SourceLayout.System

/-! Computational presentations of the source scopes and coefficients. -/
namespace GroupWL.ComputableSource

open SourceLayout ConstructiveCoordinates
variable {F T E : Type} [Field F] {r L : ℕ} (C : ComparisonData F T E r)
  [FiniteCode (C.Readout L)]

def scope : C.Block L → Finset (C.Readout L) :=
  letI : DecidableEq (C.Readout L) := (FiniteCode.equiv (α := C.Readout L)).decidableEq
  fun B => match B with
  | .inl h => {.inl h}
  | .inr s => {.inl (C.squareLeft L s), .inl (C.squareRight L s),
      .inr (C.squareAfter L s), .inr (C.squareBefore L s)}

theorem scope_eq (B : C.Block L) : scope C B = C.scope L B := by
  classical
  ext x
  cases B <;> simp [scope,ComparisonData.scope]

def coefficient (B : C.Block L) (q : C.Readout L) : C.readoutSpace L q →ₗ[F] F :=
  letI : DecidableEq (C.Readout L) := (FiniteCode.equiv (α := C.Readout L)).decidableEq
  (C.blockEquation L B).comp (LinearMap.single F (C.readoutSpace L) q)

theorem coefficient_eq [Fintype T] [Fintype E] (B : C.Block L) (q : C.Readout L) :
    coefficient C B q = C.coefficient B q := by
  unfold coefficient ComparisonData.coefficient
  congr 2
  exact Subsingleton.elim _ _

def affineSystem [Fintype T] [Fintype E] :
    AffineSystem F (C.Block L) (C.Readout L) (C.readoutSpace L) where
  scope := scope C
  coefficient := coefficient C
  coefficient_outside B q h := by
    rw [coefficient_eq]
    apply C.coefficient_outside
    simpa only [scope_eq] using h

theorem affineSystem_eq [Fintype T] [Fintype E] :
    affineSystem C = C.affineSystem (L := L) := by
  unfold affineSystem ComparisonData.affineSystem
  congr 1
  · exact funext (scope_eq C)
  · funext B q
    exact coefficient_eq C B q

def nodeCoordinates [DecidableEq F] :
    (t : Node T E L) → Coordinates F (C.nodeSpace L t)
  | .inl t => Coordinates.pi (Fin (C.dim t))
  | .inr _ => Coordinates.scalar

def readoutCoordinates [DecidableEq F] :
    (q : C.Readout L) → Coordinates F (C.readoutSpace L q)
  | .inl h => nodeCoordinates C h.1
  | .inr _ => Coordinates.scalar

end GroupWL.ComputableSource
