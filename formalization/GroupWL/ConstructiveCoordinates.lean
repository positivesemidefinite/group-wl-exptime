import GroupWL.PivotElimination
import GroupWL.FiniteCodeConstructions
import GroupWL.IncidenceTensor

/-! Finite coordinates assembled by explicit field elimination. -/
namespace GroupWL.ConstructiveCoordinates

open CoordinateElimination
open scoped BigOperators

variable (F : Type*) [Field F] [DecidableEq F]

structure Coordinates (X : Type*) [AddCommGroup X] [Module F X] where
  dimension : ℕ
  equiv : X ≃ₗ[F] (Fin dimension → F)

variable {F}

def dotMap {n : ℕ} (a : Fin n → F) : (Fin n → F) →ₗ[F] F where
  toFun x := ∑ i, a i * x i
  map_add' x y := by simp [mul_add,Finset.sum_add_distrib]
  map_smul' c x := by simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.mul_sum]; congr 1; funext i; ring

/-- Dual coefficients are computed by evaluations on the unit vectors. -/
def dualPi (n : ℕ) : ((Fin n → F) →ₗ[F] F) ≃ₗ[F] (Fin n → F) where
  toFun f i := f (Pi.single i 1)
  invFun := dotMap
  left_inv f := by
    apply LinearMap.ext
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ f x]
    change (∑ i, f (Pi.single i 1)*x i) = ∑ i, x i • f (fun j => if i=j then 1 else 0)
    apply Finset.sum_congr rfl
    intro i _
    have he : (fun j : Fin n => if i=j then (1:F) else 0) = Pi.single i 1 := by
      funext j
      simp [Pi.single_apply,eq_comm]
    rw [he,smul_eq_mul,mul_comm]
  right_inv a := by funext i; simp [dotMap,Pi.single_apply]
  map_add' f g := by funext i; rfl
  map_smul' c f := by funext i; rfl

namespace Coordinates

def pi (ι : Type*) [FiniteCode ι] : Coordinates F (ι → F) :=
  ⟨FiniteCode.size ι, LinearEquiv.funCongrLeft F F (FiniteCode.equiv (α := ι)).symm⟩

def scalar : Coordinates F F :=
  ⟨1, (LinearEquiv.funUnique (Fin 1) F F).symm⟩

def dual {X : Type*} [AddCommGroup X] [Module F X] (D : Coordinates F X) :
    Coordinates F (X →ₗ[F] F) :=
  ⟨D.dimension, D.equiv.dualMap.symm.trans (dualPi D.dimension)⟩

def prod {X Y : Type*} [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]
    (D : Coordinates F X) (E : Coordinates F Y) : Coordinates F (X × Y) :=
  ⟨D.dimension+E.dimension,
    ((D.equiv.prodCongr E.equiv).trans
      (LinearEquiv.sumArrowLequivProdArrow _ _ F F).symm).trans
      (LinearEquiv.funCongrLeft F F finSumFinEquiv.symm)⟩

def dependentPi {ι : Type*} [FiniteCode ι] {X : ι → Type*}
    [∀ i, AddCommGroup (X i)] [∀ i, Module F (X i)] (D : ∀ i, Coordinates F (X i)) :
    Coordinates F (∀ i, X i) := by
  let e : (∀ i, X i) ≃ₗ[F] ((Σ i, Fin (D i).dimension) → F) :=
    { toFun := fun x a => (D a.1).equiv (x a.1) a.2
      invFun := fun x i => (D i).equiv.symm (fun j => x ⟨i,j⟩)
      left_inv := by intro x; funext i; apply (D i).equiv.injective; simp
      right_inv := by intro x; funext a; exact congrFun ((D a.1).equiv.apply_symm_apply _) a.2
      map_add' := by intros; funext a; simp
      map_smul' := by intros; funext a; simp }
  exact ⟨FiniteCode.size (Σ i, Fin (D i).dimension),
    e.trans (Coordinates.pi (Σ i, Fin (D i).dimension)).equiv⟩

def reindexKernel {X Y : Type*} [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]
    (D : Coordinates F X) (E : Coordinates F Y) (f : X →ₗ[F] Y) :
    LinearMap.ker f ≃ₗ[F]
      LinearMap.ker (E.equiv.toLinearMap.comp (f.comp D.equiv.symm.toLinearMap)) where
  toFun x := ⟨D.equiv x, by
    change E.equiv (f (D.equiv.symm (D.equiv x))) = 0
    rw [D.equiv.symm_apply_apply]
    have hx : f x = 0 := x.property
    rw [hx,map_zero]⟩
  invFun x := ⟨D.equiv.symm x, by
    apply E.equiv.injective
    change E.equiv (f (D.equiv.symm x)) = E.equiv 0
    rw [map_zero]
    exact x.property⟩
  left_inv x := Subtype.ext (D.equiv.symm_apply_apply _)
  right_inv x := Subtype.ext (D.equiv.apply_symm_apply _)
  map_add' x y := Subtype.ext (D.equiv.map_add x y)
  map_smul' c x := Subtype.ext (D.equiv.map_smul c x)

/-- Kernel coordinates from finite input/output coordinates, with no basis
selection or search over field vectors. -/
def kernel {X Y : Type*} [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]
    (D : Coordinates F X) (E : Coordinates F Y) (f : X →ₗ[F] Y) :
    Coordinates F (LinearMap.ker f) :=
  let g := E.equiv.toLinearMap.comp (f.comp D.equiv.symm.toLinearMap)
  ⟨(PivotElimination.kernelChart E.dimension D.dimension g).width,
    (reindexKernel D E f).trans (PivotElimination.kernelCoordinates g)⟩

theorem kernel_dimension_le {X Y : Type*} [AddCommGroup X] [Module F X]
    [AddCommGroup Y] [Module F Y] (D : Coordinates F X) (E : Coordinates F Y)
    (f : X →ₗ[F] Y) : (kernel D E f).dimension ≤ D.dimension :=
  (PivotElimination.kernelChart _ _ _).width_le

end Coordinates

section Readout
open IncidenceTensor
variable {F : Type} [Field F] [DecidableEq F]
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {V : J → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module F (V j)]
variable (A : AffineSystem F I J V)

/-- An explicit kernel algorithm computes the radical coordinates at each
readout from a code of its incidence list and coordinates of its readout space. -/
def readoutRadical (j : J) [FiniteCode (Neighbors A j)] (D : Coordinates F (V j)) :
    Coordinates F (ReadoutRadical A j) :=
  Coordinates.kernel (Coordinates.pi (Neighbors A j)) D.dual (relationMap A j)

theorem readoutRadical_dimension_le (j : J) [FiniteCode (Neighbors A j)]
    (D : Coordinates F (V j)) :
    (readoutRadical A j D).dimension ≤ FiniteCode.size (Neighbors A j) :=
  Coordinates.kernel_dimension_le _ _ _

end Readout
end GroupWL.ConstructiveCoordinates
