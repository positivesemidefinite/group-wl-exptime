import GroupWL.WedgeConstraintEncoding

/-! Materialized matrix multiplication computes the forms on the chosen basis. -/
namespace GroupWL.MatrixEncoding
open CachedElimination
variable {p m n k : ℕ} [Fact p.Prime]

theorem product_ofLinear (f : (Fin n → ZMod p) →ₗ[ZMod p] (Fin m → ZMod p))
    (g : (Fin k → ZMod p) →ₗ[ZMod p] (Fin n → ZMod p)) :
    product (ofLinear f) (ofLinear g)=ofLinear (f.comp g) := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  have h := congrFun (LinearMap.congr_fun (product_toLinear (ofLinear f) (ofLinear g))
    (Pi.single (⟨j,hj⟩ : Fin k) 1)) (⟨i,hi⟩ : Fin m)
  rw [toLinear_ofLinear,toLinear_ofLinear] at h
  change (product (ofLinear f) (ofLinear g))[(⟨i,hi⟩ : Fin m)][(⟨j,hj⟩ : Fin k)]=
    (ofLinear (f.comp g))[(⟨i,hi⟩ : Fin m)][(⟨j,hj⟩ : Fin k)]
  erw [ofLinear_entry]
  simpa [toLinear,Pi.single_apply] using h

end GroupWL.MatrixEncoding

namespace GroupWL.ConstructiveIncidence
open IncidenceTensor ConstructiveCoordinates
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [FiniteCode I] [FiniteCode J]
variable (p : ℕ) [Fact p.Prime]
variable {V : J → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module (ZMod p) (V j)]
variable (A : AffineSystem (ZMod p) I J V)
  (R : ∀ j, Coordinates (ZMod p) (ReadoutRadical A j)) (q : ℕ)

theorem chosenFormMatrix_product (hq : 0<q) : chosenFormMatrix p A R q hq=
    MatrixEncoding.word (MatrixEncoding.product (CachedElimination.ofLinear (numericFormMap A R q))
      (CachedElimination.ofLinear (chosenChart A R q hq).lift)) := by
  rw [MatrixEncoding.product_ofLinear]
  rfl

end GroupWL.ConstructiveIncidence
