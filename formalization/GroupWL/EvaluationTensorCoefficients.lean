import GroupWL.ConstructiveTensor

/-! Block formulas for assembling the dense evaluation tensor from a
materialized operator basis and the input-twist coefficient array. -/
namespace GroupWL.EvaluationTensorCoefficients

open ConstructiveCoordinates
variable {F X Z : Type} [Field F] [DecidableEq F]
  [AddCommGroup X] [Module F X] [AddCommGroup Z] [Module F Z]
def unit {n : ℕ} (i : Fin n) : Fin n → F := Pi.single i 1

variable (D : Coordinates F X) (E : Coordinates F Z)
  (Y : Submodule F (X →ₗ[F] Z)) (H : Coordinates F Y)

private theorem prod_apply_left (x : X × Y) (i : Fin D.dimension) :
    (D.prod H).equiv x (Fin.castAdd H.dimension i) = D.equiv x.1 i := by
  change Sum.elim (D.equiv x.1) (H.equiv x.2)
    (finSumFinEquiv.symm (Fin.castAdd H.dimension i)) = _
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

private theorem prod_apply_right (x : X × Y) (i : Fin H.dimension) :
    (D.prod H).equiv x (Fin.natAdd D.dimension i) = H.equiv x.2 i := by
  change Sum.elim (D.equiv x.1) (H.equiv x.2)
    (finSumFinEquiv.symm (Fin.natAdd D.dimension i)) = _
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

theorem prod_inverse_left (i : Fin D.dimension) :
    (D.prod H).equiv.symm (unit (F := F) (Fin.castAdd H.dimension i)) =
      (D.equiv.symm (unit (F := F) i),0) := by
  change (D.equiv.symm (fun j => unit (F := F) (Fin.castAdd H.dimension i) (Fin.castAdd H.dimension j)),
    H.equiv.symm (fun j => unit (F := F) (Fin.castAdd H.dimension i) (Fin.natAdd D.dimension j))) = _
  have hl : (fun j => unit (F := F) (Fin.castAdd H.dimension i) (Fin.castAdd H.dimension j)) =
      unit (F := F) i := by
    funext j
    simp [unit,Pi.single_apply,(Fin.castAdd_injective D.dimension H.dimension).eq_iff]
  have hr : (fun j => unit (F := F) (Fin.castAdd H.dimension i) (Fin.natAdd D.dimension j)) = 0 := by
    funext j
    have hh : Fin.natAdd D.dimension j ≠ Fin.castAdd H.dimension i := by
      intro h
      have hv := congrArg Fin.val h
      dsimp at hv
      omega
    simp [unit,Pi.single_apply,hh]
  rw [hl,hr,map_zero]

theorem prod_inverse_right (i : Fin H.dimension) :
    (D.prod H).equiv.symm (unit (F := F) (Fin.natAdd D.dimension i)) =
      (0,H.equiv.symm (unit (F := F) i)) := by
  change (D.equiv.symm (fun j => unit (F := F) (Fin.natAdd D.dimension i) (Fin.castAdd H.dimension j)),
    H.equiv.symm (fun j => unit (F := F) (Fin.natAdd D.dimension i) (Fin.natAdd D.dimension j))) = _
  have hl : (fun j => unit (F := F) (Fin.natAdd D.dimension i) (Fin.castAdd H.dimension j)) = 0 := by
    funext j
    have hh : Fin.castAdd H.dimension j ≠ Fin.natAdd D.dimension i := by
      intro h
      have hv := congrArg Fin.val h
      dsimp at hv
      omega
    simp [unit,Pi.single_apply,hh]
  have hr : (fun j => unit (F := F) (Fin.natAdd D.dimension i) (Fin.natAdd D.dimension j)) =
      unit (F := F) i := by
    funext j
    simp [unit,Pi.single_apply,(Fin.natAdd_injective H.dimension D.dimension).eq_iff]
  rw [hl,hr,map_zero]

def operatorCoefficient (j : Fin H.dimension) (i : Fin D.dimension) (z : Fin E.dimension) : F :=
  E.equiv (((H.equiv.symm (unit (F := F) j) : Y) : X →ₗ[F] Z)
    (D.equiv.symm (unit (F := F) i))) z

variable (ε : AlternatingBilinearMap F X Z)

def tensor : AlternatingBilinearMap F
    (Fin (D.dimension+H.dimension) → F) (Fin E.dimension → F) :=
  DenseTensorEncoding.transport (evaluationTwist Y ε) (D.prod H).equiv E.equiv

theorem coefficient_left_left (i j : Fin D.dimension) (z : Fin E.dimension) :
    tensor D E Y H ε (unit (F := F) (Fin.castAdd H.dimension i))
      (unit (F := F) (Fin.castAdd H.dimension j)) z =
      E.equiv (ε (D.equiv.symm (unit (F := F) i)) (D.equiv.symm (unit (F := F) j))) z := by
  unfold tensor
  rw [DenseTensorEncoding.transport_apply]
  erw [prod_inverse_left D Y H i]
  erw [prod_inverse_left D Y H j]
  simp

theorem coefficient_left_right (i : Fin D.dimension) (j : Fin H.dimension) (z : Fin E.dimension) :
    tensor D E Y H ε (unit (F := F) (Fin.castAdd H.dimension i))
      (unit (F := F) (Fin.natAdd D.dimension j)) z = operatorCoefficient D E Y H j i z := by
  unfold tensor
  rw [DenseTensorEncoding.transport_apply]
  erw [prod_inverse_left D Y H i,prod_inverse_right D Y H j]
  simp [operatorCoefficient]

theorem coefficient_right_left (i : Fin H.dimension) (j : Fin D.dimension) (z : Fin E.dimension) :
    tensor D E Y H ε (unit (F := F) (Fin.natAdd D.dimension i))
      (unit (F := F) (Fin.castAdd H.dimension j)) z = -operatorCoefficient D E Y H i j z := by
  unfold tensor
  rw [DenseTensorEncoding.transport_apply]
  erw [prod_inverse_right D Y H i,prod_inverse_left D Y H j]
  simp [operatorCoefficient]

theorem coefficient_right_right (i j : Fin H.dimension) (z : Fin E.dimension) :
    tensor D E Y H ε (unit (F := F) (Fin.natAdd D.dimension i))
      (unit (F := F) (Fin.natAdd D.dimension j)) z = 0 := by
  unfold tensor
  rw [DenseTensorEncoding.transport_apply]
  erw [prod_inverse_right D Y H i,prod_inverse_right D Y H j]
  simp

end GroupWL.EvaluationTensorCoefficients
