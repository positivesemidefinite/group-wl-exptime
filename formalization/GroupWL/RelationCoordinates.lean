import GroupWL.ConstructiveCoordinates

/-! The matrix supplied to radical elimination consists of coefficient
evaluations on the readout coordinate vectors, in numeric neighbor order. -/
namespace GroupWL.ConstructiveCoordinates
open IncidenceTensor
open scoped BigOperators
variable {F I J : Type} [Field F] [DecidableEq F]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {V : J → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module F (V j)]
variable (A : AffineSystem F I J V) (j : J) [FiniteCode (Neighbors A j)]
  (D : Coordinates F (V j))

def relationCoordinates : (Fin (FiniteCode.size (Neighbors A j)) → F) →ₗ[F]
    (Fin D.dimension → F) :=
  D.dual.equiv.toLinearMap.comp ((relationMap A j).comp
    (Coordinates.pi (F:=F) (Neighbors A j)).equiv.symm.toLinearMap)

theorem relationCoordinates_unit (i : Fin (FiniteCode.size (Neighbors A j)))
    (k : Fin D.dimension) :
    relationCoordinates A j D (Pi.single i 1) k =
      A.coefficient ((FiniteCode.equiv (α := Neighbors A j)).symm i).val j
        (D.equiv.symm (Pi.single k 1)) := by
  have hpi : (Coordinates.pi (F:=F) (Neighbors A j)).equiv.symm (Pi.single i (1:F)) =
      Pi.single ((FiniteCode.equiv (α := Neighbors A j)).symm i) 1 := by
    funext h
    change ((Pi.single i (1:F) : Fin (FiniteCode.size (Neighbors A j)) → F)) (FiniteCode.equiv h) = _
    simp only [Pi.single_apply]
    have he : i=FiniteCode.equiv h ↔ (FiniteCode.equiv (α := Neighbors A j)).symm i=h :=
      by
        constructor
        · intro hh; rw [hh,Equiv.symm_apply_apply]
        · intro hh; rw [← hh,Equiv.apply_symm_apply]
    simpa only [eq_comm,he]
  have hrel (h : Neighbors A j) : relationMap A j (Pi.single h (1:F)) = A.coefficient h.val j := by
    simp [relationMap,Pi.single_apply]
  change D.dual.equiv (relationMap A j ((Coordinates.pi (F:=F) (Neighbors A j)).equiv.symm (Pi.single i 1))) k = _
  rw [hpi,hrel]
  rfl

end GroupWL.ConstructiveCoordinates
