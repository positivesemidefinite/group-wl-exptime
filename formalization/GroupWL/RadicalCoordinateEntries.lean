import GroupWL.ConstructiveIncidenceCoefficients
import GroupWL.GeneratedCoordinateEntries
import GroupWL.RelationCoordinates

/-! Entrywise identification of readout radical coordinates with the executed
Gaussian kernel lift. -/
namespace GroupWL.ConstructiveIncidence
open IncidenceTensor ConstructiveCoordinates
variable {F I J : Type} [Field F] [DecidableEq F]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [FiniteCode I] [FiniteCode J]
variable {V : J → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module F (V j)]
variable (A : AffineSystem F I J V) [∀ j, FiniteCode (Neighbors A j)]
    (D : ∀ j, Coordinates F (V j))

theorem radicalLift_kernel_entry (e : Incidence A)
    (k : Fin (readoutRadical A e.1.2 (D e.1.2)).dimension) :
    radicalLift A (fun j => readoutRadical A j (D j)) e k =
      (PivotElimination.kernelChart (D e.1.2).dimension
        (FiniteCode.size (Neighbors A e.1.2))
        (relationCoordinates A e.1.2 (D e.1.2))).lift (Pi.single k 1)
          (FiniteCode.equiv (⟨e.1.1,e.2⟩ : Neighbors A e.1.2)) := by
  have h := GeneratedCoordinateEntries.kernel_inverse_coordinates
    (Coordinates.pi (F:=F) (Neighbors A e.1.2)) (D e.1.2).dual
    (relationMap A e.1.2) (Pi.single k 1)
  have he := congrFun h (FiniteCode.equiv (⟨e.1.1,e.2⟩ : Neighbors A e.1.2))
  change ((readoutRadical A e.1.2 (D e.1.2)).equiv.symm (Pi.single k 1)).val
    ((FiniteCode.equiv (α := Neighbors A e.1.2)).symm
      (FiniteCode.equiv (⟨e.1.1,e.2⟩ : Neighbors A e.1.2))) = _ at he
  rw [Equiv.symm_apply_apply] at he
  exact he

end GroupWL.ConstructiveIncidence
