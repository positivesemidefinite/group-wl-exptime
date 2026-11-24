import GroupWL.GeneratedCoordinateEntries

/-! Constraint-matrix entries are exactly the corresponding generator entries. -/
namespace GroupWL.GeneratedCoordinateEntries
open ConstructiveCoordinates GeneratedCoordinates ObstructionDuality
variable {F ι κ : Type} [Field F] [DecidableEq F]
  [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] [FiniteCode ι] [FiniteCode κ]

theorem matrix_inverse_single (i : Fin (FiniteCode.size ι)) (z : Fin (FiniteCode.size κ)) :
    (matrixCoordinates (F:=F) (ι:=ι) (κ:=κ)).equiv.symm (Pi.single (matrixPosition (F:=F) i z) 1)=
      Pi.single ((FiniteCode.equiv (α:=ι)).symm i) (Pi.single ((FiniteCode.equiv (α:=κ)).symm z) 1) := by
  funext a b
  change (Pi.single (matrixPosition (F:=F) i z) (1:F) :
    Fin (matrixCoordinates (F:=F) (ι:=ι) (κ:=κ)).dimension → F)
      (FiniteCode.equiv (α:=Σ _ : ι,Fin (FiniteCode.size κ)) ⟨a,FiniteCode.equiv b⟩)=_
  simp [matrixPosition,Pi.single_apply,eq_comm,Equiv.eq_symm_apply]
  simp [ite_apply,Pi.single_apply,(FiniteCode.equiv (α:=Σ _ : ι,Fin (FiniteCode.size κ))).injective.eq_iff,
    Sigma.mk.inj_iff,heq_iff_eq,Equiv.apply_eq_iff_eq_symm_apply,eq_comm]
  have he : (FiniteCode.equiv (α:=Σ _ : ι,Fin (FiniteCode.size κ)) ⟨a,FiniteCode.equiv b⟩=
      FiniteCode.equiv ⟨(FiniteCode.equiv (α:=ι)).symm i,z⟩) ↔
      a=(FiniteCode.equiv (α:=ι)).symm i ∧ b=(FiniteCode.equiv (α:=κ)).symm z := by
    rw [(FiniteCode.equiv (α:=Σ _ : ι,Fin (FiniteCode.size κ))).injective.eq_iff]
    simp [Sigma.mk.inj_iff,heq_iff_eq,Equiv.apply_eq_iff_eq_symm_apply]
  have he' : (FiniteCode.equiv (α:=Σ _ : ι,Fin (FiniteCode.size κ)) ⟨a,FiniteCode.equiv b⟩=
      FiniteCode.equiv ⟨(FiniteCode.equiv (α:=ι)).symm i,z⟩) ↔
      i=FiniteCode.equiv a ∧ b=(FiniteCode.equiv (α:=κ)).symm z := by
    simpa [Equiv.eq_symm_apply,eq_comm] using he
  by_cases ha : i=FiniteCode.equiv a
  · by_cases hb : b=(FiniteCode.equiv (α:=κ)).symm z
    · simp only [if_pos ha,if_pos hb]
      exact (if_pos (he'.mpr ⟨ha,hb⟩)).symm
    · simp only [if_pos ha,if_neg hb]
      exact (if_neg (fun h=>hb (he'.mp h).2)).symm
  · simp only [if_neg ha]
    exact (if_neg (fun h=>ha (he'.mp h).1)).symm

variable {W : Type} [AddCommGroup W] [Module F W]
  (D : Coordinates F W) (σ : W →ₗ[F] MatrixSpace F ι κ)

theorem constraintMap_entry (k : Fin D.dimension)
    (i : Fin (FiniteCode.size ι)) (z : Fin (FiniteCode.size κ)) :
    constraintMap D σ (Pi.single (matrixPosition (F:=F) i z) 1) k=
      σ (D.equiv.symm (Pi.single k 1)) ((FiniteCode.equiv (α:=ι)).symm i)
        ((FiniteCode.equiv (α:=κ)).symm z) := by
  change tests D σ ((matrixCoordinates (F:=F) (ι:=ι) (κ:=κ)).equiv.symm
    (Pi.single (matrixPosition (F:=F) i z) 1)) k=_
  rw [matrix_inverse_single]
  simp [tests,generator,matrixDual,matrixPair,Pi.single_apply,ite_apply]

end GroupWL.GeneratedCoordinateEntries
