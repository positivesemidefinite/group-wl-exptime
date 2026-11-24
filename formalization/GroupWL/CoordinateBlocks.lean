import GroupWL.BadBudget
import GroupWL.RestrictionRank

namespace GroupWL
namespace CoordinateBlocks

variable {F I W : Type*} [Field F] [AddCommGroup W] [Module F W]

/-- Vectors supported at one vertex. -/
def atVertex (i : I) : Submodule F (I → W) where
  carrier := {x | ∀ j, j ≠ i → x j = 0}
  zero_mem' := by intro j _; rfl
  add_mem' := by intro x y hx hy j hj; simp only [Pi.add_apply, hx j hj, hy j hj, add_zero]
  smul_mem' := by intro c x hx j hj; simp only [Pi.smul_apply, hx j hj, smul_zero]

/-- The different vertices' coordinate spaces are an independent family. -/
theorem independent : iSupIndep (atVertex (F := F) (W := W) : I → Submodule F (I → W)) := by
  intro i
  apply Submodule.disjoint_def.mpr
  intro x hxi hxrest
  have hle : (⨆ (j) (_ : j ≠ i), atVertex (F := F) (W := W) j) ≤
      (LinearMap.proj i : (I → W) →ₗ[F] W).ker := by
    refine iSup_le fun j => iSup_le fun hji => ?_
    intro v hv
    exact hv i (Ne.symm hji)
  have hi : x i = 0 := hle hxrest
  funext j
  by_cases hj : j = i
  · simpa only [hj] using hi
  · exact hxi j hj

/-- Identifying the coordinate subspace with one copy of the local space. -/
noncomputable def equiv (i : I) : atVertex (F := F) (W := W) i ≃ₗ[F] W := by
  classical
  refine
    { toFun := fun x => x.1 i
      invFun := fun w => ⟨Pi.single i w, ?_⟩
      left_inv := ?_
      right_inv := ?_
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  · intro j hj
    simp [Pi.single_apply, hj]
  · intro x
    apply Subtype.ext
    funext j
    by_cases hj : j = i
    · simp [Pi.single_apply, hj]
    · simp [Pi.single_apply, hj, x.property j hj]
  · intro w
    simp

/-- Each vertex contributes exactly the dimension of its local coordinate block. -/
theorem finrank_atVertex (i : I) :
    Module.finrank F (atVertex (F := F) (W := W) i) = Module.finrank F W :=
  (equiv i).finrank_eq

/-- For scalar `q`-frames, the block has dimension exactly `q`. -/
theorem finrank_scalarFrame (i : I) (q : ℕ) :
    Module.finrank F (atVertex (F := F) (W := Fin q → F) i) = q := by
  rw [finrank_atVertex, Module.finrank_pi, Fintype.card_fin]

/-- The bad-vertex inequality phrased using the rank of restricted scalar
functionals, exactly the geometric criterion used by the residual argument. -/
theorem restriction_bad_budget
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (S : I → Submodule F V) (hS : iSupIndep S) (E : Submodule F V)
    (q : ℕ) (hdim : ∀ i, Module.finrank F (S i) = q)
    (bad : Finset I)
    (hbad : ∀ i ∈ bad, Module.finrank F (RestrictionRank.restriction E (S i)).range ≤ 1) :
    (q - 1) * bad.card ≤ Module.finrank F E := by
  apply BadBudget.bad_budget S hS E q bad
  intro i hi
  exact (RestrictionRank.bad_iff_intersection E (S i) q (hdim i)).mp (hbad i hi)

end CoordinateBlocks
end GroupWL
