import GroupWL.ResidualTensors
import GroupWL.RelativeMultipliers

namespace GroupWL.ResidualTensors

open IncidenceTensor IncidenceCoordinates ObstructionDuality

set_option linter.unusedSectionVars false

section CoordinateDuality
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- The full coordinate pairing identifies vectors with the dual space. -/
noncomputable def coordinateDual : (ι → K) ≃ₗ[K] Module.Dual K (ι → K) where
  toFun := coordinateFunctional
  invFun := functionalCoefficients
  left_inv x := by ext i; simp [functionalCoefficients, coordinateFunctional, Pi.single_apply]
  right_inv f := by apply LinearMap.ext; intro x; exact (functional_eq_sum f x).symm
  map_add' x y := by ext z; simp [coordinateFunctional, add_mul, Finset.sum_add_distrib]
  map_smul' c x := by ext z; simp [coordinateFunctional, mul_assoc, Finset.mul_sum]

end CoordinateDuality

universe u
variable {F I J : Type u} [Field F] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {V : J → Type u} [∀ j, AddCommGroup (V j)] [∀ j, Module F (V j)]
variable (A : AffineSystem F I J V) (q : ℕ)

/-- The actual old input associated to a retained annihilator covector. -/
noncomputable def queryInput (E : Submodule F (InputIndex A q → F)) :
    orthogonal E →ₗ[F] OldInput A q :=
  (LinearMap.fst F (OldInput A q) (OldOutput A q)).comp
    ((inputCoordinates A q).symm.toLinearMap.comp (orthogonal E).subtype)

/-- Increasing the retained span restricts the query domain by its natural
inclusion, with no choice of a projection onto an orthogonal complement. -/
noncomputable def queryInclusion {E D : Submodule F (InputIndex A q → F)} (hED : E ≤ D) :
    orthogonal D →ₗ[F] orthogonal E := Submodule.inclusion (orthogonal_antitone hED)

@[simp] theorem queryInput_comp_inclusion {E D : Submodule F (InputIndex A q → F)}
    (hED : E ≤ D) :
    (queryInput A q E).comp (queryInclusion A q hED) = queryInput A q D := rfl

/-- The retained space transported back to the physical tensor input. -/
noncomputable def physicalRetained (E : Submodule F (InputIndex A q → F)) :
    Submodule F (PaddedInput A q) := E.map (inputCoordinates A q).symm.toLinearMap

/-- Coordinate annihilator vectors are precisely physical annihilating
functionals after transporting the full (unrestricted) coordinate pairing. -/
noncomputable def queryDual (E : Submodule F (InputIndex A q → F)) :
    orthogonal E →ₗ[F] (physicalRetained A q E).dualAnnihilator where
  toFun u := ⟨(coordinateFunctional u.val).comp (inputCoordinates A q).toLinearMap, by
    rw [Submodule.mem_dualAnnihilator]
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hx
    change coordinateFunctional u.val (inputCoordinates A q ((inputCoordinates A q).symm z)) = 0
    rw [LinearEquiv.apply_symm_apply]
    exact u.property z hz⟩
  map_add' u v := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    simp [coordinateFunctional, add_mul, Finset.sum_add_distrib]
  map_smul' c u := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    simp [coordinateFunctional, mul_assoc, Finset.mul_sum]

theorem queryDual_surjective (E : Submodule F (InputIndex A q → F)) :
    Function.Surjective (queryDual A q E) := by
  intro f
  let h := f.val.comp (inputCoordinates A q).symm.toLinearMap
  let u : InputIndex A q → F := (coordinateDual (K := F)).symm h
  have hu : u ∈ orthogonal E := by
    intro z hz
    have hf := ((physicalRetained A q E).mem_dualAnnihilator f.val).mp f.property
    have hf := hf
      ((inputCoordinates A q).symm z) ⟨z, hz, rfl⟩
    change coordinateFunctional u z = 0
    change coordinateDual u z = 0
    rw [show coordinateDual u = h from (coordinateDual (K := F)).apply_symm_apply h]
    exact hf
  refine ⟨⟨u, hu⟩, ?_⟩
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  change coordinateDual u (inputCoordinates A q x) = f.val x
  rw [show coordinateDual u = h from (coordinateDual (K := F)).apply_symm_apply h]
  exact congrArg f.val ((inputCoordinates A q).symm_apply_apply x)

/-- The scalar frame at a vertex is an actual copy of `F^q`. -/
noncomputable def scalarFrameEquiv (v : I ⊕ J) :
    (Fin q → F) ≃ₗ[F] IncidenceBudget.scalarSubspace A q v where
  toFun x := ⟨IncidenceBudget.scalarEmbedding A q (Pi.single v x),
    ⟨Pi.single v x, by intro w hw; simp [hw], rfl⟩⟩
  invFun z a := (z.val.1 v a).fst
  left_inv x := by funext a; simp [IncidenceBudget.scalarEmbedding]
  right_inv z := by
    apply Subtype.ext
    obtain ⟨x, hx, hz⟩ := z.property
    change IncidenceBudget.scalarEmbedding A q (Pi.single v (fun a => (z.val.1 v a).fst)) = z.val
    rw [← hz]
    apply congrArg (IncidenceBudget.scalarEmbedding A q)
    funext w a
    by_cases hw : w = v
    · subst w; simp [IncidenceBudget.scalarEmbedding]
    · simp [hw, hx w hw]
  map_add' x y := by apply Subtype.ext; simp [Pi.single_add]
  map_smul' c x := by apply Subtype.ext; simp [Pi.single_smul]

@[simp] theorem scalarFrameEquiv_single (v : I ⊕ J) (a : Fin q) :
    (scalarFrameEquiv A q v (Pi.single a 1)).val = (unitInput A v a, 0) := by
  apply Prod.ext
  · funext w b
    change TrivSqZeroExt.inl ((Pi.single v (Pi.single a (1 : F)) : (I ⊕ J) → Fin q → F) w b) = unitInput A v a w b
    by_cases hw : w = v
    · subst w
      by_cases hb : b = a
      · subst b; simp [unitInput]
      · simp [unitInput, Pi.single_eq_of_ne hb]
    · simp [unitInput, Pi.single_eq_of_ne hw]
  · rfl

/-- Reading a functional in the scalar-frame basis preserves its rank. -/
noncomputable def scalarFrameDualEquiv (v : I ⊕ J) :
    Module.Dual F (IncidenceBudget.scalarSubspace A q v) ≃ₗ[F] (Fin q → F) :=
  (scalarFrameEquiv A q v).dualMap.trans (coordinateDual (K := F)).symm

@[simp] theorem scalarFrameDualEquiv_apply (v : I ⊕ J)
    (f : Module.Dual F (IncidenceBudget.scalarSubspace A q v)) (a : Fin q) :
    scalarFrameDualEquiv A q v f a = f (scalarFrameEquiv A q v (Pi.single a 1)) := by
  simp [scalarFrameDualEquiv, coordinateDual, functionalCoefficients,
    LinearEquiv.trans_apply, LinearEquiv.dualMap_apply]
  congr 2
  funext b
  simp [Pi.single_apply]

theorem scalarProjection_eq_restriction (E : Submodule F (InputIndex A q → F))
    (v : I ⊕ J) :
    scalarVertexProjection A (queryInput A q E) v =
      (scalarFrameDualEquiv A q v).toLinearMap.comp
        ((RestrictionRank.restriction (physicalRetained A q E)
          (IncidenceBudget.scalarSubspace A q v)).comp (queryDual A q E)) := by
  apply LinearMap.ext
  intro u
  funext a
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, scalarFrameDualEquiv_apply]
  change (queryInput A q E u v a).fst =
    coordinateFunctional u.val (inputCoordinates A q
      (scalarFrameEquiv A q v (Pi.single a 1)).val)
  rw [scalarFrameEquiv_single, inputCoordinates_unit]
  rw [show coordinateFunctional u.val (Pi.single (scalarIndex A q v a) 1) =
    u.val (scalarIndex A q v a) by simp [coordinateFunctional, Pi.single_apply]]
  change (((inputCoordinates A q).symm u.val).1 v a).fst = _
  rw [← inputCoordinates_scalar]
  rw [LinearEquiv.apply_symm_apply]

theorem scalarProjection_finrank (E : Submodule F (InputIndex A q → F))
    (v : I ⊕ J) :
    Module.finrank F (scalarVertexProjection A (queryInput A q E) v).range =
      Module.finrank F (RestrictionRank.restriction (physicalRetained A q E)
        (IncidenceBudget.scalarSubspace A q v)).range := by
  rw [scalarProjection_eq_restriction, LinearMap.range_comp,
    LinearEquiv.finrank_map_eq, LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr (queryDual_surjective A q E))]

theorem goodVertex_iff_not_bad (E : Submodule F (InputIndex A q → F))
    (v : I ⊕ J) :
    GoodVertex A (queryInput A q E) v ↔
      v ∉ IncidenceBudget.badVertices A q (physicalRetained A q E) := by
  rw [IncidenceBudget.mem_badVertices_iff, GoodVertex, scalarProjection_finrank]
  omega

theorem good_of_goodVertex (E : Submodule F (InputIndex A q → F)) (i : I)
    (hi : GoodVertex A (queryInput A q E) (.inl i)) : Good A q E i := by
  obtain ⟨x, y, ab, hab⟩ := goodVertex_exists_scalar_minor A (queryInput A q E) (.inl i) hi
  have hu : IsUnit (LocalMultiplier.minor
      (((inputCoordinates A q).symm x.val).1 (.inl i))
      (((inputCoordinates A q).symm y.val).1 (.inl i)) ab.val.1 ab.val.2) := by
    apply (LocalMultiplier.squareZero_isUnit_iff _).mpr
    change (queryInput A q E x (.inl i) ab.1.1).fst *
      (queryInput A q E y (.inl i) ab.1.2).fst -
      (queryInput A q E x (.inl i) ab.1.2).fst *
      (queryInput A q E y (.inl i) ab.1.1).fst ≠ 0
    rw [mul_comm (queryInput A q E x (.inl i) ab.1.2).fst]
    exact hab
  obtain ⟨t, ht⟩ := hu
  exact ⟨⟨x, y, ab, t, ht⟩⟩

theorem goodVertex_of_good (E : Submodule F (InputIndex A q → F)) (i : I)
    (hi : Good A q E i) : GoodVertex A (queryInput A q E) (.inl i) := by
  classical
  obtain ⟨m⟩ := hi
  let s := scalarVertexProjection A (queryInput A q E) (.inl i)
  have hminor := (LocalMultiplier.squareZero_isUnit_iff (↑m.unit : TrivSqZeroExt F F)).mp
    m.unit.isUnit
  rw [m.unit_eq] at hminor
  change s m.u m.ab.1.1 * s m.v m.ab.1.2 -
    s m.u m.ab.1.2 * s m.v m.ab.1.1 ≠ 0 at hminor
  by_contra h
  have hdim : Module.finrank F s.range ≤ 1 := by
    change ¬ 1 < Module.finrank F s.range at h
    omega
  obtain ⟨w, hw⟩ := (finrank_le_one_iff (K := F) (V := s.range)).mp hdim
  obtain ⟨a, ha⟩ := hw ⟨s m.u, ⟨m.u, rfl⟩⟩
  obtain ⟨b, hb⟩ := hw ⟨s m.v, ⟨m.v, rfl⟩⟩
  have hu (k : Fin q) : s m.u k = a * w.val k :=
    (congrArg (fun z : s.range => z.val k) ha).symm
  have hv (k : Fin q) : s m.v k = b * w.val k :=
    (congrArg (fun z : s.range => z.val k) hb).symm
  apply hminor
  rw [hu, hu, hv, hv]
  ring

theorem good_iff_not_bad (E : Submodule F (InputIndex A q → F)) (i : I) :
    Good A q E i ↔ .inl i ∉ IncidenceBudget.badVertices A q (physicalRetained A q E) :=
  ⟨fun h => (goodVertex_iff_not_bad A q E (.inl i)).mp (goodVertex_of_good A q E i h),
   fun h => good_of_goodVertex A q E i ((goodVertex_iff_not_bad A q E (.inl i)).mpr h)⟩

theorem physicalRetained_finrank (E : Submodule F (InputIndex A q → F)) :
    Module.finrank F (physicalRetained A q E) = Module.finrank F E :=
  (inputCoordinates A q).symm.finrank_map_eq E

/-- The concrete bad-vertex budget in the same coordinates as the residual
and shear constructions. -/
theorem coordinate_badVertices_budget (E : Submodule F (InputIndex A q → F)) :
    (q - 1) * (IncidenceBudget.badVertices A q (physicalRetained A q E)).card ≤
      Module.finrank F E := by
  have h := IncidenceBudget.badVertices_budget A q (physicalRetained A q E)
  rwa [physicalRetained_finrank] at h

theorem good_antitone {E D : Submodule F (InputIndex A q → F)} (hED : E ≤ D)
    (i : I) (hi : Good A q D i) : Good A q E i := by
  rw [good_iff_not_bad] at hi ⊢
  exact fun h => hi (BadBudget.badVertices_mono _ (Submodule.map_mono hED) q h)

/-- The owner budget uses the dimension of the coordinate retained space. -/
theorem coordinate_owner_budget (owner : I ⊕ J → I) (K : ℕ) (hq : 1 < q)
    (E : Submodule F (InputIndex A q → F))
    (hbudget : Module.finrank F E < (q - 1) * (K + 1)) :
    (BadBudget.ownerSet owner (IncidenceBudget.scalarSubspace A q)
      (physicalRetained A q E) q).card ≤ K := by
  apply IncidenceBudget.owner_budget A q K hq owner (physicalRetained A q E)
  rwa [physicalRetained_finrank]

end GroupWL.ResidualTensors
