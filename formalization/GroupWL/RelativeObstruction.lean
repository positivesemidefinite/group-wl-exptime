import GroupWL.ResidualTensors
import GroupWL.RelativeMultipliers

/-! # Relative obstructions without orthogonal projections

Ambient functionals are tested against rank-one relative corrections.  This
identifies their contractions on the annihilator and supplies actual linear
lifts through the selected incidence-kernel space.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace GroupWL.RelativeObstruction

open ObstructionDuality AlternatingCoordinates CoordinateShears MatrixEvaluationGroup
open ResidualTensors

section Generic
variable {F ι κ : Type*} [Field F] [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]


/-- Explicit instance parameters keep the subtype-valued operator codomain
visible to typeclass inference. -/
noncomputable instance shearAddCommGroup (C : Submodule F (MatrixSpace F ι κ)) :
    AddCommGroup ((ι → F) →ₗ[F] operatorSpace C) :=
  LinearMap.addCommGroup (R₁ := F) (R₂ := F) (M := ι → F)
    (N₂ := operatorSpace C) (σ₁₂ := RingHom.id F)

/-- The relative correction space in the actual shear parameters. -/
def correctionSpace (C : Submodule F (MatrixSpace F ι κ)) (E : Submodule F (ι → F)) :
    Submodule F ((ι → F) →ₗ[F] operatorSpace C) where
  carrier := {α | CoherentShears.RelativeCorrection (operatorSpace C) E α}
  zero_mem' := by constructor <;> intros <;> simp
  add_mem' := by
    rintro α β ⟨hα, hα'⟩ ⟨hβ, hβ'⟩
    constructor
    · intro x hx; simp [hα x hx, hβ x hx]
    · intro x e he; simp [hα' x e he, hβ' x e he]
  smul_mem' := by
    rintro c α ⟨hα, hα'⟩
    constructor
    · intro x hx; simp [hα x hx]
    · intro x e he; simp [hα' x e he]

/-- The actual relative boundary map, with its entire ambient tensor target. -/
noncomputable def relativeBoundary (C : Submodule F (MatrixSpace F ι κ))
    (E : Submodule F (ι → F)) : correctionSpace C E →ₗ[F] TensorSpace F ι κ where
  toFun α := bilinearCoordinates (shearCoboundary (operatorSpace C) α.val).toLinearMap
  map_add' α β := by
    funext i j z
    simp only [bilinearCoordinates_apply, shearCoboundary_apply, Submodule.coe_add,
      LinearMap.add_apply, Pi.add_apply, Pi.sub_apply]
    ring
  map_smul' c α := by
    funext i j z
    simp only [bilinearCoordinates_apply, shearCoboundary_apply, Submodule.coe_smul,
      LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Pi.sub_apply]
    ring

/-- One covector in the retained annihilator times one admissible operator. -/
noncomputable def elementaryCorrection (C : Submodule F (MatrixSpace F ι κ))
    (E : Submodule F (ι → F)) (u : orthogonal E)
    (y : MatrixSpace F ι κ) (hy : y ∈ annihilator C) (hyE : y ∈ vanishingOn E) :
    correctionSpace C E := by
  let y' : operatorSpace C := ⟨matrixLinearEquiv y, ⟨y, hy, rfl⟩⟩
  refine ⟨(coordinateFunctional u.val).smulRight y', ?_, ?_⟩
  · intro x hx
    change coordinateFunctional u.val x • y' = 0
    rw [u.property x hx, zero_smul]
  · intro x e he
    change coordinateFunctional u.val x • matrixToLinear y e = 0
    rw [show matrixToLinear y e = 0 from hyE e he, smul_zero]

theorem elementaryCorrection_coordinates (C : Submodule F (MatrixSpace F ι κ))
    (E : Submodule F (ι → F)) (u : orthogonal E)
    (y : MatrixSpace F ι κ) (hy : y ∈ annihilator C) (hyE : y ∈ vanishingOn E) :
    relativeBoundary C E (elementaryCorrection C E u y hy hyE) =
      boundary (fun i j z => u.val i * y j z) := by
  funext i j z
  change (coordinateFunctional u.val (Pi.single i 1) • matrixToLinear y (Pi.single j 1) -
    coordinateFunctional u.val (Pi.single j 1) • matrixToLinear y (Pi.single i 1)) z = _
  simp [coordinateFunctional, matrixToLinear, evaluation, Pi.single_apply, boundary]

/-- Pairing against a rank-one matrix is ordinary operator evaluation. -/
theorem matrixPair_rankOne_single (y : MatrixSpace F ι κ) (u : ι → F) (z : κ) :
    matrixPair y (rankOne u (Pi.single z 1)) = matrixToLinear y u z := by
  simp [matrixPair, rankOne, Pi.single_apply, matrixToLinear, evaluation, mul_comm]

theorem rankOne_mem_vanishing (E : Submodule F (ι → F)) (u : orthogonal E) (w : κ → F) :
    rankOne u.val w ∈ vanishingOn E := by
  intro x hx
  funext z
  change (∑ i, x i * (u.val i * w z)) = 0
  have hu := u.property x hx
  change (∑ i, u.val i * x i) = 0 at hu
  simp_rw [show ∀ i, x i * (u.val i * w z) = (u.val i * x i) * w z from fun i => by ring]
  rw [← Finset.sum_mul, hu, zero_mul]

/-- The rank-one boundary test reads a single contraction of the dual tensor. -/
theorem pairing_elementaryCorrection
    (C : Submodule F (MatrixSpace F ι κ)) (E : Submodule F (ι → F))
    (b : AlternatingBilinearMap F (ι → F) (κ → F)) (u : orthogonal E)
    (y : MatrixSpace F ι κ) (hy : y ∈ annihilator C) (hyE : y ∈ vanishingOn E) :
    tensorPair (bilinearCoordinates b.toLinearMap)
      (relativeBoundary C E (elementaryCorrection C E u y hy hyE)) =
      2 * matrixPair (matrixLinearEquiv.symm (b.toLinearMap u.val)) y := by
  have hb : ∀ i j z, bilinearCoordinates b.toLinearMap j i z =
      -bilinearCoordinates b.toLinearMap i j z := by
    intro i j z
    simpa only [bilinearCoordinates_apply, Pi.neg_apply] using
      congrFun (b.skew (Pi.single j 1) (Pi.single i 1)) z
  rw [elementaryCorrection_coordinates, tensorPair_boundary _ _ hb]
  congr 1
  have hf : matrixLinearEquiv.symm (b.toLinearMap u.val) =
      fun j z => b.toLinearMap u.val (Pi.single j 1) z := by
    funext j z
    simp [matrixLinearEquiv]
    apply congrArg (fun x : ι → F => b.toLinearMap u.val x z)
    funext k
    simp [Pi.single_apply]
  rw [hf]
  change (∑ i, ∑ j, ∑ z, bilinearCoordinates b.toLinearMap i j z * (u.val i * y j z)) =
    ∑ j, ∑ z, (b.toLinearMap u.val (Pi.single j 1) z) * y j z
  simp_rw [bilinear_evaluation]
  simp only [Pi.single_apply, Finset.mul_sum, Finset.sum_mul]
  simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Every relative dual contraction is the restriction of a genuine element
of `C`.  This applies unchanged when `E` is isotropic. -/
theorem relative_slices (h2 : (2 : F) ≠ 0)
    (C : Submodule F (MatrixSpace F ι κ)) (E : Submodule F (ι → F))
    (b : AlternatingBilinearMap F (ι → F) (κ → F))
    (hb : ∀ α : correctionSpace C E,
      tensorPair (bilinearCoordinates b.toLinearMap) (relativeBoundary C E α) = 0)
    (u : orthogonal E) :
    ∃ c ∈ C, ∀ v : orthogonal E, b u.val v.val = matrixToLinear c v.val := by
  let f : Module.Dual F (vanishingOn E) :=
    (matrixDual (matrixLinearEquiv.symm (b.toLinearMap u.val))).comp (vanishingOn E).subtype
  have hf : ∀ y : vanishingOn E, y.val ∈ annihilator C → f y = 0 := by
    intro y hy
    have he := hb (elementaryCorrection C E u y.val hy y.property)
    rw [pairing_elementaryCorrection] at he
    exact (mul_eq_zero.mp he).resolve_left h2
  obtain ⟨c, hc, hcf⟩ := (relative_matrix_obstruction_iff C (vanishingOn E) f).mp hf
  refine ⟨c, hc, ?_⟩
  intro v
  funext z
  have hz := hcf ⟨rankOne v.val (Pi.single z 1), rankOne_mem_vanishing E v _⟩
  change matrixPair (matrixLinearEquiv.symm (b.toLinearMap u.val))
    (rankOne v.val (Pi.single z 1)) = matrixPair c (rankOne v.val (Pi.single z 1)) at hz
  rw [matrixPair_rankOne_single, matrixPair_rankOne_single] at hz
  change matrixLinearEquiv (matrixLinearEquiv.symm (b.toLinearMap u.val)) v.val z = _ at hz
  simpa only [LinearEquiv.apply_symm_apply] using hz

/-- Ambient finite-dimensional separation already suffices for the relative
image test; antisymmetrization removes the symmetric part of every separator. -/
theorem exists_relative_shear_of_pairings (h2 : (2 : F) ≠ 0)
    (C : Submodule F (MatrixSpace F ι κ)) (E : Submodule F (ι → F))
    (t : AlternatingBilinearMap F (ι → F) (κ → F))
    (ht : ∀ b : AlternatingBilinearMap F (ι → F) (κ → F),
      (∀ α : correctionSpace C E,
        tensorPair (bilinearCoordinates b.toLinearMap) (relativeBoundary C E α) = 0) →
      tensorPair (bilinearCoordinates b.toLinearMap) (bilinearCoordinates t.toLinearMap) = 0) :
    ∃ α : (ι → F) →ₗ[F] operatorSpace C,
      CoherentShears.RelativeCorrection (operatorSpace C) E α ∧
      ∀ x y, shearCoboundary _ α x y = t x y := by
  have halt (b : AlternatingBilinearMap F (ι → F) (κ → F)) :
      Alternating (bilinearCoordinates b.toLinearMap) := by
    constructor
    · intro i z; simp
    · intro i j z
      simpa only [bilinearCoordinates_apply, Pi.neg_apply] using
        congrFun (b.skew (Pi.single j 1) (Pi.single i 1)) z
  have hr : bilinearCoordinates t.toLinearMap ∈ LinearMap.range (relativeBoundary C E) := by
    apply (mem_range_iff_dual_obstructions (K := F) (V := correctionSpace C E) (relativeBoundary C E) (bilinearCoordinates t.toLinearMap)).mpr
    intro φ hφ
    obtain ⟨g, rfl⟩ := tensorDual_surjective φ
    let γ := boundary g
    let b := alternatingFromArray (LinearEquiv.refl F (ι → F)) (LinearEquiv.refl F (κ → F)) γ
    have hco (f : (ι → F) →ₗ[F] (ι → F) →ₗ[F] (κ → F)) :
        typedCoordinates (LinearEquiv.refl F (ι → F)) (LinearEquiv.refl F (κ → F)) f =
          bilinearCoordinates f := by
      funext i j z
      rw [typedCoordinates_apply, bilinearCoordinates_apply]
      rfl
    have hb : bilinearCoordinates b.toLinearMap = γ := by
      rw [← hco]
      exact coordinates_alternatingFromArray h2 (LinearEquiv.refl F (ι → F))
        (LinearEquiv.refl F (κ → F)) γ (boundary_alternating g)
    have hb' : ∀ α : correctionSpace C E,
        tensorPair (bilinearCoordinates b.toLinearMap) (relativeBoundary C E α) = 0 := by
      intro α
      rw [hb]
      change tensorPair (boundary g) (bilinearCoordinates
        (shearCoboundary (operatorSpace C) α.val).toLinearMap) = 0
      rw [tensorPair_boundary_left _ _ (halt (shearCoboundary (operatorSpace C) α.val))]
      have hz := LinearMap.congr_fun hφ α
      change tensorPair g (bilinearCoordinates
        (shearCoboundary (operatorSpace C) α.val).toLinearMap) = 0 at hz
      rw [hz, mul_zero]
    have hz := ht b hb'
    rw [hb] at hz
    change tensorPair (boundary g) (bilinearCoordinates t.toLinearMap) = 0 at hz
    rw [tensorPair_boundary_left _ _ (halt t)] at hz
    exact (mul_eq_zero.mp hz).resolve_left h2
  obtain ⟨α, hα⟩ := hr
  refine ⟨α.val, α.property, ?_⟩
  have he : (shearCoboundary (operatorSpace C) α.val).toLinearMap = t.toLinearMap :=
    bilinearCoordinates.injective hα
  exact fun x y => LinearMap.congr_fun (LinearMap.congr_fun he x) y

end Generic

section Incidence
open IncidenceTensor IncidenceCoordinates IncidenceGroup GlobalCokernel
universe u
variable {F I J : Type u} [Field F] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {V : J → Type u} [∀ j, AddCommGroup (V j)] [∀ j, Module F (V j)]
variable (A : AffineSystem F I J V) (q : ℕ)

/-- The actual relative-dual lifting statement. It does not require the
restricted slice map to be injective, or the retained space to be nondegenerate. -/
theorem incidence_relative_lift (h2 : (2 : F) ≠ 0) (hq : 0 < q)
    (E : Submodule F (InputIndex A q → F))
    (b : AlternatingBilinearMap F (InputIndex A q → F) (OutputIndex A q → F))
    (hb : ∀ α : correctionSpace (C A q hq) E,
      tensorPair (bilinearCoordinates b.toLinearMap) (relativeBoundary (C A q hq) E α) = 0) :
    ∃ P : orthogonal E →ₗ[F] OldInput A q,
      (∀ u, P u ∈ chosenSpace A q hq) ∧
      ∀ u v : orthogonal E, b u.val v.val = outputCoordinates A q
        (omega A q (P u) ((inputCoordinates A q).symm v.val).1, 0) := by
  let U := orthogonal E
  let M : chosenSpace A q hq →ₗ[F] (U →ₗ[F] (OutputIndex A q → F)) :=
    { toFun := fun a => (outputCoordinates A q).toLinearMap.comp
        ((sliceMap A q a.val).comp ((inputCoordinates A q).symm.toLinearMap.comp U.subtype))
      map_add' := by
        intro a a'
        apply LinearMap.ext
        intro v
        simp only [LinearMap.comp_apply, map_add, Submodule.coe_add, LinearMap.add_apply]
      map_smul' := by
        intro c a
        apply LinearMap.ext
        intro v
        simp only [LinearMap.comp_apply, map_smul, Submodule.coe_smul, LinearMap.smul_apply, RingHom.id_apply] }
  let G : U →ₗ[F] U →ₗ[F] (OutputIndex A q → F) :=
    LinearMap.mk₂ F (fun u v => b u.val v.val)
      (by intros; simp) (by intros; simp) (by intros; simp) (by intros; simp)
  have hG : ∀ u, G u ∈ LinearMap.range M := by
    intro u
    obtain ⟨c, hc, hcv⟩ := relative_slices h2 (C A q hq) E b hb u
    obtain ⟨d, hd, hdc⟩ := hc
    obtain ⟨a, ha, had⟩ := hd
    subst d
    subst c
    refine ⟨⟨a, ha⟩, ?_⟩
    apply LinearMap.ext
    intro v
    change outputCoordinates A q (sliceMap A q a ((inputCoordinates A q).symm v.val)) = b u.val v.val
    rw [hcv v]
    change _ = matrixLinearEquiv
      (matrixLinearEquiv.symm (((inputCoordinates A q).arrowCongr (outputCoordinates A q))
        (sliceMap A q a))) v.val
    rw [LinearEquiv.apply_symm_apply]
    rfl
  obtain ⟨P, hP⟩ := exists_linear_lift M G hG
  refine ⟨(chosenSpace A q hq).subtype.comp P, fun u => (P u).property, ?_⟩
  intro u v
  have huv := LinearMap.congr_fun (LinearMap.congr_fun hP u) v
  exact huv.symm

end Incidence

end GroupWL.RelativeObstruction
