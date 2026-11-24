import GroupWL.ObstructionDuality
import GroupWL.TensorGroup

/-! # Separation by alternating coordinate obstructions

The ambient tensor pairing is perfect. For an alternating target, arbitrary
linear separating functionals can be antisymmetrized. This avoids any
nondegeneracy assumption about restrictions of a coordinate pairing.
-/

namespace GroupWL
namespace AlternatingCoordinates

open ObstructionDuality
variable {F ι κ : Type*} [Field F] [Fintype ι] [Fintype κ]

/-- Pairing a fixed array with all three-index coordinate arrays. -/
def tensorDual : TensorSpace F ι κ →ₗ[F] Module.Dual F (TensorSpace F ι κ) where
  toFun g :=
    { toFun := tensorPair g
      map_add' := by intros; simp [tensorPair, mul_add, Finset.sum_add_distrib]
      map_smul' := by intros; simp [tensorPair, Finset.mul_sum, mul_left_comm] }
  map_add' := by intros; ext t; simp [tensorPair, add_mul, Finset.sum_add_distrib]
  map_smul' := by intros; ext t; simp [tensorPair, Finset.mul_sum, mul_assoc]

/-- The actual coordinate tensor pairing represents every linear functional. -/
theorem tensorDual_surjective :
    Function.Surjective (tensorDual : TensorSpace F ι κ →ₗ[F]
      Module.Dual F (TensorSpace F ι κ)) := by
  classical
  intro h
  refine ⟨fun i j z => h (Pi.single i (Pi.single j (Pi.single z 1))), ?_⟩
  apply LinearMap.ext
  intro t
  have ht : t = ∑ i, ∑ j, ∑ z,
      t i j z • Pi.single i (Pi.single j (Pi.single z (1 : F))) := by
    ext i j z
    simp [Finset.sum_apply, Pi.single_apply, ite_apply]
  change tensorPair (fun i j z => h (Pi.single i (Pi.single j (Pi.single z 1)))) t = h t
  conv_rhs => rw [ht]
  simp [tensorPair, map_sum, map_smul, mul_comm]

theorem tensorPair_comm (g t : TensorSpace F ι κ) : tensorPair g t = tensorPair t g := by
  simp only [tensorPair, mul_comm]

theorem boundary_alternating (g : TensorSpace F ι κ) : Alternating (boundary g) := by
  constructor
  · intro i z; exact sub_self _
  · intro i j z; exact (neg_sub _ _).symm

/-- Antisymmetrizing the separating functional multiplies its value on an
alternating target by two. -/
theorem tensorPair_boundary_left (g t : TensorSpace F ι κ) (ht : Alternating t) :
    tensorPair (boundary g) t = 2 * tensorPair g t := by
  rw [tensorPair_comm, tensorPair_boundary _ _ ht.2]
  change 2 * tensorPair t g = 2 * tensorPair g t
  rw [tensorPair_comm t g]

/-- The actual boundary map from families of perpendicular matrices. -/
def boundaryMap (C : Submodule F (MatrixSpace F ι κ)) :
    (ι → annihilator C) →ₗ[F] TensorSpace F ι κ where
  toFun a := boundary (fun i => (a i).val)
  map_add' := by intros; funext i j z; simp [boundary]; ring
  map_smul' := by intros; funext i j z; simp [boundary, mul_sub]

@[simp] theorem boundaryMap_apply (C : Submodule F (MatrixSpace F ι κ))
    (a : ι → annihilator C) : boundaryMap C a = boundary (fun i => (a i).val) := rfl

/-- Image membership for alternating targets is detected precisely by the
alternating obstructions whose slices lie in `C`. -/
theorem mem_boundary_range_iff (h2 : (2 : F) ≠ 0)
    (C : Submodule F (MatrixSpace F ι κ)) (t : TensorSpace F ι κ)
    (ht : Alternating t) :
    t ∈ LinearMap.range (boundaryMap C) ↔
      ∀ g : TensorSpace F ι κ, Alternating g → (∀ i, g i ∈ C) → tensorPair g t = 0 := by
  constructor
  · rintro ⟨a, rfl⟩ g hg hC
    exact (global_dual_criterion h2 C g hg).mpr hC
      (fun i => (a i).val) (fun i => (a i).property)
  · intro htC
    apply (mem_range_iff_dual_obstructions (boundaryMap C) t).mpr
    intro h hh
    obtain ⟨g, rfl⟩ := tensorDual_surjective h
    let γ := boundary g
    have hγ : Alternating γ := boundary_alternating g
    have hs : ∀ i, γ i ∈ C := by
      apply (global_dual_criterion h2 C γ hγ).mp
      intro a ha
      rw [show γ = boundary g from rfl, tensorPair_boundary_left _ _ (boundary_alternating a)]
      have hz := LinearMap.congr_fun hh (fun i => (⟨a i, ha i⟩ : annihilator C))
      change tensorPair g (boundary a) = 0 at hz
      rw [hz, mul_zero]
    have hz := htC γ hγ hs
    rw [show γ = boundary g from rfl, tensorPair_boundary_left g t ht] at hz
    exact (mul_eq_zero.mp hz).resolve_left h2

section ExtraImage
variable {B : Type*} [AddCommGroup B] [Module F B]

/-- Adding a family of alternating charge tensors adds exactly their
annihilation conditions to the dual test. -/
theorem mem_boundary_add_range_iff (h2 : (2 : F) ≠ 0)
    (C : Submodule F (MatrixSpace F ι κ))
    (charge : B →ₗ[F] TensorSpace F ι κ) (hcharge : ∀ b, Alternating (charge b))
    (t : TensorSpace F ι κ) (ht : Alternating t) :
    t ∈ LinearMap.range ((boundaryMap C).coprod charge) ↔
      ∀ g : TensorSpace F ι κ, Alternating g → (∀ i, g i ∈ C) →
        (∀ b, tensorPair g (charge b) = 0) → tensorPair g t = 0 := by
  constructor
  · rintro ⟨⟨a, b⟩, rfl⟩ g hg hC hb
    change tensorPair g (boundaryMap C a + charge b) = 0
    have hd := (global_dual_criterion h2 C g hg).mpr hC
      (fun i => (a i).val) (fun i => (a i).property)
    change tensorDual g (boundaryMap C a + charge b) = 0
    rw [map_add]
    change tensorPair g (boundaryMap C a) + tensorPair g (charge b) = 0
    rw [boundaryMap_apply, hd, hb b, add_zero]
  · intro htC
    apply (mem_range_iff_dual_obstructions ((boundaryMap C).coprod charge) t).mpr
    intro h hh
    obtain ⟨g, rfl⟩ := tensorDual_surjective h
    let γ := boundary g
    have hγ : Alternating γ := boundary_alternating g
    have hd (a : ι → annihilator C) : tensorPair g (boundaryMap C a) = 0 := by
      have hz := LinearMap.congr_fun hh (a, 0)
      simpa using hz
    have hc (b : B) : tensorPair g (charge b) = 0 := by
      have hz := LinearMap.congr_fun hh (0, b)
      simpa [boundaryMap, boundary, tensorDual, tensorPair] using hz
    have hs : ∀ i, γ i ∈ C := by
      apply (global_dual_criterion h2 C γ hγ).mp
      intro a ha
      rw [show γ = boundary g from rfl, tensorPair_boundary_left _ _ (boundary_alternating a)]
      rw [show tensorPair g (boundary a) = 0 from hd (fun i => ⟨a i, ha i⟩), mul_zero]
    have hcharges : ∀ b, tensorPair γ (charge b) = 0 := by
      intro b
      rw [show γ = boundary g from rfl, tensorPair_boundary_left _ _ (hcharge b), hc b, mul_zero]
    have hz := htC γ hγ hs hcharges
    rw [show γ = boundary g from rfl, tensorPair_boundary_left g t ht] at hz
    exact (mul_eq_zero.mp hz).resolve_left h2
end ExtraImage

section Elementary
variable [DecidableEq ι] [DecidableEq κ]

/-- One oriented basis wedge with one output coordinate. -/
def elementaryArray (a b : ι) (c : κ) : TensorSpace F ι κ :=
  Pi.single a (Pi.single b (Pi.single c 1)) - Pi.single b (Pi.single a (Pi.single c 1))

theorem basisTensor_apply (a b : ι) (c : κ) (i j : ι) (z : κ) :
    (Pi.single a (Pi.single b (Pi.single c (1 : F))) : TensorSpace F ι κ) i j z =
      (Pi.single a (1 : F) : ι → F) i * (Pi.single b (1 : F) : ι → F) j *
        (Pi.single c (1 : F) : κ → F) z := by
  by_cases hi : i = a <;> by_cases hj : j = b <;>
    simp [Pi.single_apply, hi, hj, ite_apply]

theorem single_one_symm (a i : ι) :
    (Pi.single a (1 : F) : ι → F) i = (Pi.single i (1 : F) : ι → F) a := by
  simp [Pi.single_apply, eq_comm]

theorem elementaryArray_apply (a b : ι) (c : κ) (i j : ι) (z : κ) :
    elementaryArray (F := F) a b c i j z =
      ((Pi.single i (1 : F) : ι → F) a * (Pi.single j (1 : F) : ι → F) b -
        (Pi.single j (1 : F) : ι → F) a * (Pi.single i (1 : F) : ι → F) b) *
          (Pi.single c (1 : F) : κ → F) z := by
  change ((_ : F) - (_ : F)) = _
  rw [basisTensor_apply, basisTensor_apply, single_one_symm a i,
    single_one_symm b j, single_one_symm b i, single_one_symm a j]
  ring

theorem tensorPair_single (g : TensorSpace F ι κ) (a b : ι) (c : κ) :
    tensorPair g (Pi.single a (Pi.single b (Pi.single c 1))) = g a b c := by
  simp [tensorPair, Pi.single_apply, ite_apply]

theorem tensorPair_elementary (g : TensorSpace F ι κ) (a b : ι) (c : κ) :
    tensorPair g (elementaryArray a b c) = g a b c - g b a c := by
  change tensorDual g (_ - _) = _
  rw [map_sub]
  exact congrArg₂ (· - ·) (tensorPair_single g a b c) (tensorPair_single g b a c)

theorem tensorPair_elementary_alternating (g : TensorSpace F ι κ)
    (hg : Alternating g) (a b : ι) (c : κ) :
    tensorPair g (elementaryArray a b c) = 2 * g a b c := by
  rw [tensorPair_elementary, hg.2]
  ring

end Elementary

section Bilinear
variable [DecidableEq ι]

/-- Bilinear maps and their complete arrays on pairs of coordinate unit vectors. -/
noncomputable def bilinearCoordinates :
    ((ι → F) →ₗ[F] (ι → F) →ₗ[F] (κ → F)) ≃ₗ[F] TensorSpace F ι κ :=
  (LinearEquiv.piRing F ((ι → F) →ₗ[F] (κ → F)) ι F).trans
    (LinearEquiv.piCongrRight (fun _ => LinearEquiv.piRing F (κ → F) ι F))

@[simp] theorem bilinearCoordinates_apply
    (b : (ι → F) →ₗ[F] (ι → F) →ₗ[F] (κ → F)) (i j : ι) (z : κ) :
    bilinearCoordinates b i j z = b (Pi.single i 1) (Pi.single j 1) z := by
  simp [bilinearCoordinates]

variable {X Z : Type*} [AddCommGroup X] [Module F X] [AddCommGroup Z] [Module F Z]

/-- Complete tensor coordinates in arbitrary specified input and output bases. -/
noncomputable def typedCoordinates
    (eX : X ≃ₗ[F] (ι → F)) (eZ : Z ≃ₗ[F] (κ → F)) :
    (X →ₗ[F] X →ₗ[F] Z) ≃ₗ[F] TensorSpace F ι κ :=
  (eX.arrowCongr (eX.arrowCongr eZ)).trans bilinearCoordinates

@[simp] theorem typedCoordinates_apply
    (eX : X ≃ₗ[F] (ι → F)) (eZ : Z ≃ₗ[F] (κ → F))
    (b : X →ₗ[F] X →ₗ[F] Z) (i j : ι) (z : κ) :
    typedCoordinates eX eZ b i j z =
      eZ (b (eX.symm (Pi.single i 1)) (eX.symm (Pi.single j 1))) z := by
  simp [typedCoordinates]

@[simp] theorem typedCoordinates_flip
    (eX : X ≃ₗ[F] (ι → F)) (eZ : Z ≃ₗ[F] (κ → F))
    (b : X →ₗ[F] X →ₗ[F] Z) (i j : ι) (z : κ) :
    typedCoordinates eX eZ b.flip i j z = typedCoordinates eX eZ b j i z := rfl

/-- Alternating bilinear maps have alternating coordinate arrays. -/
theorem typedCoordinates_alternating
    (eX : X ≃ₗ[F] (ι → F)) (eZ : Z ≃ₗ[F] (κ → F))
    (b : AlternatingBilinearMap F X Z) :
    Alternating (typedCoordinates eX eZ b.toLinearMap) := by
  constructor
  · intro i z
    rw [typedCoordinates_apply]
    simp
  · intro i j z
    rw [typedCoordinates_apply, typedCoordinates_apply]
    rw [show b.toLinearMap (eX.symm (Pi.single j 1)) (eX.symm (Pi.single i 1)) =
      -b.toLinearMap (eX.symm (Pi.single i 1)) (eX.symm (Pi.single j 1)) from b.skew _ _]
    simp

/-- Reconstruct the actual alternating bilinear map represented by an array. -/
noncomputable def alternatingFromArray
    (eX : X ≃ₗ[F] (ι → F)) (eZ : Z ≃ₗ[F] (κ → F))
    (g : TensorSpace F ι κ) : AlternatingBilinearMap F X Z where
  toLinearMap := (2 : F)⁻¹ • ((typedCoordinates eX eZ).symm g -
    ((typedCoordinates eX eZ).symm g).flip)
  map_self_eq_zero x := by simp

theorem coordinates_alternatingFromArray (h2 : (2 : F) ≠ 0)
    (eX : X ≃ₗ[F] (ι → F)) (eZ : Z ≃ₗ[F] (κ → F))
    (g : TensorSpace F ι κ) (hg : Alternating g) :
    typedCoordinates eX eZ (alternatingFromArray eX eZ g).toLinearMap = g := by
  change typedCoordinates eX eZ ((2 : F)⁻¹ • (_ - _)) = g
  rw [map_smul, map_sub, LinearEquiv.apply_symm_apply]
  funext i j z
  change (2 : F)⁻¹ * (g i j z - typedCoordinates eX eZ
    (((typedCoordinates eX eZ).symm g).flip) i j z) = g i j z
  rw [typedCoordinates_flip, LinearEquiv.apply_symm_apply, hg.2]
  field_simp
  ring

end Bilinear

end AlternatingCoordinates
end GroupWL
