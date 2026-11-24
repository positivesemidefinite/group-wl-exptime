import GroupWL.BaerSubgroups
import GroupWL.LinearSplitting

/-! # Reconstruction from the recovered quotient and evaluation maps

The maps below are linear coordinate labels, not an assumed isomorphism.
We split their exact sequences, construct the missing alternating twist, and
prove that the resulting coordinates recover the entire group law.
-/

namespace GroupWL.Recognition

variable {F A X Z : Type*} [Field F]
  [AddCommGroup A] [Module F A] [AddCommGroup X] [Module F X]
  [AddCommGroup Z] [Module F Z]

structure CoordinateMaps (b : AlternatingBilinearMap F A A)
    (Y : Submodule F (X →ₗ[F] Z)) where
  matrix : Submodule F A
  quotient : A →ₗ[F] X
  quotient_surjective : Function.Surjective quotient
  quotient_kernel : LinearMap.ker quotient = matrix
  center : Z →ₗ[F] A
  center_injective : Function.Injective center
  center_mem : ∀ z, center z ∈ matrix
  operator : matrix →ₗ[F] Y
  operator_surjective : Function.Surjective operator
  operator_kernel : LinearMap.ker operator =
    LinearMap.range (center.codRestrict matrix center_mem)
  commutator_range : ∀ a a', b a a' ∈ LinearMap.range center
  evaluation : ∀ a (m : matrix),
    b a m = center ((operator m : X →ₗ[F] Z) (quotient a))

namespace CoordinateMaps

variable {b : AlternatingBilinearMap F A A} {Y : Submodule F (X →ₗ[F] Z)}
variable (C : CoordinateMaps b Y)

def centerInMatrix : Z →ₗ[F] C.matrix := C.center.codRestrict C.matrix C.center_mem

theorem operator_center (z : Z) : C.operator (C.centerInMatrix z) = 0 := by
  have hmem : C.centerInMatrix z ∈ LinearMap.ker C.operator := by
    rw [C.operator_kernel]
    exact LinearMap.mem_range_self _ z
  exact hmem

theorem bracket_center_right (a : A) (z : Z) : b a (C.center z) = 0 := by
  have h := C.evaluation a (C.centerInMatrix z)
  rw [C.operator_center] at h
  simpa using h

theorem bracket_center_left (z : Z) (a : A) : b (C.center z) a = 0 := by
  rw [b.skew, C.bracket_center_right, neg_zero]

/-- Both exact sequences are split, with the center inclusion and quotient
projection preserved exactly. -/
theorem exists_coordinates :
    ∃ E : ((X × Y) × Z) ≃ₗ[F] A,
      (∀ u, C.quotient (E u) = u.1.1) ∧
      (∀ z, E ((0, 0), z) = C.center z) ∧
      ∀ y, ∃ hy : E ((0, y), 0) ∈ C.matrix,
        C.operator ⟨E ((0, y), 0), hy⟩ = y := by
  have hz : Function.Injective C.centerInMatrix := by
    intro z z' h
    apply C.center_injective
    exact congrArg Subtype.val h
  obtain ⟨EB, hEBq, hEBz⟩ := exists_exact_sequence_equiv C.operator C.centerInMatrix
    C.operator_surjective hz C.operator_kernel.symm
  obtain ⟨EA, hEAq, hEAB⟩ := exists_exact_sequence_equiv C.quotient C.matrix.subtype
    C.quotient_surjective Subtype.val_injective
    (by rw [Submodule.range_subtype, C.quotient_kernel])
  let E : ((X × Y) × Z) ≃ₗ[F] A :=
    (LinearEquiv.prodAssoc F X Y Z).trans
      (((LinearEquiv.refl F X).prodCongr EB).trans EA)
  refine ⟨E, ?_, ?_, ?_⟩
  · intro u
    exact hEAq u.1.1 (EB (u.1.2, u.2))
  · intro z
    change EA (0, EB (0, z)) = C.center z
    rw [hEBz, hEAB]
    rfl
  · intro y
    have heq : E ((0, y), 0) = (EB (y, 0) : A) := hEAB _
    have hy : E ((0, y), 0) ∈ C.matrix := heq ▸ (EB (y, 0)).property
    refine ⟨hy, ?_⟩
    have hsub : (⟨E ((0, y), 0), hy⟩ : C.matrix) = EB (y, 0) := Subtype.ext heq
    rw [hsub]
    exact hEBq y 0

def quotientSection (E : ((X × Y) × Z) ≃ₗ[F] A) : X →ₗ[F] A :=
  E.toLinearMap.comp ((LinearMap.inl F (X × Y) Z).comp (LinearMap.inl F X Y))

def matrixSection (E : ((X × Y) × Z) ≃ₗ[F] A) : Y →ₗ[F] A :=
  E.toLinearMap.comp ((LinearMap.inl F (X × Y) Z).comp (LinearMap.inr F X Y))

noncomputable def twist (E : ((X × Y) × Z) ≃ₗ[F] A) : AlternatingBilinearMap F X Z where
  toLinearMap :=
    { toFun x :=
        { toFun x' := C.center.leftInverse (b (quotientSection E x) (quotientSection E x'))
          map_add' x' x'' := by simp
          map_smul' r x' := by simp }
      map_add' x x' := by ext y; simp
      map_smul' r x := by ext y; simp }
  map_self_eq_zero x := by simp

theorem center_twist (E : ((X × Y) × Z) ≃ₗ[F] A) (x x' : X) :
    C.center (C.twist E x x') = b (quotientSection E x) (quotientSection E x') := by
  obtain ⟨z, hz⟩ := C.commutator_range (quotientSection E x) (quotientSection E x')
  change C.center (C.center.leftInverse (b (quotientSection E x) (quotientSection E x'))) = _
  rw [← hz, LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr C.center_injective)]

theorem bracket_coordinates
    (E : ((X × Y) × Z) ≃ₗ[F] A)
    (hquot : ∀ u, C.quotient (E u) = u.1.1)
    (hcenter : ∀ z, E ((0, 0), z) = C.center z)
    (hmatrix : ∀ y, ∃ hy : E ((0, y), 0) ∈ C.matrix,
      C.operator ⟨E ((0, y), 0), hy⟩ = y) (u v : (X × Y) × Z) :
    E ((0, 0), evaluationTwist Y (C.twist E) u.1 v.1) = b (E u) (E v) := by
  have hdecomp : ∀ w : (X × Y) × Z,
      E w = quotientSection E w.1.1 + matrixSection E w.1.2 + C.center w.2 := by
    intro w
    have hw : w = ((w.1.1, 0), 0) + ((0, w.1.2), 0) + ((0, 0), w.2) := by ext <;> simp
    conv_lhs => rw [hw, map_add, map_add, hcenter]
    rfl
  have hxy : ∀ x y,
      b (quotientSection E x) (matrixSection E y) = C.center ((y : X →ₗ[F] Z) x) := by
    intro x y
    obtain ⟨hy, hread⟩ := hmatrix y
    have h := C.evaluation (quotientSection E x) ⟨E ((0, y), 0), hy⟩
    rw [hread] at h
    change b (quotientSection E x) (matrixSection E y) =
      C.center ((y : X →ₗ[F] Z) (C.quotient (E ((x, 0), 0)))) at h
    simpa only [hquot] using h
  have hyy : ∀ y y', b (matrixSection E y) (matrixSection E y') = 0 := by
    intro y y'
    obtain ⟨hy', hread'⟩ := hmatrix y'
    have h := C.evaluation (matrixSection E y) ⟨E ((0, y'), 0), hy'⟩
    rw [hread'] at h
    change b (matrixSection E y) (matrixSection E y') =
      C.center ((y' : X →ₗ[F] Z) (C.quotient (E ((0, y), 0)))) at h
    simpa only [hquot, map_zero] using h
  have hyx : ∀ y x, b.toLinearMap (matrixSection E y) (quotientSection E x) =
      -C.center ((y : X →ₗ[F] Z) x) := by
    intro y x
    exact (b.skew _ _).trans (congrArg Neg.neg (hxy x y))
  have hxx : ∀ x x', b.toLinearMap (quotientSection E x) (quotientSection E x') =
      C.center (C.twist E x x') := fun x x' => (C.center_twist E x x').symm
  rw [hcenter, hdecomp u, hdecomp v]
  simp only [AlternatingBilinearMap.add_left, AlternatingBilinearMap.add_right,
    C.bracket_center_right, C.bracket_center_left, hyy, hxy, hyx, hxx, add_zero]
  simp only [evaluationTwist_apply, map_add, map_sub]
  abel

end CoordinateMaps

section ArbitraryGroup

variable {p : ℕ} [Fact p.Prime] {H : Type*} [Group H]
variable (D : Baer.Data p H)
variable {X Z : Type*} [AddCommGroup X] [Module (ZMod p) X]
  [AddCommGroup Z] [Module (ZMod p) Z]
variable (Y : Submodule (ZMod p) (X →ₗ[ZMod p] Z))

/-- Reconstruction of the full multiplication of the arbitrary comparison
group from the recovered quotient, center, and matrix labels. -/
theorem isomorphic_to_twist_of_coordinate_maps (C : CoordinateMaps D.bracket Y) :
    ∃ η : AlternatingBilinearMap (ZMod p) X Z,
      Nonempty (H ≃* TensorGroup (evaluationTwist Y η)) := by
  obtain ⟨E, hquot, hcenter, hmatrix⟩ := C.exists_coordinates
  refine ⟨C.twist E, ⟨?_⟩⟩
  exact (D.coordinatesMulEquiv (evaluationTwist Y (C.twist E)) E
    (C.bracket_coordinates E hquot hcenter hmatrix)).symm

/-- The constructed group isomorphism preserves the recovered quotient and
central labels exactly. These identities allow later game arguments to use
the same named coordinates after reconstruction. -/
theorem exists_isomorphism_preserving_coordinates (C : CoordinateMaps D.bracket Y) :
    ∃ (η : AlternatingBilinearMap (ZMod p) X Z)
      (f : H ≃* TensorGroup (evaluationTwist Y η)),
      (∀ h : H, (f h).fst.1 = C.quotient ⟨h⟩) ∧
      (∀ z : Z, f (C.center z).val = ⟨0, z⟩) := by
  obtain ⟨E, hquot, hcenter, hmatrix⟩ := C.exists_coordinates
  let e := D.coordinatesMulEquiv (evaluationTwist Y (C.twist E)) E
    (C.bracket_coordinates E hquot hcenter hmatrix)
  refine ⟨C.twist E, e.symm, ?_, ?_⟩
  · intro h
    change (E.symm ⟨h⟩).1.1 = C.quotient ⟨h⟩
    simpa using (hquot (E.symm ⟨h⟩)).symm
  · intro z
    apply e.injective
    rw [e.apply_symm_apply]
    change (C.center z).val = (E ((0, 0), z)).val
    rw [hcenter]

theorem exists_isomorphism_preserving_all_coordinates [NeZero (2 : ZMod p)]
    (C : CoordinateMaps D.bracket Y) :
    ∃ (η : AlternatingBilinearMap (ZMod p) X Z)
      (f : H ≃* TensorGroup (evaluationTwist Y η)),
      (∀ h : H, (f h).fst.1 = C.quotient ⟨h⟩) ∧
      (∀ z : Z, f (C.center z).val = ⟨0, z⟩) ∧
      (∀ m : C.matrix, (f m.val.val).fst = (0, C.operator m)) := by
  obtain ⟨η, f, hfq, hfc⟩ := exists_isomorphism_preserving_coordinates D Y C
  refine ⟨η, f, hfq, hfc, ?_⟩
  intro m
  have hm : C.quotient m.val = 0 := by
    have hmem : m.val ∈ LinearMap.ker C.quotient := by
      rw [C.quotient_kernel]
      exact m.property
    exact hmem
  have hxm : (f m.val.val).fst.1 = 0 := (hfq m.val.val).trans hm
  refine Prod.ext hxm ?_
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  obtain ⟨a, rfl⟩ := C.quotient_surjective x
  have heval : a.val * m.val.val * a.val⁻¹ * m.val.val⁻¹ =
      (C.center ((C.operator m : X →ₗ[ZMod p] Z) (C.quotient a))).val :=
    congrArg Baer.Data.Vector.val (C.evaluation a m)
  have hcomm : f (a.val * m.val.val * a.val⁻¹ * m.val.val⁻¹) =
      f a.val * f m.val.val * (f a.val)⁻¹ * (f m.val.val)⁻¹ := by simp
  rw [heval, hfc, TensorGroup.commutator_eq] at hcomm
  have h := congrArg TensorGroup.snd hcomm
  simpa [evaluationTwist_apply, hxm, hfq] using h.symm

end ArbitraryGroup
end GroupWL.Recognition
