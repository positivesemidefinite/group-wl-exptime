import GroupWL.IncidenceCoordinates
import GroupWL.AlternatingCoordinates
import GroupWL.CoordinateShears

/-! # The actual global obstruction quotient

All spaces and charges in this file are those of the affine-incidence
construction, in the manuscript's scalar-first coordinates.
-/

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace GroupWL
namespace GlobalCokernel

open IncidenceTensor IncidenceCoordinates IncidenceGroup ObstructionDuality AlternatingCoordinates
universe u
variable {F I J : Type u} [Field F] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {V : J → Type u} [∀ j, AddCommGroup (V j)] [∀ j, Module F (V j)]
variable (A : AffineSystem F I J V) (q : ℕ)

noncomputable abbrev tensorCoordinates :=
  typedCoordinates (inputCoordinates A q) (outputCoordinates A q)

noncomputable abbrev C (hq : 0 < q) :=
  coordinateObstruction A q hq (inputCoordinates A q) (outputCoordinates A q)

noncomputable def chargeCoordinates (hq : 2 ≤ q) : (I → F) →ₗ[F]
    TensorSpace F (InputIndex A q) (OutputIndex A q) :=
  (tensorCoordinates A q).toLinearMap.comp (chargeBilinear A q hq)

noncomputable def obstructionCoordinates (h : sourceRelations A) :
    TensorSpace F (InputIndex A q) (OutputIndex A q) :=
  tensorCoordinates A q (paddedSourceObstruction A h).toLinearMap

@[simp] theorem operatorCoordinates_apply
    (f : PaddedInput A q →ₗ[F] PaddedOutput A q) (i : InputIndex A q) (z : OutputIndex A q) :
    operatorCoordinates A q (inputCoordinates A q) (outputCoordinates A q) f i z =
      outputCoordinates A q (f ((inputCoordinates A q).symm (Pi.single i 1))) z := rfl

/-- Coordinate slice membership is equivalent to membership of all actual
operator slices. Extension from basis inputs uses linearity, not a game assumption. -/
theorem coordinate_slices_iff (hq : 0 < q)
    (b : PaddedInput A q →ₗ[F] PaddedInput A q →ₗ[F] PaddedOutput A q) :
    (∀ i, tensorCoordinates A q b i ∈ C A q hq) ↔
      ∀ x, b x ∈ constructionObstructionSpace A q hq := by
  classical
  let e := operatorCoordinates A q (inputCoordinates A q) (outputCoordinates A q)
  have he (i : InputIndex A q) :
      e (b ((inputCoordinates A q).symm (Pi.single i 1))) = tensorCoordinates A q b i := by
    funext j z
    exact operatorCoordinates_apply A q _ j z
  constructor
  · intro hs x
    let T := e.toLinearMap.comp (b.comp (inputCoordinates A q).symm.toLinearMap)
    have hT : T (inputCoordinates A q x) ∈ C A q hq := by
      rw [LinearMap.pi_apply_eq_sum_univ]
      apply Submodule.sum_mem
      intro i _
      apply Submodule.smul_mem
      have hi := hs i
      rw [← he i] at hi
      have hui : (fun j : InputIndex A q => if i = j then (1 : F) else 0) = Pi.single i 1 := by
        funext j
        simp [Pi.single_apply, eq_comm]
      change e (b ((inputCoordinates A q).symm (fun j => if i = j then 1 else 0))) ∈ _
      rw [hui]
      exact hi
    have hx : e (b x) ∈ C A q hq := by simpa [T] using hT
    obtain ⟨f, hf, hef⟩ := hx
    exact e.injective hef ▸ hf
  · intro hs i
    rw [← he i]
    exact ⟨b ((inputCoordinates A q).symm (Pi.single i 1)), hs _, rfl⟩

/-- Every alternating coordinate obstruction comes from the actual source
transpose kernel. All construction-specific hypotheses have been derived. -/
theorem coordinate_obstruction_classification (h2 : (2 : F) ≠ 0) (hq : 2 ≤ q)
    (g : TensorSpace F (InputIndex A q) (OutputIndex A q))
    (hg : Alternating g) (hs : ∀ i, g i ∈ C A q (by omega)) :
    ∃ h : sourceRelations A, g = obstructionCoordinates A q h := by
  let b := alternatingFromArray (inputCoordinates A q) (outputCoordinates A q) g
  have hb : tensorCoordinates A q b.toLinearMap = g :=
    coordinates_alternatingFromArray h2 _ _ g hg
  have hbs : ∀ x, b.toLinearMap x ∈ constructionObstructionSpace A q (by omega) := by
    apply (coordinate_slices_iff A q (by omega) b.toLinearMap).mp
    rwa [hb]
  obtain ⟨h, hh⟩ := padded_obstruction_classification A hq b hbs
  refine ⟨h, ?_⟩
  rw [← hb]
  congr 1
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  exact hh x y

theorem obstructionCoordinates_slices (hq : 0 < q) (h : sourceRelations A) :
    ∀ i, obstructionCoordinates A q h i ∈ C A q hq :=
  (coordinate_slices_iff A q hq _).mpr (paddedSourceObstruction_slice_mem A h hq)

theorem obstructionCoordinates_alternating (h : sourceRelations A) :
    Alternating (obstructionCoordinates A q h) :=
  typedCoordinates_alternating _ _ _

/-- The chosen scalar coordinate remains the corresponding coefficient after
passing to the explicit input basis. -/
theorem scalarCoordinate_from_coordinates (v : I ⊕ J) (a : Fin q)
    (x : InputIndex A q → F) :
    scalarCoordinate A q v a ((inputCoordinates A q).symm x) = x (scalarIndex A q v a) := by
  change (((inputCoordinates A q).symm x).1 v a).fst = _
  rw [← inputCoordinates_scalar, LinearEquiv.apply_symm_apply]

/-- Each actual charge has the exact elementary wedge coordinate array. -/
theorem unitCharge_coordinates (hq : 2 ≤ q) (i : I) :
    tensorCoordinates A q (unitCharge A q hq i).toLinearMap =
      elementaryArray
        (scalarIndex A q (.inl i) (firstPair q hq).1.1)
        (scalarIndex A q (.inl i) (firstPair q hq).1.2)
        (chargeIndex A q hq i) := by
  classical
  funext a b z
  rw [typedCoordinates_apply]
  change outputCoordinates A q
    (((_ : F) * (_ : F) - (_ : F) * (_ : F)) • chargeOutput A q hq i) z = _
  rw [map_smul]
  simp only [Pi.smul_apply, smul_eq_mul, scalarCoordinate_from_coordinates,
    outputCoordinates_chargeOutput]
  exact (elementaryArray_apply _ _ _ a b z).symm

/-- The real charge map is the sum of its specified elementary basis wedges. -/
theorem chargeCoordinates_eq_sum (hq : 2 ≤ q) (β : I → F) :
    chargeCoordinates A q hq β = ∑ i, β i •
      elementaryArray
        (scalarIndex A q (.inl i) (firstPair q hq).1.1)
        (scalarIndex A q (.inl i) (firstPair q hq).1.2)
        (chargeIndex A q hq i) := by
  simp [chargeCoordinates, chargeBilinear, unitCharge_coordinates]

theorem chargeCoordinates_alternating (hq : 2 ≤ q) (β : I → F) :
    Alternating (chargeCoordinates A q hq β) :=
  typedCoordinates_alternating (inputCoordinates A q) (outputCoordinates A q) (epsilonCharge A q hq β)

/-- The ordered-pair tensor pairing reads twice the source charge pairing.
The factor is explicit and is inverted only in odd characteristic. -/
theorem obstruction_charge_pairing (hq : 2 ≤ q) (h : sourceRelations A) (β : I → F) :
    tensorPair (obstructionCoordinates A q h) (chargeCoordinates A q hq β) =
      2 * ∑ i, h.val i * β i := by
  rw [chargeCoordinates_eq_sum]
  change tensorDual (obstructionCoordinates A q h) (∑ i, β i • _) = _
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  have hr (i : I) : obstructionCoordinates A q h
      (scalarIndex A q (.inl i) (firstPair q hq).1.1)
      (scalarIndex A q (.inl i) (firstPair q hq).1.2)
      (chargeIndex A q hq i) = h.val i := by
    unfold obstructionCoordinates
    rw [typedCoordinates_apply, inputCoordinates_symm_scalar, inputCoordinates_symm_scalar,
      outputCoordinates_charge]
    exact source_obstruction_charge_reading A hq h i
  change (∑ i, β i * tensorPair (obstructionCoordinates A q h) _) = _
  simp only [tensorPair_elementary_alternating _ (obstructionCoordinates_alternating A q h), hr]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The source transpose relations detect the actual affine image. -/
theorem mem_source_range_iff (β : I → F) :
    β ∈ LinearMap.range A.linearMap ↔
      ∀ h : sourceRelations A, ∑ i, h.val i * β i = 0 := by
  rw [mem_range_iff_coordinate_relations]
  constructor
  · intro hb h
    apply hb h.val
    intro z
    have hz := LinearMap.congr_fun ((mem_sourceRelations_iff A h.val).mp h.property) z
    exact hz
  · intro hb h hh
    apply hb ⟨h, (mem_sourceRelations_iff A h).mpr ?_⟩
    apply LinearMap.ext
    intro z
    exact hh z

/-- The charge coboundary theorem for the actual constructed tensor space. -/
theorem charge_mem_boundary_range_iff (h2 : (2 : F) ≠ 0) (hq : 2 ≤ q) (β : I → F) :
    chargeCoordinates A q hq β ∈ LinearMap.range (boundaryMap (C A q (by omega))) ↔
      β ∈ LinearMap.range A.linearMap := by
  rw [mem_boundary_range_iff h2 _ _ (chargeCoordinates_alternating A q hq β),
    mem_source_range_iff A]
  constructor
  · intro hb h
    have hz := hb (obstructionCoordinates A q h)
      (obstructionCoordinates_alternating A q h) (obstructionCoordinates_slices A q (by omega) h)
    rw [obstruction_charge_pairing] at hz
    exact (mul_eq_zero.mp hz).resolve_left h2
  · intro hb g hg hs
    obtain ⟨h, rfl⟩ := coordinate_obstruction_classification A q h2 hq g hg hs
    rw [obstruction_charge_pairing, hb h, mul_zero]

@[simp] theorem obstructionCoordinates_zero :
    obstructionCoordinates A q (0 : sourceRelations A) = 0 := by
  have hr : sourceMultipliers A (0 : sourceRelations A) = 0 := by
    funext v
    cases v with
    | inl i => rfl
    | inr j =>
      apply TrivSqZeroExt.ext
      · rfl
      · apply Subtype.ext
        rfl
  have hm : multiplierMap (q := q) A (sourceMultipliers A (0 : sourceRelations A)) = 0 := by
    rw [hr]
    apply LinearMap.ext
    intro x
    funext v k
    exact zero_mul _
  have hz : (paddedSourceObstruction (q := q) A (0 : sourceRelations A)).toLinearMap = 0 := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change ((omega A q) (multiplierMap A (sourceMultipliers A (0 : sourceRelations A)) x.1) y.1, 0) = 0
    rw [hm]
    simp
  unfold obstructionCoordinates
  rw [hz, map_zero]

/-- Every alternating tensor has a representative among the actual charge tensors. -/
theorem every_tensor_charge_representative (h2 : (2 : F) ≠ 0) (hq : 2 ≤ q)
    (t : TensorSpace F (InputIndex A q) (OutputIndex A q)) (ht : Alternating t) :
    ∃ β : I → F, t - chargeCoordinates A q hq β ∈
      LinearMap.range (boundaryMap (C A q (by omega))) := by
  have ht' : t ∈ LinearMap.range ((boundaryMap (C A q (by omega))).coprod
      (chargeCoordinates A q hq)) := by
    apply (mem_boundary_add_range_iff h2 _ _ (chargeCoordinates_alternating A q hq) t ht).mpr
    intro g hg hs hc
    obtain ⟨h, rfl⟩ := coordinate_obstruction_classification A q h2 hq g hg hs
    have hh : h = 0 := by
      apply Subtype.ext
      funext i
      have hi := hc (Pi.single i 1)
      rw [obstruction_charge_pairing] at hi
      have hsum := (mul_eq_zero.mp hi).resolve_left h2
      simpa [Pi.single_apply] using hsum
    rw [hh, obstructionCoordinates_zero]
    simp [tensorPair]
  obtain ⟨⟨a, β⟩, he⟩ := ht'
  refine ⟨β, a, ?_⟩
  change boundaryMap (C A q (by omega)) a + chargeCoordinates A q hq β = t at he
  exact (eq_sub_iff_add_eq).mpr he

/-- The actual canonical coordinate twist in the constructed group. -/
noncomputable abbrev canonicalTwist
    (ε : AlternatingBilinearMap F (PaddedInput A q) (PaddedOutput A q)) :=
  twistCoordinates A q (inputCoordinates A q) (outputCoordinates A q) ε

@[simp] theorem canonicalTwist_coordinates
    (ε : AlternatingBilinearMap F (PaddedInput A q) (PaddedOutput A q)) :
    bilinearCoordinates (canonicalTwist A q ε).toLinearMap =
      tensorCoordinates A q ε.toLinearMap := by
  funext i j z
  rfl

/-- Full charge coboundary theorem, stated for actual shears into the operator
space of the constructed group, rather than for a coordinate proxy. -/
theorem charge_is_shear_iff (h2 : (2 : F) ≠ 0) (hq : 2 ≤ q) (β : I → F) :
    (∃ α : (InputIndex A q → F) →ₗ[F] MatrixEvaluationGroup.operatorSpace (C A q (by omega)),
      ∀ x y, shearCoboundary _ α x y = canonicalTwist A q (epsilonCharge A q hq β) x y) ↔
      β ∈ LinearMap.range A.linearMap := by
  rw [← charge_mem_boundary_range_iff A q h2 hq β]
  have hc : chargeCoordinates A q hq β =
      bilinearCoordinates (canonicalTwist A q (epsilonCharge A q hq β)).toLinearMap := by
    rw [canonicalTwist_coordinates]
    rfl
  rw [hc, CoordinateShears.mem_boundary_range_iff_shear]
  constructor
  · rintro ⟨α, hα⟩
    refine ⟨α, ?_⟩
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    exact hα x
  · rintro ⟨α, hα⟩
    exact ⟨α, fun x y => LinearMap.congr_fun (LinearMap.congr_fun hα x) y⟩

/-- Every twist on the full padded coordinate space is the sum of an actual
charge twist and an actual shear coboundary. -/
theorem every_twist_charge_representative (h2 : (2 : F) ≠ 0) (hq : 2 ≤ q)
    (ε : AlternatingBilinearMap F (InputIndex A q → F) (OutputIndex A q → F)) :
    ∃ (β : I → F)
      (α : (InputIndex A q → F) →ₗ[F] MatrixEvaluationGroup.operatorSpace (C A q (by omega))),
      ∀ x y, shearCoboundary _ α x y =
        ε x y - canonicalTwist A q (epsilonCharge A q hq β) x y := by
  have hε : Alternating (bilinearCoordinates ε.toLinearMap) := by
    constructor
    · intro i z
      simp
    · intro i j z
      simpa only [bilinearCoordinates_apply, Pi.neg_apply] using
        congrFun (ε.skew (Pi.single j 1) (Pi.single i 1)) z
  obtain ⟨β, hβ⟩ := every_tensor_charge_representative A q h2 hq
    (bilinearCoordinates ε.toLinearMap) hε
  have hc : chargeCoordinates A q hq β =
      bilinearCoordinates (canonicalTwist A q (epsilonCharge A q hq β)).toLinearMap := by
    rw [canonicalTwist_coordinates]
    rfl
  rw [hc, ← map_sub, CoordinateShears.mem_boundary_range_iff_shear] at hβ
  obtain ⟨α, hα⟩ := hβ
  refine ⟨β, α, ?_⟩
  intro x y
  exact LinearMap.congr_fun (LinearMap.congr_fun hα x) y

end GlobalCokernel
end GroupWL
