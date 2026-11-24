import GroupWL.GlobalCokernel
import GroupWL.CoherentShears
import GroupWL.ResidualCancellation
import GroupWL.IncidenceBudget

/-! # Minor-normalized residual tensors for the actual incidence construction -/

namespace GroupWL.ResidualTensors

attribute [local instance] Classical.propDecidable

open ObstructionDuality AlternatingCoordinates

section CoordinateWedges
variable {F ι κ : Type*} [Field F] [Fintype ι] [Fintype κ] [DecidableEq ι]

/-- An alternating tensor supported on the wedge of two specified covectors. -/
def rankTwoArray (u v : ι → F) (w : κ → F) : TensorSpace F ι κ :=
  fun i j z => (u i * v j - v i * u j) * w z

theorem rankTwoArray_alternating (u v : ι → F) (w : κ → F) :
    Alternating (rankTwoArray u v w) := by
  constructor
  · intro i z
    simp [rankTwoArray, mul_comm]
  · intro i j z
    dsimp [rankTwoArray]
    ring

/-- Evaluation of a bilinear map is the sum of all its basis coefficients. -/
theorem bilinear_evaluation (b : (ι → F) →ₗ[F] (ι → F) →ₗ[F] (κ → F))
    (u v : ι → F) (z : κ) :
    b u v z = ∑ i, ∑ j, u i * v j * bilinearCoordinates b i j z := by
  classical
  have hu : u = ∑ i, u i • Pi.single i (1 : F) := by
    ext i
    simp [Pi.single_apply]
  have hv : v = ∑ j, v j • Pi.single j (1 : F) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hu, hv]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, bilinearCoordinates_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Ordered-pair pairing with a wedge reads twice its bilinear evaluation. -/
theorem tensorPair_rankTwo (b : (ι → F) →ₗ[F] (ι → F) →ₗ[F] (κ → F))
    (hb : Alternating (bilinearCoordinates b)) (u v : ι → F) (w : κ → F) :
    tensorPair (bilinearCoordinates b) (rankTwoArray u v w) =
      2 * ∑ z, b u v z * w z := by
  have he : rankTwoArray u v w = boundary (fun i j z => u i * v j * w z) := by
    funext i j z
    dsimp [rankTwoArray, boundary]
    ring
  rw [he, tensorPair_boundary _ _ hb.2]
  congr 1
  simp only [bilinear_evaluation, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro z _
  dsimp [matrixPair]
  ring

/-- The coordinate orthogonal space, without choosing an orthogonal projection. -/
def orthogonal (E : Submodule F (ι → F)) : Submodule F (ι → F) where
  carrier := {u | ∀ x ∈ E, coordinateFunctional u x = 0}
  zero_mem' := by intro x hx; simp [coordinateFunctional]
  add_mem' := by
    intro u v hu hv x hx
    simp only [coordinateFunctional, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply,
      add_mul, Finset.sum_add_distrib]
    change coordinateFunctional u x + coordinateFunctional v x = 0
    rw [hu x hx, hv x hx, add_zero]
  smul_mem' := by
    intro c u hu x hx
    change (∑ i, (c * u i) * x i) = 0
    simp only [mul_assoc, ← Finset.mul_sum]
    rw [show (∑ i, u i * x i) = 0 from hu x hx, mul_zero]

theorem orthogonal_antitone : Antitone (orthogonal (F := F) (ι := ι)) := by
  intro E D hED u hu x hx
  exact hu x (hED hx)

/-- The actual bilinear tensor whose coefficients are `rankTwoArray`. -/
def rankTwoTensor (u v : ι → F) (w : κ → F) :
    AlternatingBilinearMap F (ι → F) (κ → F) where
  toLinearMap := LinearMap.mk₂ F
    (fun x y => (coordinateFunctional u x * coordinateFunctional v y -
      coordinateFunctional v x * coordinateFunctional u y) • w)
    (by intros; simp only [map_add, add_mul, mul_add, add_smul]; module)
    (by intros; simp only [map_smul, smul_eq_mul]; module)
    (by intros; simp only [map_add, add_mul, mul_add, add_smul]; module)
    (by intros; simp only [map_smul, smul_eq_mul]; module)
  map_self_eq_zero x := by simp [mul_comm]

@[simp] theorem rankTwoTensor_coordinates (u v : ι → F) (w : κ → F) :
    bilinearCoordinates (rankTwoTensor u v w).toLinearMap = rankTwoArray u v w := by
  classical
  funext i j z
  rw [bilinearCoordinates_apply]
  simp [rankTwoTensor, coordinateFunctional, Pi.single_apply, rankTwoArray]

theorem rankTwoTensor_vanishes (E : Submodule F (ι → F))
    (u v : orthogonal E) (w : κ → F) (x : ι → F) (hx : x ∈ E) (y : ι → F) :
    rankTwoTensor u.val v.val w x y = 0 := by
  change ((_ : F) * (_ : F) - (_ : F) * (_ : F)) • w = 0
  rw [u.property x hx, v.property x hx]
  simp

end CoordinateWedges

section Normalization
variable {F : Type*} [Field F]

/-- The output functional prescribed by the actual invertible local minor. -/
def normalizedRadical (t : (TrivSqZeroExt F F)ˣ) : TrivSqZeroExt F F →ₗ[F] F where
  toFun z := ((↑t⁻¹ : TrivSqZeroExt F F) * z).snd
  map_add' x y := by simp [mul_add]
  map_smul' c z := by simp only [mul_smul_comm, TrivSqZeroExt.snd_smul, RingHom.id_apply]

/-- The unit minor cancels exactly; normalization reads the radical multiplier. -/
theorem normalizedRadical_mul (t : (TrivSqZeroExt F F)ˣ) (r : TrivSqZeroExt F F) :
    normalizedRadical t (r * ↑t) = r.snd := by
  change ((↑t⁻¹ : TrivSqZeroExt F F) * (r * ↑t)).snd = r.snd
  rw [mul_left_comm, Units.inv_mul, mul_one]

end Normalization

section Incidence
open IncidenceTensor IncidenceCoordinates GlobalCokernel
universe u
variable {F I J : Type u} [Field F] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {V : J → Type u} [∀ j, AddCommGroup (V j)] [∀ j, Module F (V j)]
variable (A : AffineSystem F I J V) (q : ℕ)

/-- The minor-normalizing output covector in the specified scalar-first basis. -/
noncomputable def minorReading (i : I) (ab : Pair q) (t : (TrivSqZeroExt F F)ˣ) :
    (OutputIndex A q → F) →ₗ[F] F where
  toFun z := normalizedRadical t (((outputCoordinates A q).symm z).1.1 (.inl i) ab)
  map_add' x y := by simp only [map_add, Prod.fst_add, Pi.add_apply]
  map_smul' c z := by simp only [map_smul, Prod.smul_fst, Pi.smul_apply, RingHom.id_apply]

/-- The actual minor-normalized tensor, including its single internal output. -/
noncomputable def normalizedTensor (i : I) (ab : Pair q)
    (u v : InputIndex A q → F) (t : (TrivSqZeroExt F F)ˣ) :
    AlternatingBilinearMap F (InputIndex A q → F) (OutputIndex A q → F) :=
  rankTwoTensor u v (functionalCoefficients (minorReading A q i ab t))

/-- Its pairing with any alternating tensor is the prescribed minor reading. -/
theorem normalizedTensor_pairing (i : I) (ab : Pair q)
    (u v : InputIndex A q → F) (t : (TrivSqZeroExt F F)ˣ)
    (b : AlternatingBilinearMap F (InputIndex A q → F) (OutputIndex A q → F)) :
    tensorPair (bilinearCoordinates b.toLinearMap)
      (bilinearCoordinates (normalizedTensor A q i ab u v t).toLinearMap) =
      2 * minorReading A q i ab t (b u v) := by
  rw [show normalizedTensor A q i ab u v t =
    rankTwoTensor u v (functionalCoefficients (minorReading A q i ab t)) from rfl,
    rankTwoTensor_coordinates]
  have hb : Alternating (bilinearCoordinates b.toLinearMap) := by
    constructor
    · intro i z; simp
    · intro i j z
      simpa only [bilinearCoordinates_apply, Pi.neg_apply] using
        congrFun (b.skew (Pi.single j 1) (Pi.single i 1)) z
  rw [tensorPair_rankTwo _ hb, functional_eq_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  exact mul_comm _ _

/-- A relative or global local multiplier is read exactly by this normalization. -/
theorem normalizedTensor_reads_multiplier (i : I) (ab : Pair q)
    (u v : InputIndex A q → F) (t : (TrivSqZeroExt F F)ˣ)
    (b : AlternatingBilinearMap F (InputIndex A q → F) (OutputIndex A q → F))
    (r : TrivSqZeroExt F F)
    (hr : ((outputCoordinates A q).symm (b u v)).1.1 (.inl i) ab = r * ↑t) :
    tensorPair (bilinearCoordinates b.toLinearMap)
      (bilinearCoordinates (normalizedTensor A q i ab u v t).toLinearMap) = 2 * r.snd := by
  rw [normalizedTensor_pairing]
  change 2 * normalizedRadical t _ = _
  rw [hr, normalizedRadical_mul]

/-- A chosen genuine unit minor on the retained annihilator. -/
structure MinorAt (E : Submodule F (InputIndex A q → F)) (i : I) where
  u : orthogonal E
  v : orthogonal E
  ab : Pair q
  unit : (TrivSqZeroExt F F)ˣ
  unit_eq : (↑unit : TrivSqZeroExt F F) =
    LocalMultiplier.minor (((inputCoordinates A q).symm u.val).1 (.inl i))
      (((inputCoordinates A q).symm v.val).1 (.inl i)) ab.val.1 ab.val.2

/-- Good equations are precisely those admitting the unit minors used in the
manuscript's residual construction. -/
def Good (E : Submodule F (InputIndex A q → F)) (i : I) : Prop :=
  Nonempty (MinorAt A q E i)

/-- The fixed minor determines the exact normalized tensor. -/
noncomputable def MinorAt.tensor {E : Submodule F (InputIndex A q → F)} {i : I}
    (m : MinorAt A q E i) := normalizedTensor A q i m.ab m.u.val m.v.val m.unit

theorem MinorAt.tensor_vanishes {E : Submodule F (InputIndex A q → F)} {i : I}
    (m : MinorAt A q E i) (x : InputIndex A q → F) (hx : x ∈ E) (y : InputIndex A q → F) :
    m.tensor A q x y = 0 :=
  rankTwoTensor_vanishes E m.u m.v _ x hx y

/-- Every global obstruction gives the required normalized radical reading,
for any of the allowable minor choices. -/
theorem MinorAt.global_reading {E : Submodule F (InputIndex A q → F)} {i : I}
    (m : MinorAt A q E i) (h : sourceRelations A) :
    tensorPair (obstructionCoordinates A q h)
      (bilinearCoordinates (m.tensor A q).toLinearMap) = 2 * h.val i := by
  rw [show obstructionCoordinates A q h =
    bilinearCoordinates (canonicalTwist A q (paddedSourceObstruction A h)).toLinearMap from
    (canonicalTwist_coordinates A q _).symm]
  apply normalizedTensor_reads_multiplier A q i m.ab m.u.val m.v.val m.unit
    (canonicalTwist A q (paddedSourceObstruction A h)) (sourceMultipliers A h (.inl i))
  change ((outputCoordinates A q).symm (outputCoordinates A q
    ((paddedSourceObstruction A h) ((inputCoordinates A q).symm m.u.val)
      ((inputCoordinates A q).symm m.v.val)))).1.1 (.inl i) m.ab = _
  rw [LinearEquiv.symm_apply_apply, m.unit_eq]
  change ((omega A q)
    (multiplierMap A (sourceMultipliers A h) ((inputCoordinates A q).symm m.u.val).1)
    ((inputCoordinates A q).symm m.v.val).1).1 (.inl i) m.ab = _
  rw [omega_internal]
  dsimp [multiplierMap, LocalMultiplier.minor]
  ring

/-- Minor choices are fixed once at each retained subspace. -/
noncomputable def eta (E : Submodule F (InputIndex A q → F)) (i : I) :
    AlternatingBilinearMap F (InputIndex A q → F) (OutputIndex A q → F) :=
  if h : Good A q E i then (Classical.choice h).tensor A q else AlternatingBilinearMap.zero

theorem eta_vanishes (E : Submodule F (InputIndex A q → F)) (i : I)
    (x : InputIndex A q → F) (hx : x ∈ E) (y : InputIndex A q → F) :
    eta A q E i x y = 0 := by
  classical
  unfold eta
  split_ifs with h
  · exact MinorAt.tensor_vanishes A q _ x hx y
  · rfl

theorem eta_global_reading (E : Submodule F (InputIndex A q → F)) (i : I)
    (h : sourceRelations A) :
    tensorPair (obstructionCoordinates A q h) (bilinearCoordinates (eta A q E i).toLinearMap) =
      if Good A q E i then 2 * h.val i else 0 := by
  classical
  unfold eta
  split_ifs with hg
  · exact MinorAt.global_reading A q _ h
  · simp [AlternatingBilinearMap.zero, tensorPair]

/-- The manuscript's residual, using the actual affine equation residuals and
fixed minor-normalized tensors. -/
noncomputable def residual (β : I → F) (E : Submodule F (InputIndex A q → F)) (z : ∀ j, V j) :
    AlternatingBilinearMap F (InputIndex A q → F) (OutputIndex A q → F) where
  toLinearMap := ∑ i, (β i - A.equation i z) • (eta A q E i).toLinearMap
  map_self_eq_zero x := by simp

theorem residual_vanishes (β : I → F) (E : Submodule F (InputIndex A q → F)) (z : ∀ j, V j)
    (x : InputIndex A q → F) (hx : x ∈ E) (y : InputIndex A q → F) :
    residual A q β E z x y = 0 := by
  change (∑ i, (β i - A.equation i z) • (eta A q E i).toLinearMap) x y = 0
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  have hi (i : I) : (eta A q E i).toLinearMap x y = 0 := eta_vanishes A q E i x hx y
  simp [hi]

/-- Solving every bad equation makes the global residual pairing equal to the
charge pairing, with all affine-image cancellation proved. -/
theorem residual_global_pairing (β : I → F) (E : Submodule F (InputIndex A q → F))
    (z : ∀ j, V j) (hz : ∀ i, ¬ Good A q E i → A.equation i z = β i)
    (h : sourceRelations A) :
    tensorPair (obstructionCoordinates A q h)
      (bilinearCoordinates (residual A q β E z).toLinearMap) =
      2 * ∑ i, h.val i * β i := by
  classical
  change tensorDual (obstructionCoordinates A q h)
    (bilinearCoordinates (∑ i, (β i - A.equation i z) • (eta A q E i).toLinearMap)) = _
  simp only [map_sum, map_smul, smul_eq_mul]
  change (∑ i, (β i - A.equation i z) * tensorPair (obstructionCoordinates A q h)
    (bilinearCoordinates (eta A q E i).toLinearMap)) = _
  simp only [eta_global_reading]
  have hs : (∑ i, (β i - A.equation i z) * (if Good A q E i then 2 * h.val i else 0)) =
      2 * ∑ i, h.val i * (β i - A.equation i z) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : Good A q E i
    · rw [if_pos hi]; ring
    · rw [if_neg hi, hz i hi]; simp
  rw [hs]
  congr 1
  simp only [mul_sub, Finset.sum_sub_distrib]
  have hzero := LinearMap.congr_fun ((mem_sourceRelations_iff A h.val).mp h.property) z
  change (∑ i, h.val i * A.equation i z) = 0 at hzero
  rw [hzero, sub_zero]

/-- Every admissible actual residual admits a genuine global shear lift. -/
theorem residual_global_lift (h2 : (2 : F) ≠ 0) (hq : 2 ≤ q)
    (β : I → F) (E : Submodule F (InputIndex A q → F)) (z : ∀ j, V j)
    (hz : ∀ i, ¬ Good A q E i → A.equation i z = β i) :
    ∃ α : (InputIndex A q → F) →ₗ[F] MatrixEvaluationGroup.operatorSpace (C A q (by omega)),
      ∀ x y, shearCoboundary _ α x y =
        canonicalTwist A q (epsilonCharge A q hq β) x y - residual A q β E z x y := by
  let b := (canonicalTwist A q (epsilonCharge A q hq β)).toLinearMap -
    (residual A q β E z).toLinearMap
  have hb : Alternating (bilinearCoordinates b) := by
    constructor
    · intro i k; simp [b]
    · intro i j k
      simp only [b, bilinearCoordinates_apply, LinearMap.sub_apply, Pi.sub_apply]
      have hc := congrFun ((canonicalTwist A q (epsilonCharge A q hq β)).skew
        (Pi.single j 1) (Pi.single i 1)) k
      have hr := congrFun ((residual A q β E z).skew (Pi.single j 1) (Pi.single i 1)) k
      change _ = -_ at hc hr
      linear_combination hc - hr
  have hm : bilinearCoordinates b ∈ LinearMap.range (boundaryMap (C A q (by omega))) := by
    apply (mem_boundary_range_iff h2 _ _ hb).mpr
    intro g hg hs
    obtain ⟨h, rfl⟩ := coordinate_obstruction_classification A q h2 hq g hg hs
    change tensorDual (obstructionCoordinates A q h) (bilinearCoordinates b) = 0
    change tensorDual (obstructionCoordinates A q h) (bilinearCoordinates
      ((canonicalTwist A q (epsilonCharge A q hq β)).toLinearMap -
        (residual A q β E z).toLinearMap)) = 0
    rw [map_sub (bilinearCoordinates (F := F) (ι := InputIndex A q) (κ := OutputIndex A q)),
      map_sub (tensorDual (obstructionCoordinates A q h))]
    change tensorPair (obstructionCoordinates A q h) _ - tensorPair (obstructionCoordinates A q h) _ = 0
    rw [canonicalTwist_coordinates]
    change tensorPair (obstructionCoordinates A q h) (chargeCoordinates A q hq β) - _ = 0
    rw [obstruction_charge_pairing, residual_global_pairing A q β E z hz h, sub_self]
  obtain ⟨α, hα⟩ := (CoordinateShears.mem_boundary_range_iff_shear _ b).mp hm
  exact ⟨α, fun x y => LinearMap.congr_fun (LinearMap.congr_fun hα x) y⟩

end Incidence

end GroupWL.ResidualTensors
