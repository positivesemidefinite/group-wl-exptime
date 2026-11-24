import GroupWL.IncidenceTensor
import GroupWL.LocalMultiplier
import GroupWL.ObstructionDuality

/-!
# Global multipliers of the incidence tensor

This file applies the local rigidity theorem to the actual tensor constructed
from the affine system. The input space is unrestricted, so two scalar unit
vectors at each vertex supply the unit minor directly.
-/

namespace GroupWL
namespace IncidenceTensor

universe u
variable {F I J : Type u} [Field F] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {V : J → Type u} [∀ j, AddCommGroup (V j)] [∀ j, Module F (V j)]
variable (A : AffineSystem F I J V) {q : ℕ}

/-- A scalar unit at a single vertex coordinate of the actual input space. -/
noncomputable def unitInput (v : I ⊕ J) (a : Fin q) : OldInput A q := by
  classical
  exact Pi.single v (Pi.single a 1)

@[simp] theorem unitInput_self (v : I ⊕ J) (a b : Fin q) :
    unitInput A v a v b = if b = a then 1 else 0 := by
  classical
  simp [unitInput, Pi.single_apply]

/-- The diagonal alternating identity gives every internal wedge relation. -/
theorem internal_diagonal_relation
    (P : OldInput A q →ₗ[F] OldInput A q)
    (hdiag : ∀ x, omega A q (P x) x = 0)
    (x : OldInput A q) (v : I ⊕ J) (a b : Fin q) :
    P x v a * x v b = P x v b * x v a := by
  rcases lt_trichotomy a b with hab | hab | hab
  · have h := congrArg (fun z : OldOutput A q => z.1 v ⟨(a, b), hab⟩) (hdiag x)
    change P x v a * x v b - x v a * P x v b = 0 at h
    rw [mul_comm (x v a)] at h
    exact sub_eq_zero.mp h
  · subst b
    rfl
  · have h := congrArg (fun z : OldOutput A q => z.1 v ⟨(b, a), hab⟩) (hdiag x)
    change P x v b * x v a - x v b * P x v a = 0 at h
    rw [mul_comm (x v b)] at h
    exact (sub_eq_zero.mp h).symm

/-- Every vertex has one unique multiplier when at least two coordinates are
available. This is a conclusion about the concrete incidence tensor. -/
theorem global_vertex_multiplier
    (P : OldInput A q →ₗ[F] OldInput A q)
    (hdiag : ∀ x, omega A q (P x) x = 0)
    (a b : Fin q) (hab : a ≠ b) (v : I ⊕ J) :
    ∃! r : RingAt A v, ∀ x k, P x v k = r * x v k := by
  let g : OldInput A q →ₗ[F] (Fin q → RingAt A v) := LinearMap.proj v
  let f := g.comp P
  apply LocalMultiplier.existsUnique_multiplier f.toAddMonoidHom g.toAddMonoidHom
    (fun x i j => internal_diagonal_relation A P hdiag x v i j)
    (unitInput A v a) (unitInput A v b) a b
  change IsUnit (LocalMultiplier.minor
    (unitInput A v a v) (unitInput A v b v) a b)
  simp [LocalMultiplier.minor, unitInput_self, hab, Ne.symm hab]

/-- Multipliers at the endpoints of every actual incidence agree under the
specified algebra maps. -/
theorem global_incidence_compatibility
    (P : OldInput A q →ₗ[F] OldInput A q)
    (hdiag : ∀ x, omega A q (P x) x = 0)
    (r : ∀ v, RingAt A v)
    (hr : ∀ v x k, P x v k = r v * x v k)
    (e : Incidence A) (a b : Fin q) :
    r (.inl e.1.1) = endpointMap A e (r (.inr e.1.2)) := by
  classical
  let x := unitInput A (.inl e.1.1) a + unitInput A (.inr e.1.2) b
  have hi : x (.inl e.1.1) a = 1 := by simp [x, unitInput]
  have hj : x (.inr e.1.2) b = 1 := by simp [x, unitInput]
  have h := congrArg (fun z : OldOutput A q => z.2 e (a, b)) (hdiag x)
  change P x (.inl e.1.1) a * endpointMap A e (x (.inr e.1.2) b) -
    x (.inl e.1.1) a * endpointMap A e (P x (.inr e.1.2) b) = 0 at h
  rw [hr, hr, hi, hj, mul_one, mul_one, map_one, mul_one, one_mul] at h
  exact sub_eq_zero.mp h

/-- A selected scalar-coordinate kernel forces the scalar part of the
multiplier at that selected vertex to vanish. -/
theorem selected_multiplier_scalar_zero
    (P : OldInput A q →ₗ[F] OldInput A q)
    (anchors : Set ((I ⊕ J) × Fin q))
    (hP : ∀ x, P x ∈ chosenKernel A q anchors)
    (r : ∀ v, RingAt A v)
    (hr : ∀ v x k, P x v k = r v * x v k)
    (v : I ⊕ J) (a : Fin q) (ha : (v, a) ∈ anchors) :
    (r v).fst = 0 := by
  have h := hP (unitInput A v a) (v, a) ha
  change (P (unitInput A v a) v a).fst = 0 at h
  rw [hr, unitInput_self, if_pos rfl, mul_one] at h
  exact h

/-- Oriented incidence edges; their equivalence closure is ordinary component
connectivity of the bipartite incidence graph. -/
def IncidenceStep (v w : I ⊕ J) : Prop :=
  ∃ e : Incidence A, v = .inl e.1.1 ∧ w = .inr e.1.2

/-- The chosen scalar coordinates meet every incidence component. -/
def AnchorsCover (anchors : Set ((I ⊕ J) × Fin q)) : Prop :=
  ∀ v, ∃ va ∈ anchors, Relation.EqvGen (IncidenceStep A) va.1 v

/-- Incidence-compatible multipliers have the same scalar part throughout a
connected component. -/
theorem scalar_eq_of_connected
    (r : ∀ v, RingAt A v)
    (hr : ∀ e : Incidence A, r (.inl e.1.1) = endpointMap A e (r (.inr e.1.2)))
    {v w : I ⊕ J} (h : Relation.EqvGen (IncidenceStep A) v w) :
    (r v).fst = (r w).fst := by
  induction h with
  | rel v w h =>
    obtain ⟨e, rfl, rfl⟩ := h
    have he := congrArg TrivSqZeroExt.fst (hr e)
    simpa [endpointMap] using he
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

/-- Meeting every incidence component kills every multiplier's scalar part;
no arbitrary choice of a preferred root vertex is built into the theorem. -/
theorem all_multiplier_scalars_zero
    (P : OldInput A q →ₗ[F] OldInput A q)
    (hdiag : ∀ x, omega A q (P x) x = 0)
    (anchors : Set ((I ⊕ J) × Fin q)) (hcover : AnchorsCover A anchors)
    (hP : ∀ x, P x ∈ chosenKernel A q anchors)
    (r : ∀ v, RingAt A v)
    (hr : ∀ v x k, P x v k = r v * x v k)
    (a : Fin q) : ∀ v, (r v).fst = 0 := by
  intro v
  obtain ⟨va, hva, hpath⟩ := hcover v
  have he := scalar_eq_of_connected A r
    (fun e => global_incidence_compatibility A P hdiag r hr e a a) hpath
  rw [← he]
  exact selected_multiplier_scalar_zero A P anchors hP r hr va.1 va.2 hva

/-- Radical components of compatible readout multipliers give exactly the
linear relations among incident coefficient forms. -/
theorem compatible_radical_relation
    (r : ∀ v, RingAt A v)
    (hr : ∀ e : Incidence A, r (.inl e.1.1) = endpointMap A e (r (.inr e.1.2)))
    (j : J) :
    ∑ i : Neighbors A j, (r (.inl i.val)).snd • A.coefficient i.val j = 0 := by
  have hk := (r (.inr j)).snd.property
  change (∑ i : Neighbors A j,
    (r (.inr j)).snd.val i • A.coefficient i.val j) = 0 at hk
  have hi (i : Neighbors A j) : (r (.inr j)).snd.val i = (r (.inl i.val)).snd := by
    have he := congrArg TrivSqZeroExt.snd (hr ⟨(i.val, j), i.property⟩)
    simpa [endpointMap, readoutProjection] using he.symm
  simpa only [hi] using hk

/-- The same radical relation written over all equations; coefficients outside
the scope vanish by the affine-system definition. -/
theorem compatible_radical_full_relation
    (r : ∀ v, RingAt A v)
    (hr : ∀ e : Incidence A, r (.inl e.1.1) = endpointMap A e (r (.inr e.1.2)))
    (j : J) :
    ∑ i, (r (.inl i)).snd • A.coefficient i j = 0 := by
  classical
  have hsum := Fintype.sum_subtype_add_sum_subtype (fun i => j ∈ A.scope i)
    (fun i => (r (.inl i)).snd • A.coefficient i j)
  have hz : (∑ i : {i // j ∉ A.scope i},
      (r (.inl i.val)).snd • A.coefficient i.val j) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [A.coefficient_outside i.val j i.property, smul_zero]
  rw [show (∑ i : {i // j ∈ A.scope i},
      (r (.inl i.val)).snd • A.coefficient i.val j) = 0 from
    compatible_radical_relation A r hr j, hz, add_zero] at hsum
  exact hsum.symm

/-- The actual source obstruction space, expressed by its readout relations. -/
def sourceRelations : Submodule F (I → F) where
  carrier := {h | ∀ j, ∑ i, h i • A.coefficient i j = 0}
  zero_mem' := by simp
  add_mem' := by
    intro h k hh hk j
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, hh j, hk j, add_zero]
  smul_mem' := by
    intro c h hh j
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, hh j, smul_zero]

/-- The readout relations are precisely the kernel of the transpose of the
source affine matrix under its fixed equation-coordinate pairing. -/
theorem mem_sourceRelations_iff (h : I → F) :
    h ∈ sourceRelations A ↔ A.linearMap.dualMap (coordinateFunctional h) = 0 := by
  classical
  constructor
  · intro hh
    apply LinearMap.ext
    intro z
    change (∑ i, h i * ∑ j, A.coefficient i j (z j)) = 0
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j _
    have hj := LinearMap.congr_fun (hh j) (z j)
    simpa using hj
  · intro hh j
    apply LinearMap.ext
    intro z
    have hz := LinearMap.congr_fun hh (Pi.single j z)
    have hsingle (i : I) : A.equation i (Pi.single j z) = A.coefficient i j z := by
      change (∑ k, A.coefficient i k (Pi.single j z k)) = _
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hkj
        simp [Pi.single_eq_of_ne hkj]
      · simp
    change (∑ i, h i * A.equation i (Pi.single j z)) = 0 at hz
    simpa only [hsingle, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      LinearMap.zero_apply] using hz

/-- Incidence compatibility alone forces the equation radical coefficients
into the source obstruction kernel. -/
theorem compatible_radicals_mem_sourceRelations
    (r : ∀ v, RingAt A v)
    (hr : ∀ e : Incidence A, r (.inl e.1.1) = endpointMap A e (r (.inr e.1.2))) :
    (fun i => (r (.inl i)).snd) ∈ sourceRelations A :=
  compatible_radical_full_relation A r hr

/-- Assembling the global rigidity conclusions requires no local-multiplier
hypothesis: they follow from the original diagonal tensor equations. -/
theorem global_multiplier_classification
    (P : OldInput A q →ₗ[F] OldInput A q)
    (hdiag : ∀ x, omega A q (P x) x = 0)
    (anchors : Set ((I ⊕ J) × Fin q)) (hcover : AnchorsCover A anchors)
    (hP : ∀ x, P x ∈ chosenKernel A q anchors)
    (a b : Fin q) (hab : a ≠ b) :
    ∃ r : ∀ v, RingAt A v,
      (∀ v x k, P x v k = r v * x v k) ∧
      (∀ e : Incidence A, r (.inl e.1.1) = endpointMap A e (r (.inr e.1.2))) ∧
      (∀ v, (r v).fst = 0) ∧
      (fun i => (r (.inl i)).snd) ∈ sourceRelations A := by
  classical
  choose r hr using fun v => (global_vertex_multiplier A P hdiag a b hab v).exists
  have he := fun e => global_incidence_compatibility A P hdiag r hr e a a
  exact ⟨r, hr, he,
    all_multiplier_scalars_zero A P hdiag anchors hcover hP r hr a,
    compatible_radicals_mem_sourceRelations A r he⟩

theorem incidenceStep_eq_incidenceRelation : IncidenceStep A = incidenceRelation A := by
  funext v w
  apply propext
  cases v <;> cases w <;> simp [IncidenceStep, incidenceRelation, Incidence]

/-- Anchoring every vertex satisfies the cover condition used by the
classification theorem, without any component-representative computation. -/
theorem componentAnchors_cover (q : ℕ) (hq : 0 < q) :
    AnchorsCover A (componentAnchors A q hq) := by
  intro v
  exact ⟨(v, ⟨0, hq⟩), ⟨v, rfl⟩, Relation.EqvGen.refl v⟩

/-- Source relations restricted to actual incidences. -/
theorem source_relation_on_neighbors (h : sourceRelations A) (j : J) :
    (∑ i : Neighbors A j, h.val i.val • A.coefficient i.val j) = 0 := by
  classical
  have hs := Fintype.sum_subtype_add_sum_subtype (fun i => j ∈ A.scope i)
    (fun i => h.val i • A.coefficient i j)
  have hz : (∑ i : {i // j ∉ A.scope i}, h.val i.val • A.coefficient i.val j) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [A.coefficient_outside i.val j i.property, smul_zero]
  rw [hz, add_zero, h.property j] at hs
  exact hs

/-- The radical multiplier family associated to a source obstruction. -/
def sourceMultipliers (h : sourceRelations A) : ∀ v, RingAt A v
  | .inl i => TrivSqZeroExt.inr (h.val i)
  | .inr j => TrivSqZeroExt.inr
      ⟨(fun i => h.val i.val), source_relation_on_neighbors A h j⟩

@[simp] theorem sourceMultipliers_scalar (h : sourceRelations A) (v : I ⊕ J) :
    (sourceMultipliers A h v).fst = 0 := by cases v <;> rfl

theorem sourceMultipliers_compatible (h : sourceRelations A) (e : Incidence A) :
    sourceMultipliers A h (.inl e.1.1) =
      endpointMap A e (sourceMultipliers A h (.inr e.1.2)) := by
  simp [sourceMultipliers, endpointMap, readoutProjection]

/-- Pointwise multiplication by a prescribed family of vertex multipliers. -/
def multiplierMap (r : ∀ v, RingAt A v) : OldInput A q →ₗ[F] OldInput A q where
  toFun x v k := r v * x v k
  map_add' := by
    intro x y
    funext v k
    exact mul_add _ _ _
  map_smul' := by
    intro c x
    funext v k
    change r v * (c • x v k) = c • (r v * x v k)
    exact mul_smul_comm c (r v) (x v k)

/-- Incidence compatibility makes the multiplied tensor alternating. -/
theorem multiplier_diagonal_zero (r : ∀ v, RingAt A v)
    (hr : ∀ e : Incidence A, r (.inl e.1.1) = endpointMap A e (r (.inr e.1.2)))
    (x : OldInput A q) : omega A q (multiplierMap A r x) x = 0 := by
  apply Prod.ext
  · funext v ab
    change (r v * x v ab.1.1) * x v ab.1.2 -
      x v ab.1.1 * (r v * x v ab.1.2) = 0
    ring
  · funext e ab
    change (r (.inl e.1.1) * x (.inl e.1.1) ab.1) *
      endpointMap A e (x (.inr e.1.2) ab.2) -
      x (.inl e.1.1) ab.1 *
        endpointMap A e (r (.inr e.1.2) * x (.inr e.1.2) ab.2) = 0
    rw [map_mul, ← hr e]
    ring

/-- Every source obstruction gives a genuine alternating tensor. -/
def sourceObstruction (h : sourceRelations A) :
    AlternatingBilinearMap F (OldInput A q) (OldOutput A q) where
  toLinearMap := (omega A q).toLinearMap.comp (multiplierMap A (sourceMultipliers A h))
  map_self_eq_zero := multiplier_diagonal_zero A (sourceMultipliers A h)
    (sourceMultipliers_compatible A h)

/-- Every slice of the source obstruction comes from the actual selected
kernel `L`, including its prescribed coordinate choices. -/
theorem source_multiplier_mem_chosenKernel (h : sourceRelations A)
    (anchors : Set ((I ⊕ J) × Fin q)) (x : OldInput A q) :
    multiplierMap A (sourceMultipliers A h) x ∈ chosenKernel A q anchors := by
  intro va _
  change ((sourceMultipliers A h va.1) * x va.1 va.2).fst = 0
  rw [TrivSqZeroExt.fst_mul, sourceMultipliers_scalar, zero_mul]

/-- Compatibility and zero scalar parts determine the entire multiplier
family from its equation radical coefficients. -/
theorem sourceMultipliers_recover
    (r : ∀ v, RingAt A v)
    (hr : ∀ e : Incidence A, r (.inl e.1.1) = endpointMap A e (r (.inr e.1.2)))
    (hs : ∀ v, (r v).fst = 0) :
    sourceMultipliers A
      ⟨(fun i => (r (.inl i)).snd), compatible_radicals_mem_sourceRelations A r hr⟩ = r := by
  funext v
  cases v with
  | inl i =>
    apply TrivSqZeroExt.ext
    · exact (hs (.inl i)).symm
    · rfl
  | inr j =>
    apply TrivSqZeroExt.ext
    · exact (hs (.inr j)).symm
    · apply Subtype.ext
      funext i
      have he := congrArg TrivSqZeroExt.snd (hr ⟨(i.val, j), i.property⟩)
      simpa [sourceMultipliers, endpointMap, readoutProjection] using he

/-- Global multiplier classification in the exact source-kernel form. -/
theorem exists_source_multiplier
    (P : OldInput A q →ₗ[F] OldInput A q)
    (hdiag : ∀ x, omega A q (P x) x = 0)
    (anchors : Set ((I ⊕ J) × Fin q)) (hcover : AnchorsCover A anchors)
    (hP : ∀ x, P x ∈ chosenKernel A q anchors)
    (a b : Fin q) (hab : a ≠ b) :
    ∃ h : sourceRelations A, P = multiplierMap A (sourceMultipliers A h) := by
  obtain ⟨r, hr, he, hs, hk⟩ := global_multiplier_classification A P hdiag
    anchors hcover hP a b hab
  refine ⟨⟨(fun i => (r (.inl i)).snd), hk⟩, ?_⟩
  have hr' := sourceMultipliers_recover A r he hs
  apply LinearMap.ext
  intro x
  funext v k
  change P x v k = sourceMultipliers A _ v * x v k
  rw [hr', hr]

/-- The source obstruction extended through both padding sectors. -/
def paddedSourceObstruction (h : sourceRelations A) :
    AlternatingBilinearMap F (PaddedInput A q) (PaddedOutput A q) where
  toLinearMap := LinearMap.mk₂ F (fun x y => (sourceObstruction A h x.1 y.1, 0))
    (by intros; simp) (by intros; simp) (by intros; simp) (by intros; simp)
  map_self_eq_zero x := by simp

/-- Padded source-obstruction slices are in the actual obstruction space. -/
theorem paddedSourceObstruction_slice_mem (h : sourceRelations A)
    (hq : 0 < q) (x : PaddedInput A q) :
    (paddedSourceObstruction A h).toLinearMap x ∈ constructionObstructionSpace A q hq := by
  refine ⟨multiplierMap A (sourceMultipliers A h) x.1,
    source_multiplier_mem_chosenKernel A h (componentAnchors A q hq) x.1, ?_⟩
  rfl

/-- An alternating tensor all of whose slices belong to `C` has exactly one
of the source-kernel forms. Padding contributes no additional obstructions. -/
theorem padded_obstruction_classification
    (hq : 2 ≤ q)
    (γ : AlternatingBilinearMap F (PaddedInput A q) (PaddedOutput A q))
    (hγ : ∀ x, γ.toLinearMap x ∈ constructionObstructionSpace A q (by omega)) :
    ∃ h : sourceRelations A, ∀ x y, γ x y = paddedSourceObstruction A h x y := by
  let L := chosenSpace A q (show 0 < q by omega)
  let M := (sliceMap A q).comp L.subtype
  let old := LinearMap.inl F (OldInput A q) (OldOutput A q)
  let g := γ.toLinearMap.comp old
  have hg : ∀ x, g x ∈ LinearMap.range M := by
    intro x
    obtain ⟨a, ha, hea⟩ := hγ (x, 0)
    exact ⟨⟨a, ha⟩, hea⟩
  obtain ⟨P', hP'⟩ := ObstructionDuality.exists_linear_lift M g hg
  let P : OldInput A q →ₗ[F] OldInput A q := L.subtype.comp P'
  have hslice (x : OldInput A q) (y : PaddedInput A q) :
      (omega A q (P x) y.1, 0) = γ (x, 0) y := by
    have h := LinearMap.congr_fun (LinearMap.congr_fun hP' x) y
    exact h
  have hdiag (x : OldInput A q) : omega A q (P x) x = 0 := by
    have h := congrArg Prod.fst (hslice x (x, 0))
    simpa using h
  obtain ⟨h, he⟩ := exists_source_multiplier A P hdiag (componentAnchors A q (by omega))
    (componentAnchors_cover A q (by omega)) (fun x => (P' x).property)
    (⟨0, by omega⟩ : Fin q) (⟨1, by omega⟩ : Fin q) (by intro h; have := congrArg Fin.val h; norm_num at this)
  have hz (x : PaddedInput A q) (d : OldOutput A q) : γ x (0, d) = 0 := by
    obtain ⟨a, ha, hea⟩ := hγ x
    have hh := LinearMap.congr_fun hea (0, d)
    simpa [sliceMap_apply] using hh.symm
  have hz' (d : OldOutput A q) (x : PaddedInput A q) : γ (0, d) x = 0 := by
    rw [γ.skew, hz, neg_zero]
  refine ⟨h, ?_⟩
  intro x y
  have hx : x = (x.1, 0) + (0, x.2) := by simp
  have hy : y = (y.1, 0) + (0, y.2) := by simp
  calc
    γ x y = γ (x.1, 0) (y.1, 0) := by
      conv_lhs => rw [hx, hy]
      rw [γ.add_left, γ.add_right, hz, hz', add_zero, add_zero]
    _ = (omega A q (P x.1) y.1, 0) := (hslice x.1 (y.1, 0)).symm
    _ = paddedSourceObstruction A h x y := by rw [he]; rfl

/-- The prescribed internal radical coordinate reads the source coefficient
exactly. This is the sparse charge-pairing calculation. -/
theorem source_obstruction_charge_reading (hq : 2 ≤ q)
    (h : sourceRelations A) (i : I) :
    ((paddedSourceObstruction A h
      (unitInput A (.inl i) (firstPair q hq).1.1, 0)
      (unitInput A (.inl i) (firstPair q hq).1.2, 0)).1.1
        (.inl i) (firstPair q hq)).snd = h.val i := by
  change (((sourceMultipliers A h (.inl i) *
      unitInput A (.inl i) (firstPair q hq).1.1 (.inl i) (firstPair q hq).1.1) *
      unitInput A (.inl i) (firstPair q hq).1.2 (.inl i) (firstPair q hq).1.2) -
    unitInput A (.inl i) (firstPair q hq).1.2 (.inl i) (firstPair q hq).1.1 *
      (sourceMultipliers A h (.inl i) *
        unitInput A (.inl i) (firstPair q hq).1.1 (.inl i) (firstPair q hq).1.2)).snd = _
  simp [unitInput_self, firstPair, sourceMultipliers]

/-- Pairing with the specified sparse charge tensor reads precisely these
internal radical coefficients. -/
noncomputable def chargeReading (hq : 2 ≤ q)
    (γ : AlternatingBilinearMap F (PaddedInput A q) (PaddedOutput A q)) (β : I → F) : F :=
  ∑ i, β i * ((γ
    (unitInput A (.inl i) (firstPair q hq).1.1, 0)
    (unitInput A (.inl i) (firstPair q hq).1.2, 0)).1.1
      (.inl i) (firstPair q hq)).snd

theorem source_charge_pairing (hq : 2 ≤ q) (h : sourceRelations A) (β : I → F) :
    chargeReading A hq (paddedSourceObstruction A h) β = ∑ i, h.val i * β i := by
  unfold chargeReading
  apply Finset.sum_congr rfl
  intro i _
  rw [source_obstruction_charge_reading A hq h i, mul_comm]

/-- Distinct source obstructions give distinct padded tensors. -/
theorem source_obstruction_injective (hq : 2 ≤ q) :
    Function.Injective (paddedSourceObstruction (q := q) A) := by
  intro h k he
  apply Subtype.ext
  funext i
  have hi := congrArg (fun γ : AlternatingBilinearMap F (PaddedInput A q) (PaddedOutput A q) =>
    ((γ (unitInput A (.inl i) (firstPair q hq).1.1, 0)
      (unitInput A (.inl i) (firstPair q hq).1.2, 0)).1.1
        (.inl i) (firstPair q hq)).snd) he
  rw [← source_obstruction_charge_reading A hq h i,
    ← source_obstruction_charge_reading A hq k i]
  exact hi

end IncidenceTensor
end GroupWL
