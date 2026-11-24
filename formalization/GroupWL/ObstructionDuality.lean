import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Tactic

/-!
# Linear duality and the antisymmetrization obstruction

These results are the linear-algebra engine used by the manuscript's global
and relative obstruction arguments. In particular, no nondegeneracy of the
restriction of an ambient coordinate pairing to a subspace is assumed.
-/

namespace GroupWL
namespace ObstructionDuality

open LinearMap Submodule

section Abstract
variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- Solvability is exactly annihilation by every dual obstruction. -/
theorem mem_range_iff_dual_obstructions (A : V →ₗ[K] W) (b : W) :
    b ∈ LinearMap.range A ↔
      ∀ h : Module.Dual K W, A.dualMap h = 0 → h b = 0 := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  simp only [← LinearMap.ker_dualMap_eq_dualAnnihilator_range, LinearMap.mem_ker]

/-- Two charges have the same class in the obstruction quotient exactly when
all dual obstructions give the same answer. -/
theorem sub_mem_range_iff_dual_obstructions (A : V →ₗ[K] W) (b c : W) :
    b - c ∈ LinearMap.range A ↔
      ∀ h : Module.Dual K W, A.dualMap h = 0 → h b = h c := by
  rw [mem_range_iff_dual_obstructions]
  simp only [map_sub, sub_eq_zero]

/-- The relative dual space is the dual of a quotient. This statement applies
even if the ambient coordinate pairing restricts degenerately to `E`. -/
noncomputable def quotientDual (E : Submodule K V) :
    Module.Dual K (V ⧸ E) ≃ₗ[K] E.dualAnnihilator :=
  E.dualQuotEquivDualAnnihilator

@[simp] theorem quotientDual_apply (E : Submodule K V)
    (h : Module.Dual K (V ⧸ E)) (v : V) :
    quotientDual E h v = h (Submodule.Quotient.mk v) := rfl

/-- A functional on a subspace of `W` is a relative obstruction for a
restricted linear map precisely when it vanishes on that restricted image. -/
theorem relative_mem_range_iff (S : Submodule K V) (R : Submodule K W)
    (A : V →ₗ[K] W) (hA : ∀ s ∈ S, A s ∈ R) (b : R) :
    b ∈ LinearMap.range ((A.comp S.subtype).codRestrict R
      (fun s => hA s s.property)) ↔
    ∀ h : Module.Dual K R,
      (∀ s : S, h ⟨A s, hA s s.property⟩ = 0) → h b = 0 := by
  rw [mem_range_iff_dual_obstructions]
  congr! 2
  exact LinearMap.ext_iff

/-- Restricting to a subspace turns the annihilator of the intersection into
the restrictions of the original annihilator. This is the relative duality
identity, with no inner product on the subspace and no nondegeneracy premise. -/
theorem restricted_annihilator_eq (Y R : Submodule K V) :
    (Y.comap R.subtype).dualAnnihilator = Y.dualAnnihilator.map R.dualRestrict := by
  apply le_antisymm
  · intro h hh
    let h' : Module.Dual K V := Subspace.dualLift R h
    have hi : h' ∈ (Y ⊓ R).dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro v hv
      have hv' : (⟨v, hv.2⟩ : R) ∈ Y.comap R.subtype := hv.1
      simpa only [h', Subspace.dualLift_of_mem hv.2] using
        (Submodule.mem_dualAnnihilator h).mp hh ⟨v, hv.2⟩ hv'
    rw [Subspace.dualAnnihilator_inf_eq, Submodule.mem_sup] at hi
    obtain ⟨a, ha, b, hb, hab⟩ := hi
    refine ⟨a, ha, ?_⟩
    apply LinearMap.ext
    intro r
    have heq := LinearMap.congr_fun hab r.val
    have hbzero := (Submodule.mem_dualAnnihilator b).mp hb r.val r.property
    simpa [h', Subspace.dualLift_of_subtype, hbzero] using heq
  · rintro h ⟨a, ha, rfl⟩
    rw [Submodule.mem_dualAnnihilator]
    intro r hr
    exact (Submodule.mem_dualAnnihilator a).mp ha r.val hr

/-- Equivalently, every relative obstruction has an ambient representative
in the annihilator of `Y`. -/
theorem relative_obstruction_has_lift (Y R : Submodule K V)
    (h : Module.Dual K R)
    (hh : ∀ r : R, r.val ∈ Y → h r = 0) :
    ∃ a : Module.Dual K V, a ∈ Y.dualAnnihilator ∧
      ∀ r : R, a r.val = h r := by
  have hh' : h ∈ (Y.comap R.subtype).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    exact hh
  rw [restricted_annihilator_eq, Submodule.mem_map] at hh'
  obtain ⟨a, ha, hea⟩ := hh'
  exact ⟨a, ha, fun r => LinearMap.congr_fun hea r⟩

/-- Pointwise membership in a linear image admits a simultaneous linear lift.
This justifies lifting the contraction map through `L → C|U` in the relative
criterion, even when that map is not injective. -/
theorem exists_linear_lift {U : Type*} [AddCommGroup U] [Module K U]
    (M : V →ₗ[K] W) (g : U →ₗ[K] W)
    (hg : ∀ u, g u ∈ LinearMap.range M) :
    ∃ P : U →ₗ[K] V, M.comp P = g := by
  obtain ⟨s, hs⟩ := M.rangeRestrict.exists_rightInverse_of_surjective
    M.range_rangeRestrict
  let g' : U →ₗ[K] LinearMap.range M := g.codRestrict _ hg
  refine ⟨s.comp g', ?_⟩
  apply LinearMap.ext
  intro u
  have hu := LinearMap.congr_fun hs (g' u)
  exact congrArg Subtype.val hu

variable {B S : Type*} [AddCommGroup B] [Module K B]
  [AddCommGroup S] [Module K S]

/-- An identification of the two dual obstruction spaces that respects the
charge pairing proves the stated image-membership criterion. -/
theorem charge_mem_range_iff
    (A : S →ₗ[K] B) (d : V →ₗ[K] W) (charge : B →ₗ[K] W)
    (e : LinearMap.ker A.dualMap ≃ₗ[K] LinearMap.ker d.dualMap)
    (he : ∀ h : LinearMap.ker A.dualMap, ∀ b, (e h).val (charge b) = h.val b)
    (b : B) :
    charge b ∈ LinearMap.range d ↔ b ∈ LinearMap.range A := by
  rw [mem_range_iff_dual_obstructions, mem_range_iff_dual_obstructions]
  constructor
  · intro hb h hh
    have ht := hb (e ⟨h, hh⟩).val (e ⟨h, hh⟩).property
    simpa only [he] using ht
  · intro hb h hh
    obtain ⟨g, hg⟩ := e.surjective ⟨h, hh⟩
    have ht := hb g.val g.property
    rw [← he g b] at ht
    simpa only [hg] using ht

/-- The same dual identification shows that every twist has a charge
representative modulo the image of antisymmetrization. -/
theorem exists_charge_representative
    (A : S →ₗ[K] B) (d : V →ₗ[K] W) (charge : B →ₗ[K] W)
    (e : LinearMap.ker A.dualMap ≃ₗ[K] LinearMap.ker d.dualMap)
    (he : ∀ h : LinearMap.ker A.dualMap, ∀ b, (e h).val (charge b) = h.val b)
    (w : W) :
    ∃ b : B, w - charge b ∈ LinearMap.range d := by
  have hsurj : Function.Surjective (d.coprod charge) := by
    apply LinearMap.dualMap_injective_iff.mp
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm ?_ bot_le
    intro h hh
    have hzero : ∀ v b, h (d v + charge b) = 0 := by
      intro v b
      exact LinearMap.congr_fun hh (v, b)
    have hd : d.dualMap h = 0 := by
      ext v
      simpa using hzero v 0
    obtain ⟨g, hg⟩ := e.surjective ⟨h, hd⟩
    have hgzero : g = 0 := by
      apply Subtype.ext
      apply LinearMap.ext
      intro b
      have hb : h (charge b) = 0 := by simpa using hzero 0 b
      have he' := he g b
      rw [hg] at he'
      exact he'.symm.trans hb
    have hz : h = 0 := by
      have := congrArg Subtype.val hg
      simpa [hgzero] using this.symm
    exact hz
  obtain ⟨⟨v, b⟩, hvb⟩ := hsurj w
  refine ⟨b, v, ?_⟩
  change d v + charge b = w at hvb
  rw [← hvb, add_sub_cancel_right]

end Abstract

section Coordinates
variable {K ι κ : Type*} [Field K] [Fintype ι] [Fintype κ]

/-- Coordinates of a linear map from the input space to the output space. -/
abbrev MatrixSpace (K ι κ : Type*) := ι → κ → K

/-- The coordinate pairing used in the manuscript, with the input index first. -/
def matrixPair (c y : MatrixSpace K ι κ) : K :=
  ∑ i, ∑ z, c i z * y i z

@[simp] theorem matrixPair_zero_right (c : MatrixSpace K ι κ) :
    matrixPair c 0 = 0 := by simp [matrixPair]

@[simp] theorem matrixPair_zero_left (y : MatrixSpace K ι κ) :
    matrixPair 0 y = 0 := by simp [matrixPair]

theorem matrixPair_comm (c y : MatrixSpace K ι κ) :
    matrixPair c y = matrixPair y c := by
  simp only [matrixPair, mul_comm]

/-- A matrix, viewed as the functional defined by the coordinate pairing. -/
def matrixDual : MatrixSpace K ι κ →ₗ[K] Module.Dual K (MatrixSpace K ι κ) where
  toFun c :=
    { toFun := matrixPair c
      map_add' := by
        intro x y
        simp [matrixPair, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro k y
        simp [matrixPair, Finset.mul_sum, mul_left_comm] }
  map_add' := by
    intro x y
    ext c
    simp [matrixPair, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro k y
    ext c
    simp [matrixPair, Finset.mul_sum, mul_assoc]

/-- Every coordinate functional is represented by a matrix. -/
theorem matrixDual_surjective :
    Function.Surjective (matrixDual : MatrixSpace K ι κ →ₗ[K]
      Module.Dual K (MatrixSpace K ι κ)) := by
  classical
  intro h
  refine ⟨fun i z => h (Pi.single i (Pi.single z 1)), ?_⟩
  apply LinearMap.ext
  intro y
  have he : y = ∑ i, ∑ z, y i z • Pi.single i (Pi.single z (1 : K)) := by
    ext i z
    simp [Finset.sum_apply, Pi.single_apply, ite_apply]
  change matrixPair (fun i z => h (Pi.single i (Pi.single z 1))) y = h y
  conv_rhs => rw [he]
  simp [matrixPair, map_sum, map_smul, mul_comm]

theorem matrixDual_injective :
    Function.Injective (matrixDual : MatrixSpace K ι κ →ₗ[K]
      Module.Dual K (MatrixSpace K ι κ)) := by
  classical
  intro c d h
  ext i z
  have hi := LinearMap.congr_fun h (Pi.single i (Pi.single z 1))
  simpa [matrixDual, matrixPair, Pi.single_apply, ite_apply] using hi

/-- The coordinate pairing is perfect on the ambient matrix space. -/
noncomputable def matrixDualEquiv :
    MatrixSpace K ι κ ≃ₗ[K] Module.Dual K (MatrixSpace K ι κ) :=
  LinearEquiv.ofBijective matrixDual ⟨matrixDual_injective, matrixDual_surjective⟩

@[simp] theorem matrixDualEquiv_apply (c : MatrixSpace K ι κ) :
    matrixDualEquiv c = matrixDual c := rfl

/-- The coordinate orthogonal complement, represented as an actual submodule. -/
def annihilator (C : Submodule K (MatrixSpace K ι κ)) :
    Submodule K (MatrixSpace K ι κ) :=
  C.dualAnnihilator.comap matrixDual

@[simp] theorem mem_annihilator (C : Submodule K (MatrixSpace K ι κ))
    (c : MatrixSpace K ι κ) :
    c ∈ annihilator C ↔ ∀ y ∈ C, matrixPair c y = 0 := by
  simp only [annihilator, Submodule.mem_comap, Submodule.mem_dualAnnihilator]
  rfl

/-- Nondegeneracy is used only for the ambient coordinate space. -/
theorem annihilator_annihilator (C : Submodule K (MatrixSpace K ι κ)) :
    annihilator (annihilator C) = C := by
  ext c
  rw [mem_annihilator]
  constructor
  · intro hc
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff C c).mp
    intro h hh
    obtain ⟨d, rfl⟩ := matrixDual_surjective h
    have hd : d ∈ annihilator C := hh
    have hz := hc d hd
    change matrixPair d c = 0
    rw [matrixPair_comm]
    exact hz
  · intro hc y hy
    rw [matrixPair_comm]
    exact (mem_annihilator C y).mp hy c hc

/-- Evaluation of a coordinate matrix on an input vector. -/
def evaluation (x : ι → K) : MatrixSpace K ι κ →ₗ[K] (κ → K) where
  toFun y z := ∑ i, x i * y i z
  map_add' := by
    intro y y'
    ext z
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro k y
    ext z
    simp [Finset.mul_sum, mul_left_comm]

/-- A coordinate matrix as a genuine linear map of vector spaces. -/
def matrixToLinear (y : MatrixSpace K ι κ) : (ι → K) →ₗ[K] (κ → K) where
  toFun x := evaluation x y
  map_add' := by
    intro x x'
    ext z
    simp [evaluation, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro k x
    ext z
    simp [evaluation, Finset.mul_sum, mul_assoc]

omit [Fintype κ] in
@[simp] theorem matrixToLinear_apply (y : MatrixSpace K ι κ) (x : ι → K) :
    matrixToLinear y x = evaluation x y := rfl

/-- Coordinate matrices and linear operators are equivalent. This equivalence
connects the coordinate duality calculation to the tensor-group construction. -/
noncomputable def matrixLinearEquiv :
    MatrixSpace K ι κ ≃ₗ[K] ((ι → K) →ₗ[K] (κ → K)) := by
  classical
  refine
    { toFun := matrixToLinear
      invFun := fun f i z => f (Pi.single i 1) z
      left_inv := ?_
      right_inv := ?_
      map_add' := ?_
      map_smul' := ?_ }
  · intro y y'
    apply LinearMap.ext
    intro x
    ext z
    simp [matrixToLinear, evaluation, mul_add, Finset.sum_add_distrib]
  · intro k y
    apply LinearMap.ext
    intro x
    ext z
    simp [matrixToLinear, evaluation, Finset.mul_sum]
  · intro y
    ext i z
    simp [matrixToLinear, evaluation, Pi.single_apply]
  · intro f
    apply LinearMap.ext
    intro x
    have hx : x = ∑ i, x i • Pi.single i (1 : K) := by
      ext i
      simp [Pi.single_apply]
    ext z
    change (∑ i, x i * f (Pi.single i 1) z) = f x z
    conv_rhs => rw [hx]
    simp

omit [Fintype κ] in
@[simp] theorem matrixLinearEquiv_apply (y : MatrixSpace K ι κ) :
    matrixLinearEquiv y = matrixToLinear y := rfl

/-- Coordinate outer product. It represents a rank-one map when both factors
are nonzero. -/
def rankOne (x : ι → K) (w : κ → K) : MatrixSpace K ι κ :=
  fun i z => x i * w z

/-- The coefficients of a linear functional on a coordinate vector space. -/
noncomputable def functionalCoefficients (h : Module.Dual K (κ → K)) : κ → K := by
  classical
  exact fun z => h (Pi.single z 1)

theorem functional_eq_sum (h : Module.Dual K (κ → K)) (v : κ → K) :
    h v = ∑ z, functionalCoefficients h z * v z := by
  classical
  have hv : v = ∑ z, v z • Pi.single z (1 : K) := by
    ext z
    simp [Pi.single_apply]
  conv_lhs => rw [hv]
  simp [functionalCoefficients, map_sum, map_smul, mul_comm]

theorem functionalCoefficients_eq_zero_iff (h : Module.Dual K (κ → K)) :
    functionalCoefficients h = 0 ↔ h = 0 := by
  constructor
  · intro hh
    ext v
    rw [functional_eq_sum]
    simp [hh]
  · rintro rfl
    funext z
    simp [functionalCoefficients]

/-- Evaluation's adjoint sends a functional to an outer product with `x`. -/
theorem evaluation_adjoint (x : ι → K) (h : Module.Dual K (κ → K))
    (y : MatrixSpace K ι κ) :
    h (evaluation x y) = matrixPair (rankOne x (functionalCoefficients h)) y := by
  rw [functional_eq_sum]
  unfold evaluation matrixPair rankOne
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro z _
  ring

/-- A subspace contains no nonzero coordinate rank-one matrix. -/
def NoRankOne (C : Submodule K (MatrixSpace K ι κ)) : Prop :=
  ∀ x w, rankOne x w ∈ C → x = 0 ∨ w = 0

/-- Excluding rank-one matrices from `C` forces its perpendicular to evaluate
surjectively on every nonzero input. This is the evaluation step in the
manuscript's rank lemma. -/
theorem evaluation_surjective_of_noRankOne
    (C : Submodule K (MatrixSpace K ι κ)) (hC : NoRankOne C)
    (x : ι → K) (hx : x ≠ 0) :
    Function.Surjective ((evaluation x).comp (annihilator C).subtype) := by
  apply LinearMap.dualMap_injective_iff.mp
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro h hh
  have hc : rankOne x (functionalCoefficients h) ∈ C := by
    rw [← annihilator_annihilator C, mem_annihilator]
    intro y hy
    rw [← evaluation_adjoint]
    exact LinearMap.congr_fun hh ⟨y, hy⟩
  have hw := (hC x (functionalCoefficients h) hc).resolve_left hx
  exact (functionalCoefficients_eq_zero_iff h).mp hw

/-- The resulting surjectivity gives witnesses in the actual perpendicular
matrix space, not just in its span. -/
theorem exists_evaluation_of_noRankOne
    (C : Submodule K (MatrixSpace K ι κ)) (hC : NoRankOne C)
    (x : ι → K) (hx : x ≠ 0) (z : κ → K) :
    ∃ y : MatrixSpace K ι κ, y ∈ annihilator C ∧ evaluation x y = z := by
  obtain ⟨y, hy⟩ := evaluation_surjective_of_noRankOne C hC x hx z
  exact ⟨y.val, y.property, hy⟩

/-- Matrices which vanish on the retained input subspace. -/
def vanishingOn (E : Submodule K (ι → K)) :
    Submodule K (MatrixSpace K ι κ) where
  carrier := {y | ∀ x ∈ E, evaluation x y = 0}
  zero_mem' := by simp
  add_mem' := by
    intro y y' hy hy' x hx
    rw [map_add, hy x hx, hy' x hx, add_zero]
  smul_mem' := by
    intro k y hy x hx
    rw [map_smul, hy x hx, smul_zero]

omit [Fintype κ] in
@[simp] theorem mem_vanishingOn (E : Submodule K (ι → K))
    (y : MatrixSpace K ι κ) :
    y ∈ vanishingOn E ↔ ∀ x ∈ E, evaluation x y = 0 := Iff.rfl

/-- Relative matrix obstructions are exactly restrictions of matrices in `C`.
The space `R` may be `vanishingOn E` for an isotropic subspace `E`; the result
never uses a nondegenerate pairing on `E` or on its perpendicular. -/
theorem relative_matrix_obstruction_iff
    (C R : Submodule K (MatrixSpace K ι κ)) (h : Module.Dual K R) :
    (∀ r : R, r.val ∈ annihilator C → h r = 0) ↔
      ∃ c : MatrixSpace K ι κ, c ∈ C ∧
        ∀ r : R, h r = matrixPair c r.val := by
  constructor
  · intro hh
    obtain ⟨a, ha, hea⟩ := relative_obstruction_has_lift (annihilator C) R h hh
    obtain ⟨c, rfl⟩ := matrixDual_surjective a
    have hc : c ∈ C := by
      rw [← annihilator_annihilator C]
      exact ha
    exact ⟨c, hc, fun r => (hea r).symm⟩
  · rintro ⟨c, hc, he⟩ r hr
    rw [he, matrixPair_comm]
    exact (mem_annihilator C r.val).mp hr c hc

/-- The relative matrix criterion specialized to the retained query subspace. -/
theorem retained_matrix_obstruction_iff
    (C : Submodule K (MatrixSpace K ι κ)) (E : Submodule K (ι → K))
    (h : Module.Dual K (vanishingOn E)) :
    (∀ y : vanishingOn E, y.val ∈ annihilator C → h y = 0) ↔
      ∃ c : MatrixSpace K ι κ, c ∈ C ∧
        ∀ y : vanishingOn E, h y = matrixPair c y.val :=
  relative_matrix_obstruction_iff C (vanishingOn E) h

/-- A three-index array describing a map from the input space into matrices. -/
abbrev TensorSpace (K ι κ : Type*) := ι → ι → κ → K

/-- Antisymmetrization of a family of matrix slices. -/
def boundary (a : TensorSpace K ι κ) : TensorSpace K ι κ :=
  fun i j z => a i j z - a j i z

/-- Pair tensors on all ordered input pairs. The factor two is explicit,
so this pairing is not accidentally used in characteristic two. -/
def tensorPair (g t : TensorSpace K ι κ) : K :=
  ∑ i, ∑ j, ∑ z, g i j z * t i j z

/-- Alternation includes both the diagonal and transposition conditions. -/
def Alternating (g : TensorSpace K ι κ) : Prop :=
  (∀ i z, g i i z = 0) ∧ ∀ i j z, g j i z = -g i j z

/-- The adjoint of antisymmetrization is given by the individual slices. -/
theorem tensorPair_boundary (g a : TensorSpace K ι κ)
    (hg : ∀ i j z, g j i z = -g i j z) :
    tensorPair g (boundary a) = 2 * ∑ i, matrixPair (g i) (a i) := by
  classical
  unfold tensorPair boundary matrixPair
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  have hs : (∑ i, ∑ j, ∑ z, g i j z * a j i z) =
      -(∑ i, ∑ j, ∑ z, g i j z * a i j z) := by
    rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro z _
    rw [hg]
    ring
  rw [hs]
  ring

/-- Orthogonality to a matrix space, defined by the actual coordinate pairing. -/
def OrthogonalTo (Y : Submodule K (MatrixSpace K ι κ))
    (c : MatrixSpace K ι κ) : Prop :=
  ∀ y ∈ Y, matrixPair c y = 0

/-- An alternating tensor annihilates every boundary of a family of matrices
in `Y` if and only if each one of its slices annihilates `Y`.
This is the concrete finite-coordinate adjoint calculation behind the
manuscript's global-dual criterion. -/
theorem annihilates_boundary_iff_slices
    (h2 : (2 : K) ≠ 0) (Y : Submodule K (MatrixSpace K ι κ))
    (g : TensorSpace K ι κ) (hg : Alternating g) :
    (∀ a : TensorSpace K ι κ, (∀ i, a i ∈ Y) →
      tensorPair g (boundary a) = 0) ↔
    ∀ i, OrthogonalTo Y (g i) := by
  classical
  constructor
  · intro h i y hy
    let a : TensorSpace K ι κ := Function.update 0 i y
    have ha : ∀ j, a j ∈ Y := by
      intro j
      by_cases hij : j = i
      · subst j
        simpa [a] using hy
      · simp [a, Function.update_of_ne hij]
    have hz := h a ha
    rw [tensorPair_boundary g a hg.2] at hz
    have hs : (∑ j, matrixPair (g j) (a j)) = matrixPair (g i) y := by
      calc
        (∑ j, matrixPair (g j) (a j)) = matrixPair (g i) (a i) := by
          apply Finset.sum_eq_single i
          · intro j _ hji
            simp [a, Function.update_of_ne hji, matrixPair]
          · simp
        _ = matrixPair (g i) y := by simp [a]
    rw [hs] at hz
    exact (mul_eq_zero.mp hz).resolve_left h2
  · intro h a ha
    rw [tensorPair_boundary g a hg.2]
    have hs : (∑ i, matrixPair (g i) (a i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact h i (a i) (ha i)
    rw [hs, mul_zero]

/-- The full global-dual criterion: slices lie in `C` exactly when the
alternating tensor annihilates boundaries of maps into `C`-perpendicular. -/
theorem global_dual_criterion (h2 : (2 : K) ≠ 0)
    (C : Submodule K (MatrixSpace K ι κ))
    (g : TensorSpace K ι κ) (hg : Alternating g) :
    (∀ a : TensorSpace K ι κ, (∀ i, a i ∈ annihilator C) →
      tensorPair g (boundary a) = 0) ↔
    ∀ i, g i ∈ C := by
  rw [annihilates_boundary_iff_slices h2 _ g hg]
  have hi : ∀ i, OrthogonalTo (annihilator C) (g i) ↔ g i ∈ C := by
    intro i
    change (∀ y ∈ annihilator C, matrixPair (g i) y = 0) ↔ _
    rw [← mem_annihilator, annihilator_annihilator]
  exact forall_congr' hi

end Coordinates
section Transport
variable {K ι μ κ : Type*} [Field K] [Fintype ι] [Fintype μ] [Fintype κ]

/-- Transport the matrix pairing along a map of primal coordinate spaces.
When the map parameterizes operators vanishing on a retained subspace, this
is restriction to the quotient's dual coordinates. -/
noncomputable def matrixAdjoint
    (f : MatrixSpace K μ κ →ₗ[K] MatrixSpace K ι κ) :
    MatrixSpace K ι κ →ₗ[K] MatrixSpace K μ κ :=
  matrixDualEquiv.symm.toLinearMap.comp (f.dualMap.comp matrixDual)

theorem matrixAdjoint_pair
    (f : MatrixSpace K μ κ →ₗ[K] MatrixSpace K ι κ)
    (c : MatrixSpace K ι κ) (y : MatrixSpace K μ κ) :
    matrixPair (matrixAdjoint f c) y = matrixPair c (f y) := by
  have h : matrixDualEquiv (matrixAdjoint f c) = f.dualMap (matrixDual c) := by
    apply LinearEquiv.apply_symm_apply
  exact LinearMap.congr_fun h y

/-- Coordinate restriction of the obstruction space is precisely the
annihilator of the pulled-back admissible matrix space. No orthogonal
projection appears in this identity. -/
theorem annihilator_adjoint_map
    (C : Submodule K (MatrixSpace K ι κ))
    (f : MatrixSpace K μ κ →ₗ[K] MatrixSpace K ι κ) :
    annihilator (C.map (matrixAdjoint f)) = (annihilator C).comap f := by
  ext y
  rw [mem_annihilator, Submodule.mem_comap, mem_annihilator]
  constructor
  · intro h c hc
    have hz := h (matrixAdjoint f c) ⟨c, hc, rfl⟩
    rw [matrixPair_comm, matrixAdjoint_pair] at hz
    rw [matrixPair_comm]
    exact hz
  · intro h d hd
    obtain ⟨c, hc, rfl⟩ := hd
    rw [matrixPair_comm, matrixAdjoint_pair]
    rw [matrixPair_comm]
    exact h c hc

/-- The relative antisymmetrization criterion in coordinates on the quotient.
`f` parameterizes its matrices inside the ambient matrix space. Pairing is
transported by the adjoint, so isotropic retained subspaces are allowed. -/
theorem relative_dual_criterion
    (h2 : (2 : K) ≠ 0) (C : Submodule K (MatrixSpace K ι κ))
    (f : MatrixSpace K μ κ →ₗ[K] MatrixSpace K ι κ)
    (g : TensorSpace K μ κ) (hg : Alternating g) :
    (∀ a : TensorSpace K μ κ, (∀ i, f (a i) ∈ annihilator C) →
      tensorPair g (boundary a) = 0) ↔
    ∀ i, g i ∈ C.map (matrixAdjoint f) := by
  have h := global_dual_criterion h2 (C.map (matrixAdjoint f)) g hg
  rw [annihilator_adjoint_map] at h
  exact h

end Transport

end ObstructionDuality
end GroupWL
