import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic

/-!
# Affine systems and exact local families

These results formalize the elementary affine ingredients used in Sections 2
and 5 of the manuscript. They do not assert existence of the circuit compiler
or of local families for the site-and-square construction.
-/

namespace GroupWL

open scoped BigOperators

section Duality

variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- A vector belongs to the image exactly when all linear obstructions vanish. -/
theorem mem_range_iff_annihilator (A : V →ₗ[K] W) (b : W) :
    b ∈ LinearMap.range A ↔
      ∀ φ : W →ₗ[K] K, (∀ v, φ (A v) = 0) → φ b = 0 := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  constructor
  · intro h φ hφ
    apply h φ
    rw [Submodule.mem_dualAnnihilator]
    rintro _ ⟨v, rfl⟩
    exact hφ v
  · intro h φ hφ
    apply h φ
    intro v
    exact (Submodule.mem_dualAnnihilator φ).mp hφ _ ⟨v, rfl⟩

variable {I : Type*} [Fintype I]

/-- The coordinate pairing as a linear functional. -/
def coordinateFunctional (u : I → K) : (I → K) →ₗ[K] K where
  toFun x := ∑ i, u i * x i
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- The kernel/image duality used when decoding a readout frame. -/
theorem mem_range_iff_coordinate_relations (A : V →ₗ[K] (I → K)) (b : I → K) :
    b ∈ LinearMap.range A ↔
      ∀ u : I → K, (∀ v, ∑ i, u i * A v i = 0) →
        ∑ i, u i * b i = 0 := by
  classical
  constructor
  · rintro ⟨v, rfl⟩ u hu
    exact hu v
  · intro h
    apply (mem_range_iff_annihilator A b).mpr
    intro φ hφ
    let u : I → K := fun i => φ (fun j => if i = j then 1 else 0)
    have repr (x : I → K) : φ x = ∑ i, u i * x i := by
      rw [LinearMap.pi_apply_eq_sum_univ]
      apply Finset.sum_congr rfl
      intro i _
      simp [u, mul_comm]
    rw [repr]
    apply h u
    intro v
    rw [← repr]
    exact hφ v

/-- In the manuscript's notation, annihilating `N_j` is equivalent to being
the vector of evaluations of one decoded readout. -/
theorem decoded_values_exist_iff (ell : I → V →ₗ[K] K) (θ : I → K) :
    (∃ z : V, ∀ i, ell i z = θ i) ↔
      ∀ u : I → K, (∑ i, u i • ell i = 0) → ∑ i, u i * θ i = 0 := by
  have hrange : (∃ z : V, ∀ i, ell i z = θ i) ↔
      θ ∈ LinearMap.range (LinearMap.pi ell) := by
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨z, funext hz⟩
    · rintro ⟨z, hz⟩
      exact ⟨z, fun i => congrFun hz i⟩
  rw [hrange, mem_range_iff_coordinate_relations]
  have hrel (u : I → K) :
      (∀ z : V, ∑ i, u i * ell i z = 0) ↔ (∑ i, u i • ell i = 0) := by
    constructor
    · intro h
      ext z
      simpa using h z
    · intro h z
      have := LinearMap.congr_fun h z
      simpa using this
  simp only [LinearMap.pi_apply]
  simp_rw [hrel]

end Duality

section Systems

variable (K I J : Type*) [Field K] [Fintype J] [DecidableEq J]
variable (V : J → Type*) [∀ j, AddCommGroup (V j)] [∀ j, Module K (V j)]

/-- Scopes retain zero-coefficient incidences, as required by the manuscript. -/
structure AffineSystem where
  scope : I → Finset J
  coefficient : ∀ (_i : I) j, V j →ₗ[K] K
  coefficient_outside : ∀ i j, j ∉ scope i → coefficient i j = 0

namespace AffineSystem

variable {K I J V}

def equation (A : AffineSystem K I J V) (i : I) : (∀ j, V j) →ₗ[K] K where
  toFun z := ∑ j, A.coefficient i j (z j)
  map_add' z w := by simp [map_add, Finset.sum_add_distrib]
  map_smul' c z := by simp [map_smul, Finset.mul_sum]

def linearMap (A : AffineSystem K I J V) : (∀ j, V j) →ₗ[K] (I → K) :=
  LinearMap.pi A.equation

def readouts (A : AffineSystem K I J V) (S : Finset I) : Finset J :=
  S.biUnion A.scope

def SolvesOn (A : AffineSystem K I J V) (b : I → K) (S : Finset I)
    (z : ∀ j, V j) : Prop := ∀ i ∈ S, A.equation i z = b i

omit [Fintype J] in
theorem readouts_mono (A : AffineSystem K I J V) {S T : Finset I}
    (h : S ⊆ T) : A.readouts S ⊆ A.readouts T := by
  intro j hj
  obtain ⟨i, hi, hij⟩ := Finset.mem_biUnion.mp hj
  exact Finset.mem_biUnion.mpr ⟨i, h hi, hij⟩

theorem equation_congr (A : AffineSystem K I J V) (i : I)
    {z w : ∀ j, V j} (h : ∀ j ∈ A.scope i, z j = w j) :
    A.equation i z = A.equation i w := by
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j ∈ A.scope i
  · rw [h j hj]
  · simp [A.coefficient_outside i j hj]

theorem solvesOn_congr (A : AffineSystem K I J V) (b : I → K) (S : Finset I)
    {z w : ∀ j, V j} (h : ∀ j ∈ A.readouts S, z j = w j) :
    A.SolvesOn b S z ↔ A.SolvesOn b S w := by
  have heq (i : I) (hi : i ∈ S) : A.equation i z = A.equation i w := by
    apply A.equation_congr
    intro j hj
    exact h j (Finset.mem_biUnion.mpr ⟨i, hi, hj⟩)
  constructor <;> intro hz i hi
  · rw [← heq i hi]
    exact hz i hi
  · rw [heq i hi]
    exact hz i hi

/-- Total assignments represent partial assignments modulo agreement on readouts.
The saturation field makes this representation exact. -/
structure ExactLocalFamily (A : AffineSystem K I J V) (b : I → K) (k : ℕ) where
  assignments : Finset I → Set (∀ j, V j)
  nonempty : ∀ S, S.card ≤ k → (assignments S).Nonempty
  sound : ∀ S, S.card ≤ k → ∀ z ∈ assignments S, A.SolvesOn b S z
  saturated : ∀ S, S.card ≤ k → ∀ z w,
    (∀ j ∈ A.readouts S, z j = w j) →
      (z ∈ assignments S ↔ w ∈ assignments S)
  restrict : ∀ S T, S ⊆ T → T.card ≤ k → assignments T ⊆ assignments S
  extend : ∀ S T, S ⊆ T → T.card ≤ k → ∀ z ∈ assignments S,
    ∃ w ∈ assignments T, ∀ j ∈ A.readouts S, w j = z j

/-- Restriction to the readouts of an equation set, with no irrelevant coordinates. -/
def restriction (A : AffineSystem K I J V) (S : Finset I) (z : ∀ j, V j) :
    ∀ j : {j // j ∈ A.readouts S}, V j.1 := fun j => z j.1

/-- The extension and restriction fields give exactly equality of projected
families, as in the manuscript's definition. -/
theorem ExactLocalFamily.projection_eq {A : AffineSystem K I J V}
    {b : I → K} {k : ℕ} (H : A.ExactLocalFamily b k)
    {S T : Finset I} (hST : S ⊆ T) (hT : T.card ≤ k) :
    A.restriction S '' H.assignments T = A.restriction S '' H.assignments S := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨z, H.restrict S T hST hT hz, rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨w, hw, hagree⟩ := H.extend S T hST hT z hz
    refine ⟨w, hw, ?_⟩
    funext j
    exact hagree j.1 j.2

/-- Every member of a local family extends to a total assignment that has the
required local restriction. This supplies the extension used when changing a
bounded collection of retained equations. -/
theorem ExactLocalFamily.extend_assignment {A : AffineSystem K I J V}
    {b : I → K} {k : ℕ} (H : A.ExactLocalFamily b k)
    {S T : Finset I} (hST : S ⊆ T) (hT : T.card ≤ k)
    {z : ∀ j, V j} (hz : z ∈ H.assignments S) :
    ∃ w, w ∈ H.assignments T ∧ A.SolvesOn b T w ∧
      ∀ j ∈ A.readouts S, w j = z j := by
  obtain ⟨w, hw, hagree⟩ := H.extend S T hST hT z hz
  exact ⟨w, hw, H.sound T hT w hw, hagree⟩

/-- A global solution produces exact local families through every number of blocks. -/
def exactLocalFamilyOfSolution (A : AffineSystem K I J V) (b : I → K)
    (z : ∀ j, V j) (hz : A.linearMap z = b) (k : ℕ) : A.ExactLocalFamily b k where
  assignments S := {w | ∀ j ∈ A.readouts S, w j = z j}
  nonempty S _ := ⟨z, fun _ _ => rfl⟩
  sound S _ w hw := by
    intro i hi
    calc
      A.equation i w = A.equation i z := A.equation_congr i (by
        intro j hj
        exact hw j (Finset.mem_biUnion.mpr ⟨i, hi, hj⟩))
      _ = b i := congrFun hz i
  saturated S _ w w' hw := by
    constructor <;> intro h j hj
    · exact (hw j hj).symm.trans (h j hj)
    · exact (hw j hj).trans (h j hj)
  restrict S T hST _ w hw := fun j hj => hw j (A.readouts_mono hST hj)
  extend S T _ _ w hw := ⟨z, (fun _ _ => rfl), fun j hj => (hw j hj).symm⟩

/-- If the family reaches the complete equation set, it contains a global solution. -/
theorem ExactLocalFamily.solvable_of_card_le [Fintype I]
    {A : AffineSystem K I J V} {b : I → K} {k : ℕ}
    (H : A.ExactLocalFamily b k) (hk : Fintype.card I ≤ k) :
    b ∈ LinearMap.range A.linearMap := by
  obtain ⟨z, hz⟩ := H.nonempty Finset.univ (by simpa using hk)
  refine ⟨z, ?_⟩
  ext i
  exact H.sound Finset.univ (by simpa using hk) z hz i (Finset.mem_univ i)

end AffineSystem
end Systems

section Buffers

variable {K : Type*} [AddCommGroup K]

/-- The rejecting buffer used to allow a full source image and any nonempty
destination image. -/
def rejectingBuffer (T : Set K) (c : K) : Set (K × K) :=
  {z | z.1 + z.2 - c ∈ T}

theorem rejectingBuffer_fst (T : Set K) (hT : T.Nonempty) (c : K) :
    Prod.fst '' rejectingBuffer T c = Set.univ := by
  ext a
  constructor
  · intro _
    trivial
  · intro _
    obtain ⟨t, ht⟩ := hT
    refine ⟨(a, c + t - a), ?_, rfl⟩
    change a + (c + t - a) - c ∈ T
    convert ht using 1; abel

theorem rejectingBuffer_snd (T : Set K) (hT : T.Nonempty) (c : K) :
    Prod.snd '' rejectingBuffer T c = Set.univ := by
  ext a
  constructor
  · intro _
    trivial
  · intro _
    obtain ⟨t, ht⟩ := hT
    refine ⟨(c + t - a, a), ?_, rfl⟩
    change c + t - a + a - c ∈ T
    convert ht using 1; abel

theorem rejectingBuffer_sum (T : Set K) (c : K) :
    (fun z : K × K => z.1 + z.2) '' rejectingBuffer T c =
      (fun t => c + t) '' T := by
  ext a
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.1 + z.2 - c, hz, ?_⟩
    abel
  · rintro ⟨t, ht, rfl⟩
    refine ⟨(0, c + t), ?_, by simp⟩
    change 0 + (c + t) - c ∈ T
    convert ht using 1; abel

omit [AddCommGroup K] in
/-- Fixing both scalar coordinate images fixes the entire two-coordinate buffer. -/
theorem buffer_singleton (B : Set (K × K)) (hB : B.Nonempty) (a b : K)
    (ha : Prod.fst '' B = {a}) (hb : Prod.snd '' B = {b}) :
    B = {(a, b)} := by
  have coords (z : K × K) (hz : z ∈ B) : z = (a, b) := by
    apply Prod.ext
    · have := ha ▸ (show z.1 ∈ Prod.fst '' B from ⟨z, hz, rfl⟩)
      exact Set.mem_singleton_iff.mp this
    · have := hb ▸ (show z.2 ∈ Prod.snd '' B from ⟨z, hz, rfl⟩)
      exact Set.mem_singleton_iff.mp this
  ext z
  constructor
  · intro hz
    exact Set.mem_singleton_iff.mpr (coords z hz)
  · intro hz
    obtain ⟨w, hw⟩ := hB
    have hw' := coords w hw
    simpa [Set.mem_singleton_iff.mp hz, hw'] using hw

theorem buffer_sum_singleton (B : Set (K × K)) (hB : B.Nonempty) (a b : K)
    (ha : Prod.fst '' B = {a}) (hb : Prod.snd '' B = {b}) :
    (fun z : K × K => z.1 + z.2) '' B = {a + b} := by
  rw [buffer_singleton B hB a b ha hb]
  simp

end Buffers

end GroupWL
