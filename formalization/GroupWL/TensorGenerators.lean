import GroupWL.TensorLinearity
import GroupWL.Identification
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Vector-space generators give a group-WL identification bound

Coordinate addition in a tensor group is a group word by the class-two BCH
formula. Prime-field scalar multiplication is an integer power. Therefore
every vector-space basis generates the underlying group. Combining this with
the word-type identification theorem gives the dimension bound for Version II.
-/

namespace GroupWL
namespace TensorGroup

open Refinement

variable {p : ℕ} [Fact p.Prime] [NeZero (2 : ZMod p)]
variable {V Z : Type*} [AddCommGroup V] [Module (ZMod p) V]
  [AddCommGroup Z] [Module (ZMod p) Z]
variable {b : AlternatingBilinearMap (ZMod p) V Z}

omit [NeZero (2 : ZMod p)] in
/-- Scalar multiplication in both coordinates is a group power. -/
theorem coordinate_smul_eq_pow (c : ZMod p) (x : V × Z) :
    (equivProd.symm (c • x) : TensorGroup b) = (equivProd.symm x) ^ c.val := by
  rw [pow_eq]
  ext
  · change c • x.1 = c.val • x.1
    rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
  · change c • x.2 = c.val • x.2
    rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]

/-- A subgroup is a vector subspace in the tensor coordinates. -/
def coordinateSubmodule (S : Subgroup (TensorGroup b)) : Submodule (ZMod p) (V × Z) where
  carrier := {x | equivProd.symm x ∈ S}
  zero_mem' := S.one_mem
  add_mem' := by
    intro x y hx hy
    change coordinateAdd (equivProd.symm x) (equivProd.symm y) ∈ S
    rw [coordinateAdd_eq]
    exact S.mul_mem (S.mul_mem hx hy)
      (S.inv_mem (S.pow_mem (S.mul_mem (S.mul_mem (S.mul_mem hx hy) (S.inv_mem hx))
        (S.inv_mem hy)) _))
  smul_mem' := by
    intro c x hx
    change equivProd.symm (c • x) ∈ S
    rw [coordinate_smul_eq_pow]
    exact S.pow_mem hx _

@[simp] theorem mem_coordinateSubmodule (S : Subgroup (TensorGroup b)) (x : V × Z) :
    x ∈ coordinateSubmodule S ↔ equivProd.symm x ∈ S := Iff.rfl

/-- The subgroup of values of actual finite words in a tuple. -/
def wordSubgroup {k : ℕ} (a : Fin k → TensorGroup b) : Subgroup (TensorGroup b) where
  carrier := {g | ∃ w : GroupWord k, w.eval a = g}
  one_mem' := ⟨.one, rfl⟩
  mul_mem' := by
    rintro g h ⟨w, rfl⟩ ⟨w', rfl⟩
    exact ⟨.mul w w', rfl⟩
  inv_mem' := by
    rintro g ⟨w, rfl⟩
    exact ⟨.inv w, rfl⟩

/-- Any tuple whose coordinate vectors span the entire space generates the
group by finite words. -/
theorem generates_of_coordinate_span {k : ℕ} (a : Fin k → TensorGroup b)
    (hspan : Submodule.span (ZMod p) (Set.range (fun i => equivProd (a i))) = ⊤) :
    Generates a := by
  have hle : Submodule.span (ZMod p) (Set.range (fun i => equivProd (a i))) ≤
      coordinateSubmodule (wordSubgroup a) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨.gen i, rfl⟩
  rw [hspan] at hle
  intro g
  have hg := hle (show equivProd g ∈ (⊤ : Submodule (ZMod p) (V × Z)) from trivial)
  simpa only [mem_coordinateSubmodule, Equiv.symm_apply_apply] using hg

/-- A displayed vector-space basis is an actual generating tuple. -/
theorem generates_basis {d : ℕ} (basis : Module.Basis (Fin d) (ZMod p) (V × Z)) :
    Generates (fun i => (equivProd.symm (basis i) : TensorGroup b)) := by
  apply generates_of_coordinate_span
  simpa only [Equiv.apply_symm_apply] using basis.span_eq

/-- A basis can be padded with identity elements to any larger tuple length. -/
theorem exists_generating_tuple_of_basis_le {d k : ℕ}
    (basis : Module.Basis (Fin d) (ZMod p) (V × Z)) (hdk : d ≤ k) :
    ∃ a : Fin k → TensorGroup b, Generates a := by
  classical
  let a : Fin k → TensorGroup b := fun j =>
    if hj : j.val < d then equivProd.symm (basis ⟨j.val, hj⟩) else 1
  refine ⟨a, generates_of_coordinate_span a ?_⟩
  have hb : Set.range basis ⊆ Set.range (fun i => equivProd (a i)) := by
    rintro _ ⟨i, rfl⟩
    let j : Fin k := ⟨i.val, lt_of_lt_of_le i.isLt hdk⟩
    refine ⟨j, ?_⟩
    simp only [a, j, dif_pos i.isLt, Equiv.apply_symm_apply]
  apply top_unique
  rw [← basis.span_eq]
  exact Submodule.span_mono hb

variable [FiniteDimensional (ZMod p) V] [FiniteDimensional (ZMod p) Z]

/-- The coordinate dimension bounds the number of actual group generators. -/
theorem exists_generating_tuple_of_dimension_le {k : ℕ}
    (hD : Module.finrank (ZMod p) V + Module.finrank (ZMod p) Z ≤ k) :
    ∃ a : Fin k → TensorGroup b, Generates a := by
  apply exists_generating_tuple_of_basis_le (Module.finBasis (ZMod p) (V × Z))
  simpa only [Module.finrank_prod] using hD

/-- Any positive Version-II dimension at least the coordinate dimension
identifies the tensor group among all finite groups. -/
theorem identifiesII_of_dimension_le [Fintype (TensorGroup b)] {k : ℕ}
    (hk : k ≠ 0)
    (hD : Module.finrank (ZMod p) V + Module.finrank (ZMod p) Z ≤ k) :
    IdentifiesII k (TensorGroup b) := by
  obtain ⟨a, ha⟩ := exists_generating_tuple_of_dimension_le (b := b) hD
  exact identifiesII_of_generates hk ha

/-- The safe Version-II cap is `max 1 (dim V + dim Z)`, including the trivial group. -/
theorem identifiesII_at_dimension_cap [Fintype (TensorGroup b)] :
    IdentifiesII (max 1 (Module.finrank (ZMod p) V + Module.finrank (ZMod p) Z))
      (TensorGroup b) :=
  identifiesII_of_dimension_le (by omega) (le_max_right _ _)

end TensorGroup
end GroupWL
