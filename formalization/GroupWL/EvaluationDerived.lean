import GroupWL.TensorGroup
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Subgroup.Center

/-! # Center and derived subgroup of evaluation groups

The surjectivity hypothesis is an ordinary finite-dimensional algebra property;
this file converts it into an explicit commutator for every output vector.
-/

namespace GroupWL

universe u v w

namespace TensorGroup

variable {F : Type u} {V : Type v} {Z : Type w}
variable [Field F] [AddCommGroup V] [Module F V] [AddCommGroup Z] [Module F Z]

/-- The output sector, as an actual subgroup. -/
def outputSubgroup (b : AlternatingBilinearMap F V Z) : Subgroup (TensorGroup b) where
  carrier := {g | g.fst = 0}
  one_mem' := rfl
  mul_mem' := by
    intro g h hg hh
    change g.fst = 0 at hg
    change h.fst = 0 at hh
    change g.fst + h.fst = 0
    rw [hg, hh, zero_add]
  inv_mem' := by
    intro g hg
    change g.fst = 0 at hg
    change -g.fst = 0
    rw [hg, neg_zero]

@[simp] theorem mem_outputSubgroup (b : AlternatingBilinearMap F V Z) (g : TensorGroup b) :
    g ∈ outputSubgroup b ↔ g.fst = 0 := Iff.rfl

/-- Every tensor-group commutator belongs to the output sector. -/
theorem commutator_le_output (b : AlternatingBilinearMap F V Z) :
    commutator (TensorGroup b) ≤ outputSubgroup b := by
  apply Subgroup.commutator_le.mpr
  intro g _ h _
  rw [commutatorElement_def, commutator_eq_double]
  rfl

/-- The center equals the output sector when the tensor has zero radical. -/
theorem center_eq_output [NeZero (2 : F)] (b : AlternatingBilinearMap F V Z)
    (hrad : ∀ v : V, (∀ w : V, b v w = 0) → v = 0) :
    Subgroup.center (TensorGroup b) = outputSubgroup b := by
  ext g
  rw [Subgroup.mem_center_iff, mem_outputSubgroup]
  simpa only [eq_comm] using central_iff_fst_eq_zero hrad g

end TensorGroup

section Evaluation

variable {F : Type u} {X : Type v} {Z : Type w}
variable [Field F] [AddCommGroup X] [Module F X] [AddCommGroup Z] [Module F Z]
variable [NeZero (2 : F)]

open scoped commutatorElement

/-- Each output vector is one commutator if evaluation is onto at a single input. -/
theorem output_is_commutator
    (Y : Submodule F (X →ₗ[F] Z)) (ε : AlternatingBilinearMap F X Z)
    (x : X) (heval : ∀ z : Z, ∃ y : Y, (y : X →ₗ[F] Z) x = z) (z : Z) :
    ∃ g h : TensorGroup (evaluationTwist Y ε), ⁅g, h⁆ = ⟨0, z⟩ := by
  obtain ⟨y, hy⟩ := heval z
  refine ⟨⟨(x, 0), 0⟩, ⟨(0, y), 0⟩, ?_⟩
  rw [commutatorElement_def, TensorGroup.commutator_eq]
  congr 1
  simpa using hy

/-- Evaluation surjectivity identifies the actual derived subgroup. -/
theorem evaluationGroup_derived_eq_output
    (Y : Submodule F (X →ₗ[F] Z)) (ε : AlternatingBilinearMap F X Z)
    (x : X) (heval : ∀ z : Z, ∃ y : Y, (y : X →ₗ[F] Z) x = z) :
    commutator (TensorGroup (evaluationTwist Y ε)) =
      TensorGroup.outputSubgroup (evaluationTwist Y ε) := by
  apply le_antisymm (TensorGroup.commutator_le_output _)
  intro g hg
  obtain ⟨a, b, hab⟩ := output_is_commutator Y ε x heval g.snd
  have hg' : g = ⟨0, g.snd⟩ := TensorGroup.ext hg rfl
  rw [hg', ← hab]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)

/-- With operator separation and onto evaluation, the center and derived
subgroup coincide, as asserted for the construction in the manuscript. -/
theorem evaluationGroup_center_eq_derived
    (Y : Submodule F (X →ₗ[F] Z)) (ε : AlternatingBilinearMap F X Z)
    (hsep : ∀ x : X, (∀ y : Y, (y : X →ₗ[F] Z) x = 0) → x = 0)
    (x : X) (heval : ∀ z : Z, ∃ y : Y, (y : X →ₗ[F] Z) x = z) :
    Subgroup.center (TensorGroup (evaluationTwist Y ε)) =
      commutator (TensorGroup (evaluationTwist Y ε)) := by
  rw [evaluationGroup_derived_eq_output Y ε x heval]
  exact TensorGroup.center_eq_output _ (evaluationTwist_radical_eq_zero Y ε hsep)

end Evaluation

end GroupWL
