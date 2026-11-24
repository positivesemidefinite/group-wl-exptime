import GroupWL.ShearGame
import GroupWL.Affine

/-!
# Coherent residuals assemble exact shear families

This file proves the linear-algebra-to-game assembly in Section 4.  It keeps
its mathematical inputs explicit: source-state extension, existence of global
lifts, vanishing of residuals, and the relative correction supplied by the
coherence lemma.  In particular, it does not assert that the manuscript's
specific incidence tensor has these properties.
-/

namespace GroupWL
namespace CoherentShears

universe u v w t
variable {F : Type u} {X : Type v} {Z : Type w}
variable [Field F] [AddCommGroup X] [Module F X] [AddCommGroup Z] [Module F Z]
variable (Y : Submodule F (X →ₗ[F] Z)) (ε : AlternatingBilinearMap F X Z)

/-- The relative correction space: the correction vanishes on the retained
input space and each of its operator values annihilates that space. -/
def RelativeCorrection (E : Submodule F X) (b : X →ₗ[F] Y) : Prop :=
  (∀ x ∈ E, b x = 0) ∧ ∀ x : X, ∀ e ∈ E, (b x : X →ₗ[F] Z) e = 0

theorem coboundary_add (α β : X →ₗ[F] Y) (x y : X) :
    shearCoboundary Y (α + β) x y = shearCoboundary Y α x y + shearCoboundary Y β x y := by
  simp only [shearCoboundary_apply, LinearMap.add_apply, Submodule.coe_add]
  abel

theorem coboundary_sub (α β : X →ₗ[F] Y) (x y : X) :
    shearCoboundary Y (α - β) x y = shearCoboundary Y α x y - shearCoboundary Y β x y := by
  simp only [shearCoboundary_apply, LinearMap.sub_apply, Submodule.coe_sub]
  abel

/-- Precise inputs to the residual assembly. `compatible E z w` means that
the new source assignment retains the coordinates already fixed at `E`. -/
structure ResidualData (m : ℕ) (State : Type t) where
  admissible : Submodule F X → State → Prop
  compatible : Submodule F X → State → State → Prop
  residual : Submodule F X → State → AlternatingBilinearMap F X Z
  bottom_nonempty : ∃ z, admissible ⊥ z
  compatible_self : ∀ E z, compatible E z z
  restrict_admissible : ∀ E D : Submodule F X, E ≤ D → Module.finrank F D ≤ m →
    ∀ z, admissible D z → admissible E z
  extend_state : ∀ E D : Submodule F X, E ≤ D → Module.finrank F D ≤ m →
    ∀ z, admissible E z → ∃ w, admissible D w ∧ compatible E z w
  vanishes : ∀ E z, admissible E z → ∀ x ∈ E, ∀ y, residual E z x y = 0
  global_lift : ∀ E : Submodule F X, Module.finrank F E ≤ m →
    ∀ z, admissible E z → ∃ α : X →ₗ[F] Y,
      ∀ x y, shearCoboundary Y α x y = ε x y - residual E z x y
  correction : ∀ E D : Submodule F X, E ≤ D → Module.finrank F D ≤ m →
    ∀ z w, admissible E z → admissible D w → compatible E z w →
      ∃ b : X →ₗ[F] Y, RelativeCorrection Y E b ∧
        ∀ x y, shearCoboundary Y b x y = residual D w x y - residual E z x y

variable {Y ε} {m : ℕ} {State : Type t}

/-- A global lift is a representative of the local shear at `E`. -/
def Witness (R : ResidualData Y ε m State) (E : Submodule F X) (α : X →ₗ[F] Y) : Prop :=
  ∃ z, R.admissible E z ∧
    ∀ x y, shearCoboundary Y α x y = ε x y - R.residual E z x y

/-- Extend a shear without changing any of its old input values. -/
theorem extend_witness (R : ResidualData Y ε m State)
    {E D : Submodule F X} (hED : E ≤ D) (hD : Module.finrank F D ≤ m)
    {α : X →ₗ[F] Y} (hα : Witness R E α) :
    ∃ β, Witness R D β ∧ ∀ x ∈ E, β x = α x := by
  obtain ⟨z, hz, hα⟩ := hα
  obtain ⟨w, hw, hzw⟩ := R.extend_state E D hED hD z hz
  obtain ⟨b, hb, hcb⟩ := R.correction E D hED hD z w hz hw hzw
  refine ⟨α - b, ⟨w, hw, ?_⟩, ?_⟩
  · intro x y
    rw [coboundary_sub, hα, hcb]
    abel
  · intro x hx
    simp [hb.1 x hx]

/-- Restrict a shear by using the same total source assignment and adding the
relative correction.  The correction is zero on the smaller input space. -/
theorem restrict_witness (R : ResidualData Y ε m State)
    {E D : Submodule F X} (hED : E ≤ D) (hD : Module.finrank F D ≤ m)
    {α : X →ₗ[F] Y} (hα : Witness R D α) :
    ∃ β, Witness R E β ∧ ∀ x ∈ E, β x = α x := by
  obtain ⟨z, hz, hα⟩ := hα
  have hzE := R.restrict_admissible E D hED hD z hz
  obtain ⟨b, hb, hcb⟩ := R.correction E D hED hD z z hzE hz (R.compatible_self E z)
  refine ⟨α + b, ⟨z, hzE, ?_⟩, ?_⟩
  · intro x y
    rw [coboundary_add, hα, hcb]
    abel
  · intro x hx
    simp [hb.1 x hx]

/-- The exact subspace family is constructed from the residual data. -/
def ResidualData.exactFamily (R : ResidualData Y ε m State) :
    ShearGame.ExactSubspaceFamily (Y := Y) (ε := ε) m where
  maps E := {α | Witness R E α}
  bot_nonempty := by
    obtain ⟨z, hz⟩ := R.bottom_nonempty
    obtain ⟨α, hα⟩ := R.global_lift ⊥ (by simp) z hz
    exact ⟨α, z, hz, hα⟩
  local_law E hE α hα := by
    obtain ⟨z, hz, hα⟩ := hα
    intro x hx y hy
    rw [hα, R.vanishes E z hz x hx y, sub_zero]
  restrict E D hED hD α hα := restrict_witness R hED hD hα
  extend E D hED hD α hα := extend_witness R hED hD hα

/-- Complete assembly from coherent residual data to a winning strategy in the
actual group game.  The displayed `ResidualData` obligations remain explicit. -/
theorem winning_of_coherent_residuals [DecidableEq X] (R : ResidualData Y ε m State) :
    PebbleGame.Winning (PebbleGame.empty :
      PebbleGame.Position m (ShearGame.Source Y) (ShearGame.Target Y ε)) :=
  ShearGame.winning_of_exactSubspaceFamily R.exactFamily

section AffineAdapter
variable {I J : Type*} [Fintype J] [DecidableEq J]
variable {V : J → Type*} [∀ j, AddCommGroup (V j)] [∀ j, Module F (V j)]

/-- The affine exact family discharges the source-state obligations of the
coherent-residual data.  Only the tensor-specific algebraic obligations remain
as arguments of this constructor. -/
def residualDataOfAffine (A : AffineSystem F I J V) (β : I → F) (k : ℕ)
    (H : A.ExactLocalFamily β k)
    (owners : Submodule F X → Finset I)
    (owner_mono : Monotone owners)
    (owner_bound : ∀ E : Submodule F X, Module.finrank F E ≤ m → (owners E).card ≤ k)
    (ρ : Submodule F X → (∀ j, V j) → AlternatingBilinearMap F X Z)
    (hvanish : ∀ E z, z ∈ H.assignments (owners E) → ∀ x ∈ E, ∀ y, ρ E z x y = 0)
    (hlift : ∀ E : Submodule F X, Module.finrank F E ≤ m → ∀ z ∈ H.assignments (owners E),
      ∃ α : X →ₗ[F] Y, ∀ x y, shearCoboundary Y α x y = ε x y - ρ E z x y)
    (hcorrection : ∀ E D : Submodule F X, E ≤ D → Module.finrank F D ≤ m →
      ∀ z w, z ∈ H.assignments (owners E) → w ∈ H.assignments (owners D) →
      (∀ j ∈ A.readouts (owners E), z j = w j) →
      ∃ b : X →ₗ[F] Y, RelativeCorrection Y E b ∧
        ∀ x y, shearCoboundary Y b x y = ρ D w x y - ρ E z x y) :
    ResidualData Y ε m (∀ j, V j) where
  admissible E z := z ∈ H.assignments (owners E)
  compatible E z w := ∀ j ∈ A.readouts (owners E), z j = w j
  residual := ρ
  bottom_nonempty := H.nonempty (owners ⊥) (owner_bound ⊥ (by simp))
  compatible_self _ _ := fun _ _ => rfl
  restrict_admissible E D hED hD z hz :=
    H.restrict (owners E) (owners D) (owner_mono hED) (owner_bound D hD) hz
  extend_state E D hED hD z hz := by
    obtain ⟨w, hw, hagree⟩ :=
      H.extend (owners E) (owners D) (owner_mono hED) (owner_bound D hD) z hz
    exact ⟨w, hw, fun j hj => (hagree j hj).symm⟩
  vanishes := hvanish
  global_lift := hlift
  correction := hcorrection

end AffineAdapter

end CoherentShears
end GroupWL
