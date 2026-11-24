import GroupWL.Recognition

/-! Recovering linearity and the second exact sequence from the actual
cross-commutator evaluations. -/

namespace GroupWL.Recognition

section Linear

variable {F A X Z : Type*} [Field F]
  [AddCommGroup A] [Module F A] [AddCommGroup X] [Module F X]
  [AddCommGroup Z] [Module F Z]
  (b : AlternatingBilinearMap F A A) (Y : Submodule F (X →ₗ[F] Z))
  (q : A →ₗ[F] X) (hq : Function.Surjective q)
  (c : Z →ₗ[F] A) (hc : Function.Injective c)
  (op : LinearMap.ker q → Y)
  (heval : ∀ a (m : LinearMap.ker q), b a m = c ((op m : X →ₗ[F] Z) (q a)))

/-- Linearity of the recovered operators is forced by commutator bilinearity,
injective central coordinates, and surjective quotient coordinates. -/
def operatorLinear : LinearMap.ker q →ₗ[F] Y where
  toFun := op
  map_add' m m' := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    obtain ⟨a, rfl⟩ := hq x
    apply hc
    change c ((op (m + m') : X →ₗ[F] Z) (q a)) =
      c ((op m : X →ₗ[F] Z) (q a) + (op m' : X →ₗ[F] Z) (q a))
    rw [← heval, map_add, ← heval, ← heval]
    exact b.add_right _ _ _
  map_smul' r m := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    obtain ⟨a, rfl⟩ := hq x
    apply hc
    change c ((op (r • m) : X →ₗ[F] Z) (q a)) =
      c (r • (op m : X →ₗ[F] Z) (q a))
    rw [← heval, map_smul, ← heval]
    exact b.smul_right _ _ _

@[simp] theorem operatorLinear_apply (m : LinearMap.ker q) :
    operatorLinear b Y q hq c hc op heval m = op m := rfl

end Linear

section Baer

variable {p : ℕ} [Fact p.Prime] {H X Z : Type*} [Group H]
  [AddCommGroup X] [Module (ZMod p) X] [AddCommGroup Z] [Module (ZMod p) Z]
  (D : Baer.Data p H) (Y : Submodule (ZMod p) (X →ₗ[ZMod p] Z))
  (q : Baer.Data.Vector D →ₗ[ZMod p] X) (hq : Function.Surjective q)
  (c : Z →ₗ[ZMod p] Baer.Data.Vector D) (hc : Function.Injective c)
  (hcrange : LinearMap.range c = D.centerSubmodule)
  (hcq : ∀ z, q (c z) = 0)
  (op : LinearMap.ker q → Y) (hop : Function.Surjective op)
  (heval : ∀ a (m : LinearMap.ker q), D.bracket a m = c ((op m : X →ₗ[ZMod p] Z) (q a)))

include hq hc heval in
theorem operator_eq_zero_iff_center (m : LinearMap.ker q) :
    op m = 0 ↔ m.val ∈ D.centerSubmodule := by
  constructor
  · intro hm
    rw [D.mem_centerSubmodule]
    intro a
    apply (D.bracket_zero_iff_commute ⟨a⟩ m.val).mp
    rw [heval, hm]
    simp
  · intro hm
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    obtain ⟨a, rfl⟩ := hq x
    apply hc
    change c ((op m : X →ₗ[ZMod p] Z) (q a)) = c 0
    rw [← heval, D.bracket_center_right hm, map_zero]

/-- Complete coordinate maps are obtained from these proved evaluation
identities; the center and both kernels are determined, not postulated. -/
def coordinateMapsOfEvaluations : CoordinateMaps D.bracket Y where
  matrix := LinearMap.ker q
  quotient := q
  quotient_surjective := hq
  quotient_kernel := rfl
  center := c
  center_injective := hc
  center_mem := hcq
  operator := operatorLinear D.bracket Y q hq c hc op heval
  operator_surjective := hop
  operator_kernel := by
    ext m
    change op m = 0 ↔ m ∈ LinearMap.range (c.codRestrict (LinearMap.ker q) hcq)
    rw [operator_eq_zero_iff_center D Y q hq c hc op heval m, ← hcrange]
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨z, Subtype.ext hz⟩
    · rintro ⟨z, hz⟩
      exact ⟨z, congrArg Subtype.val hz⟩
  commutator_range := by
    intro a a'
    rw [hcrange]
    exact D.bracket_mem_center a a'
  evaluation := heval

end Baer

end GroupWL.Recognition
