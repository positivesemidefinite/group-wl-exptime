import GroupWL.GameRefinement
import GroupWL.CoherentShears

/-! # Coherent residuals imply Version-II WL equivalence

This joins the proved residual assembly to the proved game-to-refinement
bridge. The specific residual construction is still an explicit premise.
-/

namespace GroupWL

universe u v w t
variable {F : Type u} {X : Type v} {Z : Type w}
variable [Field F] [AddCommGroup X] [Module F X] [AddCommGroup Z] [Module F Z]
variable (Y : Submodule F (X →ₗ[F] Z)) (ε : AlternatingBilinearMap F X Z)
variable {k : ℕ} [DecidableEq X]
variable [Fintype (ShearGame.Source Y)] [Fintype (ShearGame.Target Y ε)]

/-- Exact local shear families give equality of the actual shared WL-color
histograms at every round. The parameter shift is the stated `k+1` pairs. -/
theorem equivalentII_of_exact_shear_family
    (P : ShearGame.ExactSubspaceFamily (Y := Y) (ε := ε) (k+1)) :
    Refinement.EquivalentII k (ShearGame.Source Y) (ShearGame.Target Y ε) :=
  GameRefinement.equivalentII_of_winning_empty k
    (ShearGame.winning_of_exactSubspaceFamily P)

/-- Coherent residuals imply genuine Version-II equivalence, rather than an
uninterpreted game relation. -/
theorem equivalentII_of_coherent_residuals {State : Type t}
    (R : CoherentShears.ResidualData Y ε (k+1) State) :
    Refinement.EquivalentII k (ShearGame.Source Y) (ShearGame.Target Y ε) :=
  equivalentII_of_exact_shear_family Y ε R.exactFamily

end GroupWL
