import GroupWL.RelativeGoodVertices
import GroupWL.ResidualCorrection

/-! # Owner sets for the actual coherent residual construction -/
namespace GroupWL.ResidualAssembly

set_option linter.unusedSectionVars false

open IncidenceTensor IncidenceCoordinates ResidualTensors

universe u
variable {F I J : Type u} [Field F] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {V : J → Type u} [∀ j, AddCommGroup (V j)] [∀ j, Module F (V j)]
variable (A : AffineSystem F I J V) (q : ℕ)

/-- Equations own themselves; each readout has one fixed incident owner. -/
def vertexOwner (owner : J → I) : I ⊕ J → I := Sum.elim id owner

/-- Exactly the equation owners of bad vertices at the retained span. -/
noncomputable def owners (owner : J → I)
    (E : Submodule F (InputIndex A q → F)) : Finset I :=
  BadBudget.ownerSet (vertexOwner owner) (IncidenceBudget.scalarSubspace A q)
    (physicalRetained A q E) q

theorem owners_mono (owner : J → I) : Monotone (owners A q owner) := by
  intro E D hED
  exact BadBudget.ownerSet_mono _ _ (Submodule.map_mono hED) q

theorem owners_bound (owner : J → I) (K m : ℕ) (hq : 1 < q)
    (hm : m < (q - 1) * (K + 1))
    (E : Submodule F (InputIndex A q → F)) (hE : Module.finrank F E ≤ m) :
    (owners A q owner E).card ≤ K :=
  coordinate_owner_budget A q (vertexOwner owner) K hq E (hE.trans_lt hm)

theorem owner_mem_of_bad (owner : J → I)
    (E : Submodule F (InputIndex A q → F)) (v : I ⊕ J)
    (hv : v ∈ IncidenceBudget.badVertices A q (physicalRetained A q E)) :
    vertexOwner owner v ∈ owners A q owner E := by
  classical
  simp only [owners, BadBudget.ownerSet, Finset.mem_image]
  exact ⟨v, hv, rfl⟩

theorem equation_mem_owners_of_not_good (owner : J → I)
    (E : Submodule F (InputIndex A q → F)) (i : I) (hi : ¬ Good A q E i) :
    i ∈ owners A q owner E := by
  apply owner_mem_of_bad A q owner E (.inl i)
  simpa only [good_iff_not_bad, not_not] using hi

/-- Admissible assignments solve every bad equation. -/
theorem admissible_solves_bad (owner : J → I) (β : I → F) (K : ℕ)
    (H : A.ExactLocalFamily β K) (E : Submodule F (InputIndex A q → F))
    (hcard : (owners A q owner E).card ≤ K)
    (z : ∀ j, V j) (hz : z ∈ H.assignments (owners A q owner E)) :
    ∀ i, ¬ Good A q E i → A.equation i z = β i := by
  intro i hi
  exact H.sound _ hcard z hz i (equation_mem_owners_of_not_good A q owner E i hi)

/-- A changed readout cannot be bad: its fixed owner would pin it. -/
theorem changed_readout_good (owner : J → I) (howner : ∀ j, j ∈ A.scope (owner j))
    (E : Submodule F (InputIndex A q → F)) (z w : ∀ j, V j)
    (hagree : ∀ j ∈ A.readouts (owners A q owner E), z j = w j)
    (j : J) (hj : w j ≠ z j) : GoodVertex A (queryInput A q E) (.inr j) := by
  rw [goodVertex_iff_not_bad]
  intro hbad
  have ho := owner_mem_of_bad A q owner E (.inr j) hbad
  exact hj (hagree j (Finset.mem_biUnion.mpr ⟨owner j, ho, howner j⟩)).symm

/-- Every equation incident to a changed readout is good, since a bad
equation pins all the readouts in its scope. -/
theorem changed_readout_good_star (owner : J → I)
    (E : Submodule F (InputIndex A q → F)) (z w : ∀ j, V j)
    (hagree : ∀ j ∈ A.readouts (owners A q owner E), z j = w j)
    (j : J) (hj : w j ≠ z j) (i : I) (hij : j ∈ A.scope i) :
    GoodVertex A (queryInput A q E) (.inl i) := by
  apply goodVertex_of_good
  by_contra hi
  have ho := equation_mem_owners_of_not_good A q owner E i hi
  exact hj (hagree j (Finset.mem_biUnion.mpr ⟨i, ho, hij⟩)).symm

/-- All residual obligations are discharged for the actual incidence tensor.
The only source input is its exact affine family and a genuine incident owner
for each readout. -/
noncomputable def residualData (h2 : (2 : F) ≠ 0) (hq : 2 ≤ q)
    (β : I → F) (K m : ℕ) (hm : m < (q - 1) * (K + 1))
    (owner : J → I) (howner : ∀ j, j ∈ A.scope (owner j))
    (H : A.ExactLocalFamily β K) :
    CoherentShears.ResidualData (MatrixEvaluationGroup.operatorSpace (GlobalCokernel.C A q (by omega)))
      (GlobalCokernel.canonicalTwist A q (epsilonCharge A q hq β)) m (∀ j, V j) := by
  apply CoherentShears.residualDataOfAffine A β K H
    (owners A q owner) (owners_mono A q owner)
    (owners_bound A q owner K m (by omega) hm)
    (ResidualTensors.residual A q β)
  · intro E z _ x hx y
    exact residual_vanishes A q β E z x hx y
  · intro E hE z hz
    exact residual_global_lift A q h2 hq β E z
      (admissible_solves_bad A q owner β K H E
        (owners_bound A q owner K m (by omega) hm E hE) z hz)
  · intro E D hED hD z w hz hw hagree
    have hE : Module.finrank F E ≤ m := (Submodule.finrank_mono hED).trans hD
    apply ResidualCorrection.residual_correction A q h2 hq E D hED β z w
      (admissible_solves_bad A q owner β K H E
        (owners_bound A q owner K m (by omega) hm E hE) z hz)
      (admissible_solves_bad A q owner β K H D
        (owners_bound A q owner K m (by omega) hm D hD) w hw)
    intro j hj
    refine ⟨changed_readout_good A q owner howner E z w hagree j hj, ?_⟩
    intro i hij
    exact good_of_goodVertex A q E i
      (changed_readout_good_star A q owner E z w hagree j hj i hij)

/-- The affine exact family therefore supplies exact shears on every retained
subspace within the stated dimension budget. -/
noncomputable def exactShearFamily (h2 : (2 : F) ≠ 0) (hq : 2 ≤ q)
    (β : I → F) (K m : ℕ) (hm : m < (q - 1) * (K + 1))
    (owner : J → I) (howner : ∀ j, j ∈ A.scope (owner j))
    (H : A.ExactLocalFamily β K) :
    ShearGame.ExactSubspaceFamily
      (Y := MatrixEvaluationGroup.operatorSpace (GlobalCokernel.C A q (by omega)))
      (ε := GlobalCokernel.canonicalTwist A q (epsilonCharge A q hq β)) m :=
  (residualData A q h2 hq β K m hm owner howner H).exactFamily

/-- A concrete winning strategy in the tensor-group bijective pebble game,
with no residual, multiplier, or duality assumptions left to discharge. -/
theorem winning_of_exactAffineFamily (h2 : (2 : F) ≠ 0) (hq : 2 ≤ q)
    (β : I → F) (K m : ℕ) (hm : m < (q - 1) * (K + 1))
    (owner : J → I) (howner : ∀ j, j ∈ A.scope (owner j))
    (H : A.ExactLocalFamily β K) :
    PebbleGame.Winning (PebbleGame.empty : PebbleGame.Position m
      (ShearGame.Source (MatrixEvaluationGroup.operatorSpace (GlobalCokernel.C A q (by omega))))
      (ShearGame.Target (MatrixEvaluationGroup.operatorSpace (GlobalCokernel.C A q (by omega)))
        (GlobalCokernel.canonicalTwist A q (epsilonCharge A q hq β)))) := by
  classical
  exact CoherentShears.winning_of_coherent_residuals
    (residualData A q h2 hq β K m hm owner howner H)

end GroupWL.ResidualAssembly
