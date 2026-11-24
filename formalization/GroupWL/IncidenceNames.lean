import GroupWL.FreeAnchors
import GroupWL.FormulaRename

/-! # Coordinate formulas instantiated at the actual incidence groups -/
namespace GroupWL.IncidenceNames

open IncidenceTensor IncidenceCoordinates FreeAnchors CoordinateNames Refinement CountingLogic Module
variable {p : ℕ} [Fact p.Prime]
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {V : J → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module (ZMod p) (V j)]
variable (A : AffineSystem (ZMod p) I J V) (q : ℕ)

abbrev X := InputIndex A q → ZMod p
abbrev Z := OutputIndex A q → ZMod p

/-- The free-output component, expressed as an input coordinate label. -/
noncomputable def centralInput₀ (z : Z A q) : X A q :=
  inputCoordinates A q ((outputCoordinates A q).symm z).2

/-- The original-output component, placed in its free input copy. -/
noncomputable def centralInput₁ (z : Z A q) : X A q :=
  inputCoordinates A q (0, ((outputCoordinates A q).symm z).1)

theorem central_decomposition (hq : 0 < q) (z : Z A q) :
    (identityAnchor A q hq : X A q →ₗ[ZMod p] Z A q) (centralInput₀ A q z) +
      (outputAnchor A q hq : X A q →ₗ[ZMod p] Z A q) (centralInput₁ A q z) = z := by
  simp only [centralInput₀, centralInput₁, identityAnchor_apply, outputAnchor_apply,
    LinearEquiv.symm_apply_apply]
  rw [← map_add]
  simpa using (outputCoordinates A q).apply_symm_apply z

variable {n : ℕ} (basis : Basis (Fin n) (ZMod p) (X A q))

noncomputable def quotientFormula {m : ℕ} (a₀ a₁ t u v : Fin m)
    (x : X A q) (w : GroupWord m) : Formula m :=
  quotientWordName a₀ a₁ t u v (coordinateCode basis x) w

noncomputable def centralFormula {m : ℕ} (a₀ a₁ t b u v h : Fin m)
    (z : Z A q) (w : GroupWord m) : Formula m :=
  centralName a₀ a₁ t b u v h
    (coordinateCode basis (centralInput₀ A q z))
    (coordinateCode basis (centralInput₁ A q z)) w

noncomputable def matrixFormula (hq : 0 < q) (y : operators A q hq) : Formula 9 :=
  matrixName (fun i => coordinateCode basis (basis i))
    (fun i => coordinateCode basis (centralInput₀ A q ((y : X A q →ₗ[ZMod p] Z A q) (basis i))))
    (fun i => coordinateCode basis (centralInput₁ A q ((y : X A q →ₗ[ZMod p] Z A q) (basis i))))

variable [NeZero (2 : ZMod p)] (hq : 0 < q)
variable (ε : AlternatingBilinearMap (ZMod p) (X A q) (Z A q))

theorem quotientFormula_realize {m : ℕ} (a₀ a₁ t u v : Fin m) (huv : u ≠ v)
    (hu : u ∉ ({a₀, a₁, t} : Finset (Fin m)))
    (hv : v ∉ ({a₀, a₁, t} : Finset (Fin m)))
    (x : X A q) (w : GroupWord m) (hw : u ∉ wordVariables w)
    (a : Fin m → TensorGroup (evaluationTwist (operators A q hq) ε))
    (ha₀ : (a a₀).fst = (0, identityAnchor A q hq))
    (ha₁ : (a a₁).fst = (0, endomorphismAnchor A q hq (shiftBasis basis)))
    (hseed : (a t).fst.1 = basisSeed basis) :
    (quotientFormula A q basis a₀ a₁ t u v x w).Realize a ↔ (w.eval a).fst.1 = x := by
  unfold quotientFormula
  rw [realize_quotientWordName _ ε a₀ a₁ t u v huv hu hv
    (identityAnchor A q hq) (endomorphismAnchor A q hq (shiftBasis basis))
    (identityAnchor_injective A q hq) (shiftBasis basis)
    (endomorphismAnchor_apply A q hq (shiftBasis basis)) _ w hw a ha₀ ha₁]
  rw [hseed, hornerValue_coordinateCode_all]

theorem centralFormula_realize {m : ℕ} (a₀ a₁ t b u v h : Fin m)
    (huv : u ≠ v) (huh : u ≠ h) (hvh : v ≠ h)
    (hu : u ∉ ({a₀, a₁, t, b} : Finset (Fin m)))
    (hv : v ∉ ({a₀, a₁, t, b} : Finset (Fin m)))
    (hh : h ∉ ({a₀, a₁, t} : Finset (Fin m)))
    (z : Z A q) (w : GroupWord m) (hw : u ∉ wordVariables w ∧ v ∉ wordVariables w)
    (a : Fin m → TensorGroup (evaluationTwist (operators A q hq) ε))
    (ha₀ : (a a₀).fst = (0, identityAnchor A q hq))
    (ha₁ : (a a₁).fst = (0, endomorphismAnchor A q hq (shiftBasis basis)))
    (hb : (a b).fst = (0, outputAnchor A q hq))
    (hseed : (a t).fst.1 = basisSeed basis) :
    (centralFormula A q basis a₀ a₁ t b u v h z w).Realize a ↔
      w.eval a = ⟨0, z⟩ := by
  unfold centralFormula
  rw [realize_centralName _ ε a₀ a₁ t b u v h huv huh hvh hu hv hh
    (identityAnchor A q hq) (endomorphismAnchor A q hq (shiftBasis basis)) (outputAnchor A q hq)
    (identityAnchor_injective A q hq) (shiftBasis basis)
    (endomorphismAnchor_apply A q hq (shiftBasis basis)) _ _ w hw a ha₀ ha₁ hb]
  rw [hseed, hornerValue_coordinateCode_all, hornerValue_coordinateCode_all,
    central_decomposition]

theorem matrixFormula_realize (y : operators A q hq)
    (a : Fin 9 → TensorGroup (evaluationTwist (operators A q hq) ε))
    (ha₀ : (a 0).fst = (0, identityAnchor A q hq))
    (ha₁ : (a 1).fst = (0, endomorphismAnchor A q hq (shiftBasis basis)))
    (hb : (a 3).fst = (0, outputAnchor A q hq))
    (hseed : (a 2).fst.1 = basisSeed basis) :
    (matrixFormula A q basis hq y).Realize a ↔ (a 4).fst = (0, y) := by
  unfold matrixFormula
  apply realize_matrixName_basis _ ε _ _ _
    (identityAnchor A q hq) (endomorphismAnchor A q hq (shiftBasis basis))
    (outputAnchor A q hq) y (identityAnchor_injective A q hq) (shiftBasis basis)
    (endomorphismAnchor_apply A q hq (shiftBasis basis)) a ha₀ ha₁ hb basis
  · intro i
    rw [hseed, hornerValue_coordinateCode_all]
  · intro i
    rw [hseed, hornerValue_coordinateCode_all, hornerValue_coordinateCode_all]
    exact central_decomposition A q hq _

end GroupWL.IncidenceNames
