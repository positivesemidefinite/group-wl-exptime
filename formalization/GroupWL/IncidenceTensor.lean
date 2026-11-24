import GroupWL.Affine
import GroupWL.TensorGroup
import GroupWL.RankBound
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Data.Quot
import Mathlib.Logic.Relation

set_option linter.unusedSectionVars false

namespace GroupWL
namespace IncidenceTensor

universe u

variable {F I J : Type u} [Field F] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {V : J → Type u} [∀ j, AddCommGroup (V j)] [∀ j, Module F (V j)]

variable (A : AffineSystem F I J V)

/-- Incidences are retained even for a zero coefficient. -/
abbrev Incidence := {ij : I × J // ij.2 ∈ A.scope ij.1}

/-- The equations incident to one readout. -/
abbrev Neighbors (j : J) := {i : I // j ∈ A.scope i}

/-- The relation map whose kernel is the radical of the readout algebra. -/
def relationMap (j : J) : (Neighbors A j → F) →ₗ[F] (V j →ₗ[F] F) where
  toFun h := ∑ i, h i • A.coefficient i.1 j
  map_add' h k := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c h := by simp [Finset.smul_sum, smul_smul]

/-- The readout radical, including every linear relation among its incidences. -/
abbrev ReadoutRadical (j : J) := LinearMap.ker (relationMap A j)

/-- One radical space for each equation or readout vertex. -/
abbrev Radical : I ⊕ J → Type _
  | .inl _ => F
  | .inr j => ↥(ReadoutRadical A j)

instance radicalAddCommGroup : (v : I ⊕ J) → AddCommGroup (Radical A v)
  | .inl _ => inferInstanceAs (AddCommGroup F)
  | .inr j => inferInstanceAs (AddCommGroup (ReadoutRadical A j))
instance radicalModule : (v : I ⊕ J) → Module F (Radical A v)
  | .inl _ => inferInstanceAs (Module F F)
  | .inr j => inferInstanceAs (Module F (ReadoutRadical A j))
instance radicalOppositeModule : (v : I ⊕ J) → Module Fᵐᵒᵖ (Radical A v)
  | .inl _ => inferInstanceAs (Module Fᵐᵒᵖ F)
  | .inr j => inferInstanceAs (Module Fᵐᵒᵖ (ReadoutRadical A j))
instance radicalCentralScalar : (v : I ⊕ J) → IsCentralScalar F (Radical A v)
  | .inl _ => inferInstanceAs (IsCentralScalar F F)
  | .inr j => inferInstanceAs (IsCentralScalar F (ReadoutRadical A j))
instance radicalFiniteDimensional : (v : I ⊕ J) → Module.Finite F (Radical A v)
  | .inl _ => inferInstanceAs (Module.Finite F F)
  | .inr j => inferInstanceAs (Module.Finite F (ReadoutRadical A j))

/-- The actual square-zero algebra at a vertex. -/
abbrev RingAt (v : I ⊕ J) := TrivSqZeroExt F (Radical A v)

/-- Every incidence output uses the dual numbers over the base field. -/
abbrev EdgeRing := TrivSqZeroExt F F

/-- Distinct unordered coordinate pairs, represented in increasing order. -/
abbrev Pair (q : ℕ) := {ab : Fin q × Fin q // ab.1 < ab.2}

/-- The original input space. -/
abbrev OldInput (q : ℕ) := ∀ v : I ⊕ J, Fin q → RingAt A v

/-- The original output space: internal wedges and incidence wedges. -/
abbrev OldOutput (q : ℕ) :=
  (∀ v : I ⊕ J, Pair q → RingAt A v) × (Incidence A → Fin q × Fin q → EdgeRing (F := F))

/-- Coordinate projection of a readout relation at an actual incidence. -/
def readoutProjection (e : Incidence A) : ReadoutRadical A e.1.2 →ₗ[F] F where
  toFun h := h.val ⟨e.1.1, e.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The readout endpoint map into the incidence dual-number algebra. -/
def endpointMap (e : Incidence A) : RingAt A (.inr e.1.2) →ₐ[F] EdgeRing (F := F) :=
  TrivSqZeroExt.map (readoutProjection A e)

/-- Explicit coordinates of the incidence alternating tensor. -/
def omegaFun (q : ℕ) (x x' : OldInput A q) : OldOutput A q :=
  (fun v ab => x v ab.1.1 * x' v ab.1.2 - x' v ab.1.1 * x v ab.1.2,
   fun e ab => x (.inl e.1.1) ab.1 * endpointMap A e (x' (.inr e.1.2) ab.2) -
     x' (.inl e.1.1) ab.1 * endpointMap A e (x (.inr e.1.2) ab.2))

/-- The manuscript's actual alternating bilinear tensor. -/
def omega (q : ℕ) : AlternatingBilinearMap F (OldInput A q) (OldOutput A q) where
  toLinearMap := LinearMap.mk₂ F (omegaFun A q)
    (by
      intro x y z
      apply Prod.ext
      · funext v ab
        simp only [omegaFun, Pi.add_apply, Prod.fst_add]
        ring
      · funext e ab
        simp only [omegaFun, Pi.add_apply, Prod.snd_add, map_add]
        ring)
    (by
      intro c x y
      apply Prod.ext
      · funext v ab
        simp only [omegaFun, Pi.smul_apply, Prod.smul_fst, smul_mul_assoc,
          mul_smul_comm, smul_sub]
      · funext e ab
        simp only [omegaFun, Pi.smul_apply, Prod.smul_snd, map_smul,
          smul_mul_assoc, mul_smul_comm, smul_sub])
    (by
      intro x y z
      apply Prod.ext
      · funext v ab
        simp only [omegaFun, Pi.add_apply, Prod.fst_add]
        ring
      · funext e ab
        simp only [omegaFun, Pi.add_apply, Prod.snd_add, map_add]
        ring)
    (by
      intro c x y
      apply Prod.ext
      · funext v ab
        simp only [omegaFun, Pi.smul_apply, Prod.smul_fst, smul_mul_assoc,
          mul_smul_comm, smul_sub]
      · funext e ab
        simp only [omegaFun, Pi.smul_apply, Prod.smul_snd, map_smul,
          smul_mul_assoc, mul_smul_comm, smul_sub])
  map_self_eq_zero x := by
    apply Prod.ext
    · funext v ab
      exact sub_self _
    · funext e ab
      exact sub_self _

@[simp] theorem omega_internal (q : ℕ) (x y : OldInput A q) (v : I ⊕ J) (ab : Pair q) :
    (omega A q x y).1 v ab = x v ab.1.1 * y v ab.1.2 - y v ab.1.1 * x v ab.1.2 := rfl

@[simp] theorem omega_incidence (q : ℕ) (x y : OldInput A q)
    (e : Incidence A) (ab : Fin q × Fin q) :
    (omega A q x y).2 e ab =
      x (.inl e.1.1) ab.1 * endpointMap A e (y (.inr e.1.2) ab.2) -
        y (.inl e.1.1) ab.1 * endpointMap A e (x (.inr e.1.2) ab.2) := rfl

/-- The selected scalar-coordinate kernels. A component transversal selects
one such pair in each incidence component. -/
def chosenKernel (q : ℕ) (anchors : Set ((I ⊕ J) × Fin q)) : Submodule F (OldInput A q) where
  carrier := {x | ∀ va ∈ anchors, (x va.1 va.2).fst = 0}
  zero_mem' := by intro va _; rfl
  add_mem' hx hy := by
    intro va hva
    exact (show ( _ + _ : RingAt A va.1).fst = 0 from by rw [TrivSqZeroExt.fst_add, hx va hva, hy va hva, zero_add])
  smul_mem' c x hx := by
    intro va hva
    change (c • x va.1 va.2).fst = 0
    rw [TrivSqZeroExt.fst_smul, hx va hva, smul_zero]

/-- Every radical-valued vector lies in every permitted chosen kernel. -/
theorem radical_mem_chosenKernel (q : ℕ) (anchors : Set ((I ⊕ J) × Fin q))
    (x : OldInput A q) (hx : ∀ v a, (x v a).fst = 0) :
    x ∈ chosenKernel A q anchors := fun va _ => hx va.1 va.2

/-- The input padding is one free copy of the original output. -/
abbrev PaddedInput (q : ℕ) := OldInput A q × OldOutput A q

/-- The output padding is a free copy of the entire padded input. -/
abbrev PaddedOutput (q : ℕ) := OldOutput A q × PaddedInput A q

/-- Padding introduces zero tensor terms in the new input and output sectors. -/
def paddedOmega (q : ℕ) :
    AlternatingBilinearMap F (PaddedInput A q) (PaddedOutput A q) where
  toLinearMap := LinearMap.mk₂ F (fun x y => (omega A q x.1 y.1, 0))
    (by intros; simp)
    (by intros; simp)
    (by intros; simp)
    (by intros; simp)
  map_self_eq_zero x := by simp

@[simp] theorem paddedOmega_apply (q : ℕ) (x y : PaddedInput A q) :
    paddedOmega A q x y = (omega A q x.1 y.1, 0) := rfl

/-- The slice map whose image of `L` is the manuscript's matrix space `C`. -/
def sliceMap (q : ℕ) : OldInput A q →ₗ[F]
    (PaddedInput A q →ₗ[F] PaddedOutput A q) :=
  (paddedOmega A q).toLinearMap.comp (LinearMap.inl F (OldInput A q) (OldOutput A q))

@[simp] theorem sliceMap_apply (q : ℕ) (a : OldInput A q) (x : PaddedInput A q) :
    sliceMap A q a x = (omega A q a x.1, 0) := rfl

/-- The actual obstruction-matrix space, before a choice of coordinate bases. -/
def obstructionSpace (q : ℕ) (anchors : Set ((I ⊕ J) × Fin q)) :
    Submodule F (PaddedInput A q →ₗ[F] PaddedOutput A q) :=
  (chosenKernel A q anchors).map (sliceMap A q)

/-- Each scalar input coordinate is an explicitly defined linear functional. -/
def scalarCoordinate (q : ℕ) (v : I ⊕ J) (a : Fin q) : PaddedInput A q →ₗ[F] F where
  toFun x := (x.1 v a).fst
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- An elementary alternating tensor built from two scalar functionals. -/
def elementaryTensor {X Z : Type*} [AddCommGroup X] [Module F X]
    [AddCommGroup Z] [Module F Z] (f g : X →ₗ[F] F) (z : Z) :
    AlternatingBilinearMap F X Z where
  toLinearMap := LinearMap.mk₂ F (fun x y => (f x * g y - f y * g x) • z)
    (by intros; simp only [map_add, add_mul, mul_add, add_sub_add_comm, add_smul])
    (by intros; simp only [map_smul, smul_eq_mul, smul_smul]; congr 1; ring)
    (by intros; simp only [map_add, add_mul, mul_add, add_sub_add_comm, add_smul])
    (by intros; simp only [map_smul, smul_eq_mul, smul_smul]; congr 1; ring)
  map_self_eq_zero x := by simp

/-- The first internal pair, which exists for all manuscript parameters. -/
def firstPair (q : ℕ) (hq : 2 ≤ q) : Pair q :=
  ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp⟩

/-- The radical output unit in internal coordinate `(i;0,1)`. -/
def chargeOutput (q : ℕ) (hq : 2 ≤ q) (i : I) : PaddedOutput A q :=
  ((Pi.single (.inl i) (Pi.single (firstPair q hq) (TrivSqZeroExt.inr (1 : F))), 0), 0)

/-- Each equation charge is supported on its two scalar unit inputs and its
single prescribed radical output coordinate. -/
def unitCharge (q : ℕ) (hq : 2 ≤ q) (i : I) :
    AlternatingBilinearMap F (PaddedInput A q) (PaddedOutput A q) :=
  elementaryTensor
    (scalarCoordinate A q (.inl i) (firstPair q hq).1.1)
    (scalarCoordinate A q (.inl i) (firstPair q hq).1.2)
    (chargeOutput A q hq i)

/-- The linear family of all charge representatives. -/
def chargeBilinear (q : ℕ) (hq : 2 ≤ q) : (I → F) →ₗ[F]
    (PaddedInput A q →ₗ[F] PaddedInput A q →ₗ[F] PaddedOutput A q) where
  toFun β := ∑ i, β i • (unitCharge A q hq i).toLinearMap
  map_add' β γ := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c β := by simp [Finset.smul_sum, smul_smul]

/-- The exact charge tensor `ε_β` from the manuscript. -/
def epsilonCharge (q : ℕ) (hq : 2 ≤ q) (β : I → F) :
    AlternatingBilinearMap F (PaddedInput A q) (PaddedOutput A q) where
  toLinearMap := chargeBilinear A q hq β
  map_self_eq_zero x := by
    simp [chargeBilinear, unitCharge, elementaryTensor]

@[simp] theorem epsilonCharge_apply (q : ℕ) (hq : 2 ≤ q) (β : I → F)
    (x y : PaddedInput A q) :
    epsilonCharge A q hq β x y = ∑ i, β i • unitCharge A q hq i x y := by
  simp [epsilonCharge, chargeBilinear]

/-- The directed incidence relation; its equivalence closure gives the
connected components of the bipartite incidence graph. -/
def incidenceRelation : (I ⊕ J) → (I ⊕ J) → Prop
  | .inl i, .inr j => j ∈ A.scope i
  | _, _ => False

/-- Components of the actual incidence graph. -/
def componentSetoid : Setoid (I ⊕ J) := Relation.EqvGen.setoid (incidenceRelation A)

abbrev Component := Quotient (componentSetoid A)

/-- The scalar coordinate zero at every incidence vertex. This explicit cover
avoids choosing quotient representatives. The classification and rank proofs
need only a cover of the components, so this slightly larger anchor set preserves
the theorem while keeping the construction executable. -/
def componentAnchors (_A : AffineSystem F I J V) (q : ℕ) (hq : 0 < q) :
    Set ((I ⊕ J) × Fin q) :=
  Set.range (fun v : I ⊕ J => (v, ⟨0, hq⟩))

/-- The scalar-zero subspace `L` for the explicit all-vertex anchor cover. -/
def chosenSpace (q : ℕ) (hq : 0 < q) : Submodule F (OldInput A q) :=
  chosenKernel A q (componentAnchors A q hq)

@[simp] theorem mem_componentAnchors (q : ℕ) (hq : 0 < q)
    (v : I ⊕ J) (a : Fin q) :
    (v,a) ∈ componentAnchors A q hq ↔ a = ⟨0,hq⟩ := by
  simp [componentAnchors, eq_comm]

/-- Membership in `L` is a finite list of explicitly specified coordinate tests. -/
theorem mem_chosenSpace_iff (q : ℕ) (hq : 0 < q) (x : OldInput A q) :
    x ∈ chosenSpace A q hq ↔ ∀ v : I ⊕ J, (x v ⟨0,hq⟩).fst = 0 := by
  constructor
  · intro h v
    exact h (v,⟨0,hq⟩) ⟨v,rfl⟩
  · rintro h ⟨v,a⟩ ha
    obtain ⟨w,hw⟩ := ha
    cases hw
    exact h _

/-- Edge-compatible scalar labels agree throughout each component. -/
theorem scalar_constant_on_component (s : I ⊕ J → F)
    (hs : ∀ i j, j ∈ A.scope i → s (.inl i) = s (.inr j))
    {v w : I ⊕ J} (h : (componentSetoid A).r v w) : s v = s w := by
  induction h with
  | rel v w hvw =>
    cases v with
    | inl i =>
      cases w with
      | inl _ => exact False.elim hvw
      | inr j => exact hs i j hvw
    | inr _ => exact False.elim (by cases w <;> exact hvw)
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

/-- Killing the selected scalar in each component kills every compatible
scalar multiplier. -/
theorem scalar_zero_of_anchors (s : I ⊕ J → F)
    (hs : ∀ i j, j ∈ A.scope i → s (.inl i) = s (.inr j))
    (hz : ∀ c : Component A, s c.out = 0) (v : I ⊕ J) : s v = 0 := by
  let c : Component A := Quotient.mk (componentSetoid A) v
  have hrel : (componentSetoid A).r c.out v := Quotient.exact (Quotient.out_eq c)
  exact (scalar_constant_on_component A s hs hrel).symm.trans (hz c)

/-- The condition that all multiplier images lie in `L` removes their common
scalar parts, precisely the global step in the obstruction quotient proof. -/
theorem multiplier_scalar_zero (q : ℕ) (hq : 0 < q)
    (r : ∀ v : I ⊕ J, RingAt A v)
    (hcompat : ∀ i j, j ∈ A.scope i → (r (.inl i)).fst = (r (.inr j)).fst)
    (hL : ∀ a : OldInput A q,
      (fun v t => r v * a v t) ∈ chosenSpace A q hq) (v : I ⊕ J) :
    (r v).fst = 0 := by
  let a : OldInput A q := Pi.single v (Pi.single (⟨0, hq⟩ : Fin q) 1)
  have he := hL a (v, ⟨0, hq⟩) ⟨v, rfl⟩
  change (r v * a v ⟨0, hq⟩).fst = 0 at he
  simpa [a] using he

/-- The fully fixed matrix obstruction space for the explicit anchor cover. -/
def constructionObstructionSpace (q : ℕ) (hq : 0 < q) :
    Submodule F (PaddedInput A q →ₗ[F] PaddedOutput A q) :=
  (chosenSpace A q hq).map (sliceMap A q)

end IncidenceTensor
end GroupWL
