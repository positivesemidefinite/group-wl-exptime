import GroupWL.IncidenceTensor
import GroupWL.Affine

/-! # Frame decoding from orthogonality and commutation

The contraction identities in this file are explicit finite sums of entries of
response operators. They do not assume the affine equations decoded at the end.
-/
set_option linter.unusedSectionVars false

namespace GroupWL
namespace FrameDecoding

open IncidenceTensor
open scoped BigOperators
universe u
variable {F I J : Type u} [Field F] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {V : J → Type u} [∀ j, AddCommGroup (V j)] [∀ j, Module F (V j)]
variable (A : AffineSystem F I J V) (q : ℕ)

/-- Scalar-unit query vectors in the old input sector. -/
def oldUnit (v : I ⊕ J) (a : Fin q) : OldInput A q :=
  Pi.single v (Pi.single a 1)

/-- A response frame consists of its old-input/old-output operator parts. -/
abbrev Frame := Fin q → (OldInput A q →ₗ[F] OldOutput A q)

abbrev Scope (i : I) := {j : J // j ∈ A.scope i}

def scopeEdge (i : I) (j : Scope A i) : Incidence A := ⟨(i, j.1), j.2⟩
def neighborEdge (j : J) (i : Neighbors A j) : Incidence A := ⟨(i.1, j), i.2⟩

/-- Radical coefficient of one incidence output after a scalar-unit query. -/
def edgeRad (y : OldInput A q →ₗ[F] OldOutput A q)
    (v : I ⊕ J) (a : Fin q) (e : Incidence A) (ab : Fin q × Fin q) : F :=
  ((y (oldUnit A q v a)).2 e ab).snd

/-- Radical coefficient of one internal output at an equation vertex. -/
def equationRad (y : OldInput A q →ₗ[F] OldOutput A q)
    (i : I) (a : Fin q) (ab : Pair q) : F :=
  ((y (oldUnit A q (.inl i) a)).1 (.inl i) ab).snd

/-- Internal readout radical evaluated against a dual radical coefficient. -/
def readoutRad (y : OldInput A q →ₗ[F] OldOutput A q)
    (j : J) (a : Fin q) (ab : Pair q) (φ : ReadoutRadical A j →ₗ[F] F) : F :=
  φ (((y (oldUnit A q (.inr j) a)).1 (.inr j) ab).snd)

/-- The incidence value decoded by an equation frame. -/
def thetaEquation (f : Frame A q) (e : Incidence A) : F :=
  -∑ a, ∑ b, edgeRad A q (f a) (.inr e.1.2) b e (a, b)

/-- The incidence value decoded by a readout frame. -/
def thetaReadout (f : Frame A q) (e : Incidence A) : F :=
  -∑ b, ∑ a, edgeRad A q (f b) (.inl e.1.1) a e (a, b)

/-- Orthogonality to one radical slice at equation vertex `i`, expanded in
its scalar-input columns and radical-output coefficients. -/
def equationContraction (i : I) (a : Fin q)
    (y : OldInput A q →ₗ[F] OldOutput A q) : F :=
  (∑ ab : Pair q,
    ((if ab.1.1 = a then equationRad A q y i ab.1.2 ab else 0) -
    (if ab.1.2 = a then equationRad A q y i ab.1.1 ab else 0))) +
  ∑ j : Scope A i, ∑ b, edgeRad A q y (.inr j.1) b (scopeEdge A i j) (a, b)

/-- Orthogonality to a radical slice at readout vertex `j`. The functional
`φ` is the coordinate dual of the radical vector `u`. -/
def readoutContraction (j : J) (b : Fin q) (u : ReadoutRadical A j)
    (φ : ReadoutRadical A j →ₗ[F] F)
    (y : OldInput A q →ₗ[F] OldOutput A q) : F :=
  (∑ ab : Pair q,
    ((if ab.1.1 = b then readoutRad A q y j ab.1.2 ab φ else 0) -
    (if ab.1.2 = b then readoutRad A q y j ab.1.1 ab φ else 0))) -
  ∑ i : Neighbors A j, ∑ a,
    u.val i * edgeRad A q y (.inl i.1) a (neighborEdge A j i) (a, b)

/-- Summing the contractions over a whole frame pairs the two orientations
of every internal coordinate. -/
theorem sum_internal (r : Fin q → Fin q → Pair q → F) :
    (∑ a, ∑ ab : Pair q,
      ((if ab.1.1 = a then r a ab.1.2 ab else 0) -
      (if ab.1.2 = a then r a ab.1.1 ab else 0))) =
    ∑ ab : Pair q, (r ab.1.1 ab.1.2 ab - r ab.1.2 ab.1.1 ab) := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ab _
  simp [Finset.sum_sub_distrib]

/-- The equation-frame orthogonality sum is the sum of internal commutator
coefficients minus the decoded incidence sum. -/
theorem sum_equationContraction (i : I) (f : Frame A q) :
    (∑ a, equationContraction A q i a (f a)) =
      (∑ ab : Pair q, (equationRad A q (f ab.1.1) i ab.1.2 ab -
        equationRad A q (f ab.1.2) i ab.1.1 ab)) -
      ∑ j : Scope A i, thetaEquation A q f (scopeEdge A i j) := by
  simp only [equationContraction, Finset.sum_add_distrib]
  rw [sum_internal]
  rw [Finset.sum_comm]
  simp [thetaEquation, scopeEdge, Finset.sum_neg_distrib]

/-- Readout-frame contractions sum to the radical-weighted incidence values,
plus internal commutator coefficients. -/
theorem sum_readoutContraction (j : J) (f : Frame A q)
    (u : ReadoutRadical A j) (φ : ReadoutRadical A j →ₗ[F] F) :
    (∑ b, readoutContraction A q j b u φ (f b)) =
      (∑ ab : Pair q, (readoutRad A q (f ab.1.1) j ab.1.2 ab φ -
        readoutRad A q (f ab.1.2) j ab.1.1 ab φ)) +
      ∑ i : Neighbors A j, u.val i * thetaReadout A q f (neighborEdge A j i) := by
  simp only [readoutContraction]
  rw [Finset.sum_sub_distrib, sum_internal q (fun a b ab => readoutRad A q (f a) j b ab φ)]
  rw [Finset.sum_comm]
  simp [thetaReadout, neighborEdge, Finset.mul_sum, Finset.sum_neg_distrib,
    mul_neg, sub_eq_add_neg]

/-- The explicit charge on a retained equation frame has total internal
radical coefficient `β_i`. -/
theorem charge_equation_pair (hq : 2 ≤ q) (β : I → F) (i : I) (ab : Pair q) :
    (((epsilonCharge A q hq β
      (oldUnit A q (.inl i) ab.1.1, 0)
      (oldUnit A q (.inl i) ab.1.2, 0)).1.1 (.inl i) ab).snd) =
      if ab = firstPair q hq then β i else 0 := by
  classical
  rw [epsilonCharge_apply]
  simp only [Prod.fst_sum, Finset.sum_apply, Prod.smul_fst, Pi.smul_apply,
    TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_smul]
  rw [Finset.sum_eq_single i]
  · by_cases hab : ab = firstPair q hq
    · subst ab
      simp [unitCharge, elementaryTensor, scalarCoordinate,
        chargeOutput, oldUnit, firstPair]
    · simp [unitCharge, elementaryTensor, scalarCoordinate,
        chargeOutput, oldUnit, Pi.single_apply, hab]
  · intro j _ hji
    simp [unitCharge, elementaryTensor, chargeOutput, hji]
  · simp

/-- There is no input twist between two scalar queries at a readout vertex. -/
theorem charge_readout_pair (hq : 2 ≤ q) (β : I → F) (j : J) (a b : Fin q) :
    epsilonCharge A q hq β (oldUnit A q (.inr j) a, 0)
      (oldUnit A q (.inr j) b, 0) = 0 := by
  classical
  simp [epsilonCharge_apply, unitCharge, elementaryTensor, scalarCoordinate,
    chargeOutput, oldUnit]

/-- Incidence-output coordinates never carry a charge twist. -/
theorem charge_incidence_zero (hq : 2 ≤ q) (β : I → F)
    (x y : PaddedInput A q) (e : Incidence A) (ab : Fin q × Fin q) :
    (epsilonCharge A q hq β x y).1.2 e ab = 0 := by
  classical
  simp [epsilonCharge_apply, unitCharge, elementaryTensor, chargeOutput,
    Prod.fst_sum, Prod.snd_sum, Finset.sum_apply]

/-- The old-output part of the commutation relations on a retained frame. -/
def FrameCommutes (hq : 2 ≤ q) (β : I → F) (v : I ⊕ J) (f : Frame A q) : Prop :=
  ∀ a b, f a (oldUnit A q v b) - f b (oldUnit A q v a) =
    (epsilonCharge A q hq β (oldUnit A q v a, 0) (oldUnit A q v b, 0)).1

/-- An equation frame decodes an actual solution to its affine equation,
from its radical-slice orthogonality and the retained commutation relations. -/
theorem equation_frame_identity (hq : 2 ≤ q) (β : I → F) (i : I) (f : Frame A q)
    (hcomm : FrameCommutes A q hq β (.inl i) f)
    (horth : ∀ a, equationContraction A q i a (f a) = 0) :
    ∑ j : Scope A i, thetaEquation A q f (scopeEdge A i j) = β i := by
  have hpair (ab : Pair q) :
      equationRad A q (f ab.1.1) i ab.1.2 ab -
        equationRad A q (f ab.1.2) i ab.1.1 ab =
      if ab = firstPair q hq then β i else 0 := by
    have h := congrArg (fun z : OldOutput A q => (z.1 (.inl i) ab).snd)
      (hcomm ab.1.1 ab.1.2)
    calc
      _ = (((epsilonCharge A q hq β
        (oldUnit A q (.inl i) ab.1.1, 0)
        (oldUnit A q (.inl i) ab.1.2, 0)).1.1 (.inl i) ab).snd) := by
          simpa only [Prod.fst_sub, Pi.sub_apply, TrivSqZeroExt.snd_sub, equationRad] using h
      _ = _ := charge_equation_pair A q hq β i ab
  have hzero : (∑ a, equationContraction A q i a (f a)) = 0 := by simp [horth]
  rw [sum_equationContraction] at hzero
  simp only [hpair] at hzero
  have hzero' : β i - ∑ j : Scope A i, thetaEquation A q f (scopeEdge A i j) = 0 := by
    simpa only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] using hzero
  exact (sub_eq_zero.mp hzero').symm

/-- Internal readout terms cancel, leaving precisely the linear relation
among decoded incidence values. -/
theorem readout_frame_relation (hq : 2 ≤ q) (β : I → F) (j : J) (f : Frame A q)
    (hcomm : FrameCommutes A q hq β (.inr j) f)
    (u : ReadoutRadical A j) (φ : ReadoutRadical A j →ₗ[F] F)
    (horth : ∀ b, readoutContraction A q j b u φ (f b) = 0) :
    ∑ i : Neighbors A j, u.val i * thetaReadout A q f (neighborEdge A j i) = 0 := by
  have hpair (ab : Pair q) :
      readoutRad A q (f ab.1.1) j ab.1.2 ab φ -
        readoutRad A q (f ab.1.2) j ab.1.1 ab φ = 0 := by
    have h := congrArg (fun z : OldOutput A q => φ ((z.1 (.inr j) ab).snd))
      (hcomm ab.1.1 ab.1.2)
    simpa only [Prod.fst_sub, Pi.sub_apply, TrivSqZeroExt.snd_sub, map_sub,
      charge_readout_pair, Prod.fst_zero, Pi.zero_apply, TrivSqZeroExt.snd_zero,
      map_zero, readoutRad] using h
  have hzero : (∑ b, readoutContraction A q j b u φ (f b)) = 0 := by simp [horth]
  rw [sum_readoutContraction] at hzero
  simpa only [hpair, Finset.sum_const_zero, zero_add] using hzero

/-- A readout frame determines a single actual readout vector with all the
prescribed incidence evaluations. The kernel condition is proved by summing
its radical-slice orthogonality constraints. -/
theorem readout_frame_decodes (hq : 2 ≤ q) (β : I → F) (j : J) (f : Frame A q)
    (hcomm : FrameCommutes A q hq β (.inr j) f)
    (dual : ReadoutRadical A j → (ReadoutRadical A j →ₗ[F] F))
    (horth : ∀ u b, readoutContraction A q j b u (dual u) (f b) = 0) :
    ∃ z : V j, ∀ i : Neighbors A j,
      A.coefficient i.1 j z = thetaReadout A q f (neighborEdge A j i) := by
  apply (decoded_values_exist_iff
    (fun i : Neighbors A j => A.coefficient i.1 j)
    (fun i => thetaReadout A q f (neighborEdge A j i))).mpr
  intro u hu
  let ur : ReadoutRadical A j := ⟨u, hu⟩
  exact readout_frame_relation A q hq β j f hcomm ur (dual ur) (horth ur)

/-- Commuting retained endpoint frames read the same incidence value. -/
theorem endpoint_values_agree (hq : 2 ≤ q) (β : I → F) (e : Incidence A)
    (f g : Frame A q)
    (hcomm : ∀ a b,
      f a (oldUnit A q (.inr e.1.2) b) - g b (oldUnit A q (.inl e.1.1) a) =
      (epsilonCharge A q hq β (oldUnit A q (.inl e.1.1) a, 0)
        (oldUnit A q (.inr e.1.2) b, 0)).1) :
    thetaEquation A q f e = thetaReadout A q g e := by
  have he (a b : Fin q) :
      edgeRad A q (f a) (.inr e.1.2) b e (a, b) =
      edgeRad A q (g b) (.inl e.1.1) a e (a, b) := by
    have h := congrArg (fun z : OldOutput A q => (z.2 e (a, b)).snd) (hcomm a b)
    apply sub_eq_zero.mp
    simpa only [Prod.snd_sub, Pi.sub_apply, TrivSqZeroExt.snd_sub,
      charge_incidence_zero, TrivSqZeroExt.snd_zero, edgeRad] using h
  unfold thetaEquation thetaReadout
  rw [Finset.sum_comm (f := fun b a => edgeRad A q (g b) (.inl e.1.1) a e (a, b))]
  simp only [he]

end FrameDecoding
end GroupWL
