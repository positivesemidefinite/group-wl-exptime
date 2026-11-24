import GroupWL.FrameDecoding
import GroupWL.IncidenceCoordinates

/-! # Radical slice orthogonality in the prescribed coordinates -/
set_option linter.unusedSectionVars false

namespace GroupWL
namespace FrameOrthogonality

open IncidenceTensor IncidenceCoordinates ObstructionDuality FrameDecoding
open scoped BigOperators
universe u
variable {F I J : Type u} [Field F] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {V : J → Type u} [∀ j, AddCommGroup (V j)] [∀ j, Module F (V j)]
variable (A : AffineSystem F I J V) (q : ℕ)

noncomputable def inputBasis (c : InputIndex A q) : PaddedInput A q :=
  (inputCoordinates A q).symm (Pi.single c 1)

@[simp] theorem inputBasis_scalar (c : InputIndex A q) (v : I ⊕ J) (a : Fin q) :
    ((inputBasis A q c).1 v a).fst =
      if scalarIndex A q v a = c then 1 else 0 := by
  classical
  rw [← inputCoordinates_scalar, inputBasis, LinearEquiv.apply_symm_apply]
  simp [Pi.single_apply]

@[simp] theorem inputBasis_scalar_index (v : I ⊕ J) (a : Fin q) :
    inputBasis A q (scalarIndex A q v a) = (oldUnit A q v a, 0) :=
  inputCoordinates_symm_scalar A q v a

/-- A radical coefficient placed at a single old input coordinate. -/
def radicalUnit (v : I ⊕ J) (a : Fin q) (u : Radical A v) : OldInput A q :=
  Pi.single v (Pi.single a (TrivSqZeroExt.inr u))

theorem radicalUnit_mem_chosenKernel (v : I ⊕ J) (a : Fin q) (u : Radical A v)
    (anchors : Set ((I ⊕ J) × Fin q)) :
    radicalUnit A q v a u ∈ chosenKernel A q anchors := by
  apply radical_mem_chosenKernel
  intro w b
  by_cases hw : w = v
  · subst w
    by_cases hb : b = a
    · subst b; simp [radicalUnit]
    · simp [radicalUnit, hb]
  · simp [radicalUnit, hw]

/-- The prescribed coordinate pairing on output vectors. -/
noncomputable def outputPair (z w : PaddedOutput A q) : F :=
  ∑ c, outputCoordinates A q z c * outputCoordinates A q w c

/-- Matrices of actual linear operators in the prescribed scalar-first bases. -/
noncomputable def operatorMatrix (y : PaddedInput A q →ₗ[F] PaddedOutput A q) :
    MatrixSpace F (InputIndex A q) (OutputIndex A q) :=
  IncidenceGroup.operatorCoordinates A q (inputCoordinates A q) (outputCoordinates A q) y

@[simp] theorem operatorMatrix_apply (y : PaddedInput A q →ₗ[F] PaddedOutput A q)
    (c : InputIndex A q) (d : OutputIndex A q) :
    operatorMatrix A q y c d = outputCoordinates A q (y (inputBasis A q c)) d := rfl

/-- The Frobenius pairing is the sum of output pairings on coordinate-basis inputs. -/
theorem operatorMatrix_pair (c y : PaddedInput A q →ₗ[F] PaddedOutput A q) :
    matrixPair (operatorMatrix A q c) (operatorMatrix A q y) =
      ∑ b, outputPair A q (c (inputBasis A q b)) (y (inputBasis A q b)) := rfl

/-- The old-output part of an operator, restricted to old inputs. -/
def oldPart (y : PaddedInput A q →ₗ[F] PaddedOutput A q) :
    OldInput A q →ₗ[F] OldOutput A q :=
  (LinearMap.fst F (OldOutput A q) (PaddedInput A q)).comp
    (y.comp (LinearMap.inl F (OldInput A q) (OldOutput A q)))

@[simp] theorem oldPart_apply (y : PaddedInput A q →ₗ[F] PaddedOutput A q)
    (x : OldInput A q) : oldPart A q y x = (y (x, 0)).1 := rfl

/-- Coordinate duality on the radical at a readout vertex. -/
noncomputable def readoutDual (j : J) (u : ReadoutRadical A j) :
    ReadoutRadical A j →ₗ[F] F where
  toFun v := ∑ k, radicalCoordinates A (.inr j) u k * radicalCoordinates A (.inr j) v k
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum, mul_left_comm]

@[simp] theorem outputCoordinates_inl (w : PaddedOutput A q) (c : OldOutputIndex A q) :
    outputCoordinates A q w (.inl c) = oldOutputCoordinates A q w.1 c := rfl

@[simp] theorem outputCoordinates_inr (w : PaddedOutput A q) (c : InputIndex A q) :
    outputCoordinates A q w (.inr c) = inputCoordinates A q w.2 c := rfl

/-- Expanding the output pairing uses the actual scalar-first radical bases. -/
theorem outputPair_old (z : OldOutput A q) (w : PaddedOutput A q) :
    outputPair A q (z, 0) w =
      (∑ v, ∑ ab : Pair q,
        ((z.1 v ab).fst * (w.1.1 v ab).fst +
        ∑ k, radicalCoordinates A v (z.1 v ab).snd k *
          radicalCoordinates A v (w.1.1 v ab).snd k)) +
      ∑ e : Incidence A, ∑ ab : Fin q × Fin q,
        ((z.2 e ab).fst * (w.1.2 e ab).fst +
        (z.2 e ab).snd * (w.1.2 e ab).snd) := by
  unfold outputPair
  have h0 : (∑ c, outputCoordinates A q (z, 0) c * outputCoordinates A q w c) =
      (∑ c : OldOutputIndex A q,
        outputCoordinates A q (z, 0) (.inl c) * outputCoordinates A q w (.inl c)) +
      ∑ c : InputIndex A q,
        outputCoordinates A q (z, 0) (.inr c) * outputCoordinates A q w (.inr c) := by
    exact Fintype.sum_sum_type _
  rw [h0]
  simp only [outputCoordinates_inl, outputCoordinates_inr, map_zero,
    Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
  have h1 : (∑ c : OldOutputIndex A q,
      oldOutputCoordinates A q z c * oldOutputCoordinates A q w.1 c) =
      (∑ c : ((v : I ⊕ J) × (Pair q × Option (RadicalIndex A v))),
        oldOutputCoordinates A q z (.inl c) * oldOutputCoordinates A q w.1 (.inl c)) +
      ∑ c : (Incidence A × (Fin q × Fin q) × Option PUnit),
        oldOutputCoordinates A q z (.inr c) * oldOutputCoordinates A q w.1 (.inr c) := by
    exact Fintype.sum_sum_type _
  rw [h1]
  simp only [oldOutputCoordinates, Fintype.sum_sigma, Fintype.sum_prod_type,
    Fintype.sum_option, ringCoordinates, edgeCoordinates, squareZeroCoordinates]
  simp

@[simp] theorem outputPair_add_left (x y z : PaddedOutput A q) :
    outputPair A q (x + y) z = outputPair A q x z + outputPair A q y z := by
  simp [outputPair, add_mul, Finset.sum_add_distrib]

@[simp] theorem outputPair_sum_left {η : Type*} [Fintype η]
    (x : η → PaddedOutput A q) (z : PaddedOutput A q) :
    outputPair A q (∑ t, x t) z = ∑ t, outputPair A q (x t) z := by
  simp only [outputPair, map_sum, Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- An internal radical output block. -/
def internalRadicalOutput (v : I ⊕ J) (d : Pair q → Radical A v) : PaddedOutput A q :=
  ((Pi.single v (fun ab => TrivSqZeroExt.inr (d ab)), 0), 0)

/-- An incidence radical output block. -/
def edgeRadicalOutput (e : Incidence A) (d : Fin q × Fin q → F) : PaddedOutput A q :=
  ((0, Pi.single e (fun ab => TrivSqZeroExt.inr (d ab))), 0)

theorem outputPair_internalRadical (v : I ⊕ J) (d : Pair q → Radical A v)
    (w : PaddedOutput A q) :
    outputPair A q (internalRadicalOutput A q v d) w =
      ∑ ab, ∑ k, radicalCoordinates A v (d ab) k *
        radicalCoordinates A v (w.1.1 v ab).snd k := by
  classical
  rw [internalRadicalOutput, outputPair_old]
  simp only [Pi.zero_apply, TrivSqZeroExt.fst_zero, zero_mul,
    TrivSqZeroExt.snd_zero, Finset.sum_const_zero, add_zero]
  rw [Finset.sum_eq_single v]
  · simp
  · intro v' _ hne
    simp [Pi.single_eq_of_ne hne]
  · simp

theorem outputPair_equationRadical (i : I) (d : Pair q → F)
    (w : PaddedOutput A q) :
    outputPair A q (internalRadicalOutput A q (.inl i) d) w =
      ∑ ab, d ab * (w.1.1 (.inl i) ab).snd := by
  rw [outputPair_internalRadical]
  change (∑ ab, ∑ _k : PUnit, d ab * (w.1.1 (.inl i) ab).snd) = _
  simp

theorem outputPair_readoutRadical (j : J) (d : Pair q → ReadoutRadical A j)
    (w : PaddedOutput A q) :
    outputPair A q (internalRadicalOutput A q (.inr j) d) w =
      ∑ ab, readoutDual A j (d ab) (w.1.1 (.inr j) ab).snd := by
  rw [outputPair_internalRadical]
  rfl

theorem outputPair_edgeRadical (e : Incidence A) (d : Fin q × Fin q → F)
    (w : PaddedOutput A q) :
    outputPair A q (edgeRadicalOutput A q e d) w =
      ∑ ab, d ab * (w.1.2 e ab).snd := by
  classical
  rw [edgeRadicalOutput, outputPair_old]
  simp only [Pi.zero_apply, TrivSqZeroExt.fst_zero, zero_mul, TrivSqZeroExt.snd_zero,
    map_zero, Finset.sum_const_zero, zero_add]
  rw [Finset.sum_eq_single e]
  · simp
  · intro e' _ hne
    simp [Pi.single_eq_of_ne hne]
  · simp

/-- Pairing with a sparse output separates all the expected internal and
incidence coordinates. -/
theorem outputPair_radical_blocks (v : I ⊕ J) (d : Pair q → Radical A v)
    (e : Incidence A → Fin q × Fin q → F) (w : PaddedOutput A q) :
    outputPair A q (internalRadicalOutput A q v d + ∑ t, edgeRadicalOutput A q t (e t)) w =
      (∑ ab, ∑ k, radicalCoordinates A v (d ab) k *
        radicalCoordinates A v (w.1.1 v ab).snd k) +
      ∑ t, ∑ ab, e t ab * (w.1.2 t ab).snd := by
  rw [outputPair_add_left, outputPair_sum_left, outputPair_internalRadical]
  simp only [outputPair_edgeRadical]

theorem inr_mul_ring (v : I ⊕ J) (u : Radical A v) (r : RingAt A v) :
    TrivSqZeroExt.inr u * r = TrivSqZeroExt.inr (r.fst • u) := by
  apply TrivSqZeroExt.ext
  · simp
  · simp [TrivSqZeroExt.snd_mul, op_smul_eq_smul]

theorem mul_inr_ring (v : I ⊕ J) (r : RingAt A v) (u : Radical A v) :
    r * TrivSqZeroExt.inr u = TrivSqZeroExt.inr (r.fst • u) := by
  rw [mul_comm, inr_mul_ring]

/-- The actual radical equation slice, decomposed into its internal and
incidence output blocks. -/
theorem equation_slice_blocks (i : I) (a : Fin q) (x : PaddedInput A q) :
    sliceMap A q (radicalUnit A q (.inl i) a (1 : F)) x =
      internalRadicalOutput A q (.inl i)
        (fun ab => (if ab.1.1 = a then (x.1 (.inl i) ab.1.2).fst else 0) -
          (if ab.1.2 = a then (x.1 (.inl i) ab.1.1).fst else 0)) +
      ∑ e : Incidence A, edgeRadicalOutput A q e
        (fun ab => if e.1.1 = i ∧ ab.1 = a then (x.1 (.inr e.1.2) ab.2).fst else 0) := by
  classical
  apply Prod.ext
  · apply Prod.ext
    · funext v ab
      by_cases hv : v = .inl i
      · subst v
        simp only [sliceMap_apply, omega_internal, radicalUnit, Pi.single_eq_same,
          Pi.single_apply, internalRadicalOutput, edgeRadicalOutput,
          Prod.fst_add, Prod.fst_sum,
          Finset.sum_const_zero, add_zero]
        split_ifs <;> apply TrivSqZeroExt.ext <;>
          simp_all [TrivSqZeroExt.snd_mul, smul_eq_mul]
      · simp [sliceMap_apply, omega_internal, radicalUnit, internalRadicalOutput,
          edgeRadicalOutput, hv, Prod.fst_sum]
    · funext e ab
      rcases e with ⟨⟨i', j⟩, hij⟩
      by_cases hi : i' = i
      · subst i'
        simp [sliceMap_apply, omega_incidence, radicalUnit, internalRadicalOutput,
          edgeRadicalOutput, Pi.single_apply, Finset.sum_apply,
          Prod.fst_sum, Prod.snd_sum, endpointMap]
        split_ifs <;> apply TrivSqZeroExt.ext <;>
          simp_all [TrivSqZeroExt.snd_mul]
      · simp [sliceMap_apply, omega_incidence, radicalUnit, internalRadicalOutput,
          edgeRadicalOutput, hi, Finset.sum_apply, Prod.fst_sum, Prod.snd_sum]
  · simp [sliceMap_apply, internalRadicalOutput, edgeRadicalOutput, Prod.snd_sum]

/-- Contracting scalar input coordinates against the prescribed basis selects
exactly the corresponding scalar-unit query. -/
theorem sum_inputBasis_scalar (v : I ⊕ J) (a : Fin q) (f : InputIndex A q → F) :
    (∑ c, ((inputBasis A q c).1 v a).fst * f c) = f (scalarIndex A q v a) := by
  classical
  simp [inputBasis_scalar]

def incidenceEquationEquiv : Incidence A ≃ ((i : I) × Scope A i) where
  toFun e := ⟨e.1.1, ⟨e.1.2, e.2⟩⟩
  invFun e := scopeEdge A e.1 e.2
  left_inv e := by cases e; rfl
  right_inv e := by cases e; rfl

theorem sum_incidence_equation (i : I) (f : Incidence A → F) :
    (∑ e, if e.1.1 = i then f e else 0) = ∑ j : Scope A i, f (scopeEdge A i j) := by
  classical
  rw [Fintype.sum_equiv (incidenceEquationEquiv A) _
    (fun e => if e.1 = i then f (scopeEdge A e.1 e.2) else 0) (by intro e; rfl)]
  simp [Fintype.sum_sigma]

/-- The equation contraction is exactly a Frobenius pairing with an actual
radical slice of the incidence tensor. -/
theorem equationContraction_pair (i : I) (a : Fin q)
    (y : PaddedInput A q →ₗ[F] PaddedOutput A q) :
    matrixPair (operatorMatrix A q (sliceMap A q (radicalUnit A q (.inl i) a (1 : F))))
      (operatorMatrix A q y) = equationContraction A q i a (oldPart A q y) := by
  classical
  rw [operatorMatrix_pair]
  simp_rw [equation_slice_blocks, outputPair_add_left, outputPair_sum_left,
    outputPair_equationRadical, outputPair_edgeRadical]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ab _
    simp only [sub_mul, Finset.sum_sub_distrib]
    congr 1 <;> split_ifs <;>
      simp [sum_inputBasis_scalar, equationRad, oldPart_apply]
  · rw [Finset.sum_comm]
    have he : ∀ e : Incidence A,
        (∑ c, ∑ ab : Fin q × Fin q,
          (if e.1.1 = i ∧ ab.1 = a then ((inputBasis A q c).1 (.inr e.1.2) ab.2).fst else 0) *
            ((y (inputBasis A q c)).1.2 e ab).snd) =
        if e.1.1 = i then
          ∑ b, edgeRad A q (oldPart A q y) (.inr e.1.2) b e (a,b) else 0 := by
      intro e
      by_cases hi : e.1.1 = i
      · simp only [hi, true_and, if_true]
        rw [Finset.sum_comm]
        simp only [Fintype.sum_prod_type]
        simp only [ite_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
        apply Finset.sum_congr rfl
        intro b _
        rw [sum_inputBasis_scalar]
        simp [edgeRad]
      · simp [hi]
    simp_rw [he]
    rw [sum_incidence_equation]
    rfl

/-- Extend a readout radical relation by zero to all incidences. -/
def readoutCoefficient (j : J) (u : ReadoutRadical A j) (e : Incidence A) : F :=
  if h : e.1.2 = j then u.val ⟨e.1.1, h ▸ e.2⟩ else 0

@[simp] theorem readoutCoefficient_neighbor (j : J) (u : ReadoutRadical A j)
    (i : Neighbors A j) : readoutCoefficient A j u (neighborEdge A j i) = u.val i := by
  simp [readoutCoefficient, neighborEdge]

/-- The actual radical readout slice has the opposite incidence orientation. -/
theorem readout_slice_blocks (j : J) (b : Fin q) (u : ReadoutRadical A j)
    (x : PaddedInput A q) :
    sliceMap A q (radicalUnit A q (.inr j) b u) x =
      internalRadicalOutput A q (.inr j)
        (fun ab => ((if ab.1.1 = b then (x.1 (.inr j) ab.1.2).fst else 0) -
          (if ab.1.2 = b then (x.1 (.inr j) ab.1.1).fst else 0)) • u) -
      ∑ e : Incidence A, edgeRadicalOutput A q e
        (fun ab => if ab.2 = b then
          (x.1 (.inl e.1.1) ab.1).fst * readoutCoefficient A j u e else 0) := by
  classical
  apply Prod.ext
  · apply Prod.ext
    · funext v ab
      by_cases hv : v = .inr j
      · subst v
        simp only [sliceMap_apply, omega_internal, radicalUnit, Pi.single_eq_same,
          Pi.single_apply, internalRadicalOutput, edgeRadicalOutput,
          Prod.fst_sub, Prod.fst_sum, Finset.sum_const_zero, sub_zero]
        split_ifs <;> apply TrivSqZeroExt.ext <;>
          simp_all [TrivSqZeroExt.snd_mul, op_smul_eq_smul]
        exact (neg_smul _ _).symm
      · simp [sliceMap_apply, omega_internal, radicalUnit, internalRadicalOutput,
          edgeRadicalOutput, hv, Prod.fst_sum]
    · funext e ab
      rcases e with ⟨⟨i, j'⟩, hij⟩
      by_cases hj : j' = j
      · subst j'
        simp [sliceMap_apply, omega_incidence, radicalUnit, internalRadicalOutput,
          edgeRadicalOutput, Pi.single_apply, Finset.sum_apply,
          Prod.fst_sum, Prod.snd_sum, endpointMap, readoutCoefficient]
        split_ifs <;> apply TrivSqZeroExt.ext <;>
          simp_all [TrivSqZeroExt.snd_mul, readoutProjection]
      · simp [sliceMap_apply, omega_incidence, radicalUnit, internalRadicalOutput,
          edgeRadicalOutput, hj, Finset.sum_apply, Prod.fst_sum, Prod.snd_sum,
          readoutCoefficient]
  · simp [sliceMap_apply, internalRadicalOutput, edgeRadicalOutput, Prod.snd_sum]

@[simp] theorem outputPair_sub_left (x y z : PaddedOutput A q) :
    outputPair A q (x - y) z = outputPair A q x z - outputPair A q y z := by
  simp [outputPair, sub_mul, Finset.sum_sub_distrib]

theorem readoutDual_smul (j : J) (c : F) (u v : ReadoutRadical A j) :
    readoutDual A j (c • u) v = c * readoutDual A j u v := by
  simp [readoutDual, Finset.mul_sum, mul_assoc]

def incidenceReadoutEquiv : Incidence A ≃ ((j : J) × Neighbors A j) where
  toFun e := ⟨e.1.2, ⟨e.1.1, e.2⟩⟩
  invFun e := neighborEdge A e.1 e.2
  left_inv e := by cases e; rfl
  right_inv e := by cases e; rfl

theorem sum_incidence_readout (j : J) (u : ReadoutRadical A j) (f : Incidence A → F) :
    (∑ e, readoutCoefficient A j u e * f e) =
      ∑ i : Neighbors A j, u.val i * f (neighborEdge A j i) := by
  classical
  rw [Fintype.sum_equiv (incidenceReadoutEquiv A) _
    (fun e => readoutCoefficient A j u (neighborEdge A e.1 e.2) *
      f (neighborEdge A e.1 e.2)) (by intro e; rfl)]
  simp only [Fintype.sum_sigma, readoutCoefficient, neighborEdge]
  simp only [dite_mul, zero_mul, Finset.sum_dite_irrel, Finset.sum_const_zero]
  simp

/-- The readout contraction is a real Frobenius slice pairing, with the
coordinate dual dictated by the prescribed radical basis. -/
theorem readoutContraction_pair (j : J) (b : Fin q) (u : ReadoutRadical A j)
    (y : PaddedInput A q →ₗ[F] PaddedOutput A q) :
    matrixPair (operatorMatrix A q (sliceMap A q (radicalUnit A q (.inr j) b u)))
      (operatorMatrix A q y) =
      readoutContraction A q j b u (readoutDual A j u) (oldPart A q y) := by
  classical
  rw [operatorMatrix_pair]
  simp_rw [readout_slice_blocks, outputPair_sub_left, outputPair_sum_left,
    outputPair_readoutRadical, outputPair_edgeRadical, readoutDual_smul]
  rw [Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ab _
    simp only [sub_mul, Finset.sum_sub_distrib]
    congr 1 <;> split_ifs <;>
      simp [sum_inputBasis_scalar, readoutRad, oldPart_apply]
  · rw [Finset.sum_comm]
    have he : ∀ e : Incidence A,
        (∑ c, ∑ ab : Fin q × Fin q,
          (if ab.2 = b then ((inputBasis A q c).1 (.inl e.1.1) ab.1).fst *
            readoutCoefficient A j u e else 0) * ((y (inputBasis A q c)).1.2 e ab).snd) =
        readoutCoefficient A j u e *
          ∑ a, edgeRad A q (oldPart A q y) (.inl e.1.1) a e (a,b) := by
      intro e
      rw [Finset.sum_comm]
      simp only [Fintype.sum_prod_type]
      simp only [ite_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      simp only [mul_right_comm _ (readoutCoefficient A j u e),
        ← Finset.sum_mul, sum_inputBasis_scalar]
      simp [edgeRad, mul_comm]
    simp_rw [he]
    rw [sum_incidence_readout]
    simp only [Finset.mul_sum]
    rfl

/-- Admissibility in the actual coordinate obstruction annihilator. -/
def Admissible (hq : 0 < q) (y : PaddedInput A q →ₗ[F] PaddedOutput A q) : Prop :=
  operatorMatrix A q y ∈ annihilator (IncidenceGroup.coordinateObstruction A q hq
    (inputCoordinates A q) (outputCoordinates A q))

theorem radical_slice_orthogonal (hq : 0 < q)
    (y : PaddedInput A q →ₗ[F] PaddedOutput A q) (hy : Admissible A q hq y)
    (v : I ⊕ J) (a : Fin q) (u : Radical A v) :
    matrixPair (operatorMatrix A q (sliceMap A q (radicalUnit A q v a u)))
      (operatorMatrix A q y) = 0 := by
  rw [matrixPair_comm]
  apply (mem_annihilator _ _).mp hy
  exact ⟨sliceMap A q (radicalUnit A q v a u),
    ⟨radicalUnit A q v a u,
      radicalUnit_mem_chosenKernel A q v a u (componentAnchors A q hq), rfl⟩, rfl⟩

theorem equationContraction_zero (hq : 0 < q)
    (y : PaddedInput A q →ₗ[F] PaddedOutput A q) (hy : Admissible A q hq y)
    (i : I) (a : Fin q) : equationContraction A q i a (oldPart A q y) = 0 := by
  rw [← equationContraction_pair]
  exact radical_slice_orthogonal A q hq y hy (.inl i) a 1

/-- The actual annihilator hypothesis discharges every equation-frame
contraction, yielding the source equation rather than assuming it. -/
theorem equation_frame_decodes (hq : 2 ≤ q) (β : I → F) (i : I)
    (f : Fin q → (PaddedInput A q →ₗ[F] PaddedOutput A q))
    (hf : ∀ a, Admissible A q (by omega) (f a))
    (hcomm : FrameCommutes A q hq β (.inl i) (fun a => oldPart A q (f a))) :
    (∑ j : Scope A i, thetaEquation A q (fun a => oldPart A q (f a)) (scopeEdge A i j)) = β i := by
  apply equation_frame_identity A q hq β i _ hcomm
  intro a
  exact equationContraction_zero A q (by omega) (f a) (hf a) i a

theorem readoutContraction_zero (hq : 0 < q)
    (y : PaddedInput A q →ₗ[F] PaddedOutput A q) (hy : Admissible A q hq y)
    (j : J) (b : Fin q) (u : ReadoutRadical A j) :
    readoutContraction A q j b u (readoutDual A j u) (oldPart A q y) = 0 := by
  rw [← readoutContraction_pair]
  exact radical_slice_orthogonal A q hq y hy (.inr j) b u

/-- An actual admissible commuting readout frame determines a single source
readout vector with all its decoded incidence values. -/
theorem actual_readout_frame_decodes (hq : 2 ≤ q) (β : I → F) (j : J)
    (f : Fin q → (PaddedInput A q →ₗ[F] PaddedOutput A q))
    (hf : ∀ b, Admissible A q (by omega) (f b))
    (hcomm : FrameCommutes A q hq β (.inr j) (fun b => oldPart A q (f b))) :
    ∃ z : V j, ∀ i : Neighbors A j, A.coefficient i.1 j z =
      thetaReadout A q (fun b => oldPart A q (f b)) (neighborEdge A j i) := by
  apply readout_frame_decodes A q hq β j _ hcomm (readoutDual A j)
  intro u b
  exact readoutContraction_zero A q (by omega) (f b) (hf b) j b u

/-- Any operator supported in the free output sector lies in the actual
annihilator, including the identity and diagonal coordinate anchors. -/
theorem free_output_admissible (hq : 0 < q)
    (y : PaddedInput A q →ₗ[F] PaddedOutput A q)
    (hy : ∀ x, (y x).1 = 0) : Admissible A q hq y := by
  apply (mem_annihilator _ _).mpr
  rintro c ⟨d, ⟨a, ha, rfl⟩, rfl⟩
  rw [matrixPair_comm]
  change matrixPair (operatorMatrix A q (sliceMap A q a)) (operatorMatrix A q y) = 0
  rw [operatorMatrix_pair]
  apply Finset.sum_eq_zero
  intro b _
  rw [sliceMap_apply, outputPair_old]
  simp [hy]

/-- In particular every map into the free input copy of the output is an
admissible evaluation operator. -/
theorem free_output_map_admissible (hq : 0 < q)
    (f : PaddedInput A q →ₗ[F] PaddedInput A q) :
    Admissible A q hq ((LinearMap.inr F (OldOutput A q) (PaddedInput A q)).comp f) := by
  apply free_output_admissible
  intro x
  rfl

end FrameOrthogonality
end GroupWL
