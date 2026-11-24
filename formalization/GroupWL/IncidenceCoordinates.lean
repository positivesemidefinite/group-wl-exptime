import GroupWL.GlobalMultipliers
import GroupWL.IncidenceGroup

/-! # The scalar-first coordinates of the manuscript

Every vertex algebra is given the basis consisting of its scalar unit followed
by a basis of its radical. Equation and incidence radicals use the unit basis
of the base field. The remaining radical bases are chosen once by linear
algebra. All subsequent equivalences respect the displayed direct summands.
-/

namespace GroupWL
namespace IncidenceCoordinates

open IncidenceTensor ObstructionDuality
universe u
variable {F I J : Type u} [Field F] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {V : J → Type u} [∀ j, AddCommGroup (V j)] [∀ j, Module F (V j)]
variable (A : AffineSystem F I J V) (q : ℕ)

/-- Indices of the chosen radical bases. -/
def RadicalIndex : I ⊕ J → Type u
  | .inl _ => PUnit
  | .inr j => Module.Free.ChooseBasisIndex F (ReadoutRadical A j)

noncomputable instance radicalIndexFintype (v : I ⊕ J) : Fintype (RadicalIndex A v) := by
  cases v <;> dsimp [RadicalIndex] <;> infer_instance

noncomputable instance radicalIndexDecidableEq (v : I ⊕ J) :
    DecidableEq (RadicalIndex A v) := Classical.decEq _

/-- Radical coordinates, with the unit basis at each equation vertex. -/
noncomputable def radicalCoordinates (v : I ⊕ J) :
    Radical A v ≃ₗ[F] (RadicalIndex A v → F) := by
  cases v with
  | inl i => exact (LinearEquiv.funUnique PUnit F F).symm
  | inr j => exact (Module.Free.chooseBasis F (ReadoutRadical A j)).equivFun

/-- Scalar-first coordinates on a square-zero extension. -/
noncomputable def squareZeroCoordinates {N η : Type u} [AddCommGroup N] [Module F N]
    (e : N ≃ₗ[F] (η → F)) : TrivSqZeroExt F N ≃ₗ[F] (Option η → F) where
  toFun x := fun a => match a with | none => x.fst | some i => e x.snd i
  invFun x := (x none, e.symm (fun i => x (some i)))
  left_inv x := by
    apply TrivSqZeroExt.ext
    · rfl
    · exact e.symm_apply_apply _
  right_inv x := by
    funext i
    cases i with
    | none => rfl
    | some i => exact congrFun (e.apply_symm_apply (fun i => x (some i))) i
  map_add' x y := by funext i; cases i <;> simp
  map_smul' c x := by funext i; cases i <;> simp

/-- Coordinates in a vertex algebra: `none` is its scalar coordinate. -/
noncomputable def ringCoordinates (v : I ⊕ J) :
    RingAt A v ≃ₗ[F] (Option (RadicalIndex A v) → F) :=
  squareZeroCoordinates (radicalCoordinates A v)

/-- Coordinates in an incidence dual-number algebra. -/
noncomputable def edgeCoordinates : EdgeRing (F := F) ≃ₗ[F] (Option PUnit → F) :=
  squareZeroCoordinates (LinearEquiv.funUnique PUnit F F).symm

@[simp] theorem ringCoordinates_none (v : I ⊕ J) (x : RingAt A v) :
    ringCoordinates A v x none = x.fst := rfl

@[simp] theorem ringCoordinates_equation_radical (i : I) (x : RingAt A (.inl i)) :
    ringCoordinates A (.inl i) x (some PUnit.unit) = x.snd := rfl

@[simp] theorem edgeCoordinates_none (x : EdgeRing (F := F)) :
    edgeCoordinates (F := F) x none = x.fst := rfl

@[simp] theorem edgeCoordinates_radical (x : EdgeRing (F := F)) :
    edgeCoordinates (F := F) x (some PUnit.unit) = x.snd := rfl

abbrev OldInputIndex := (v : I ⊕ J) × (Fin q × Option (RadicalIndex A v))
abbrev OldOutputIndex := ((v : I ⊕ J) × (Pair q × Option (RadicalIndex A v))) ⊕
  (Incidence A × (Fin q × Fin q) × Option PUnit)
abbrev InputIndex := OldInputIndex A q ⊕ OldOutputIndex A q
abbrev OutputIndex := OldOutputIndex A q ⊕ InputIndex A q

noncomputable instance oldInputIndexFintype : Fintype (OldInputIndex A q) := by
  unfold OldInputIndex
  infer_instance
noncomputable instance oldOutputIndexFintype : Fintype (OldOutputIndex A q) := by
  unfold OldOutputIndex
  infer_instance
noncomputable instance inputIndexFintype : Fintype (InputIndex A q) := by
  unfold InputIndex
  infer_instance
noncomputable instance outputIndexFintype : Fintype (OutputIndex A q) := by
  unfold OutputIndex
  infer_instance

noncomputable instance inputIndexDecidableEq : DecidableEq (InputIndex A q) := Classical.decEq _
noncomputable instance outputIndexDecidableEq : DecidableEq (OutputIndex A q) := Classical.decEq _

noncomputable def oldInputCoordinates : OldInput A q ≃ₗ[F] (OldInputIndex A q → F) where
  toFun x c := ringCoordinates A c.1 (x c.1 c.2.1) c.2.2
  invFun x v a := (ringCoordinates A v).symm (fun c => x ⟨v, (a, c)⟩)
  left_inv x := by funext v a; exact (ringCoordinates A v).symm_apply_apply _
  right_inv x := by
    funext c
    exact congrFun ((ringCoordinates A c.1).apply_symm_apply (fun a => x ⟨c.1, (c.2.1, a)⟩)) c.2.2
  map_add' x y := by funext c; simp
  map_smul' k x := by funext c; simp

noncomputable def oldOutputCoordinates : OldOutput A q ≃ₗ[F] (OldOutputIndex A q → F) where
  toFun x c := match c with
    | .inl c => ringCoordinates A c.1 (x.1 c.1 c.2.1) c.2.2
    | .inr c => edgeCoordinates (x.2 c.1 c.2.1) c.2.2
  invFun x :=
    (fun v ab => (ringCoordinates A v).symm (fun c => x (.inl ⟨v, (ab, c)⟩)),
     fun e ab => edgeCoordinates.symm (fun c => x (.inr (e, ab, c))))
  left_inv x := by
    apply Prod.ext
    · funext v ab; exact (ringCoordinates A v).symm_apply_apply _
    · funext e ab; exact edgeCoordinates.symm_apply_apply _
  right_inv x := by
    funext c
    cases c with
    | inl c => exact congrFun ((ringCoordinates A c.1).apply_symm_apply _) c.2.2
    | inr c => exact congrFun (edgeCoordinates.apply_symm_apply _) c.2.2
  map_add' x y := by funext c; cases c <;> simp
  map_smul' k x := by funext c; cases c <;> simp

/-- The full input coordinates, respecting the free input padding. -/
noncomputable def inputCoordinates : PaddedInput A q ≃ₗ[F] (InputIndex A q → F) :=
  ((oldInputCoordinates A q).prodCongr (oldOutputCoordinates A q)).trans
    (LinearEquiv.sumArrowLequivProdArrow _ _ F F).symm

/-- The full output coordinates, respecting the free output padding. -/
noncomputable def outputCoordinates : PaddedOutput A q ≃ₗ[F] (OutputIndex A q → F) :=
  ((oldOutputCoordinates A q).prodCongr (inputCoordinates A q)).trans
    (LinearEquiv.sumArrowLequivProdArrow _ _ F F).symm

/-- The input coordinate of a scalar unit at a vertex. -/
def scalarIndex (v : I ⊕ J) (a : Fin q) : InputIndex A q := .inl ⟨v, (a, none)⟩

/-- The output coordinate read by the charge associated to equation `i`. -/
def chargeIndex (hq : 2 ≤ q) (i : I) : OutputIndex A q :=
  .inl (.inl ⟨.inl i, (firstPair q hq, some PUnit.unit)⟩)

@[simp] theorem inputCoordinates_scalar (x : PaddedInput A q) (v : I ⊕ J) (a : Fin q) :
    inputCoordinates A q x (scalarIndex A q v a) = (x.1 v a).fst := rfl

@[simp] theorem outputCoordinates_charge (hq : 2 ≤ q) (x : PaddedOutput A q) (i : I) :
    outputCoordinates A q x (chargeIndex A q hq i) =
      (x.1.1 (.inl i) (firstPair q hq)).snd := rfl

@[simp] theorem ringCoordinates_one (v : I ⊕ J) (c : Option (RadicalIndex A v)) :
    ringCoordinates A v 1 c = if c = none then 1 else 0 := by
  cases c <;> simp [ringCoordinates, squareZeroCoordinates]

/-- Every prescribed scalar unit is a coordinate-basis vector. -/
theorem inputCoordinates_unit (v : I ⊕ J) (a : Fin q) :
    inputCoordinates A q (unitInput A v a, 0) = Pi.single (scalarIndex A q v a) 1 := by
  classical
  funext c
  cases c with
  | inl c =>
    rcases c with ⟨w, b, d⟩
    by_cases hw : w = v
    · subst w
      simp [inputCoordinates, oldInputCoordinates, unitInput, scalarIndex, Pi.single_apply,
        ringCoordinates_one, ite_apply]
      split_ifs <;> simp_all
    · simp [inputCoordinates, oldInputCoordinates, unitInput, scalarIndex, Pi.single_apply,
        hw, Ne.symm hw, ite_apply]
  | inr c =>
    simp [inputCoordinates, scalarIndex, Pi.single_apply]

/-- The prescribed charge output is also a coordinate-basis vector. -/
theorem outputCoordinates_chargeOutput (hq : 2 ≤ q) (i : I) :
    outputCoordinates A q (chargeOutput A q hq i) = Pi.single (chargeIndex A q hq i) 1 := by
  classical
  funext c
  cases c with
  | inl c =>
    cases c with
    | inl c =>
      rcases c with ⟨w, ab, d⟩
      by_cases hw : w = .inl i
      · subst w
        cases d with
        | none =>
          simp [outputCoordinates, oldOutputCoordinates, chargeOutput, chargeIndex, Pi.single_apply,
            ringCoordinates, squareZeroCoordinates, ite_apply]
          split_ifs <;> rfl
        | some d =>
          cases d
          simp [outputCoordinates, oldOutputCoordinates, chargeOutput, chargeIndex, Pi.single_apply,
            ringCoordinates, squareZeroCoordinates, radicalCoordinates, ite_apply]
          split_ifs <;> rfl
      · simp [outputCoordinates, oldOutputCoordinates, chargeOutput, chargeIndex, Pi.single_apply,
          hw, Ne.symm hw, ite_apply]
    | inr c =>
      simp [outputCoordinates, oldOutputCoordinates, chargeOutput, chargeIndex, Pi.single_apply]
  | inr c =>
    simp [outputCoordinates, chargeOutput, chargeIndex, Pi.single_apply]

@[simp] theorem inputCoordinates_symm_scalar (v : I ⊕ J) (a : Fin q) :
    (inputCoordinates A q).symm (Pi.single (scalarIndex A q v a) 1) = (unitInput A v a, 0) := by
  rw [← inputCoordinates_unit, LinearEquiv.symm_apply_apply]

end IncidenceCoordinates
end GroupWL
