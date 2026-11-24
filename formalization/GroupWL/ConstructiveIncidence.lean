import GroupWL.ConstructiveCoordinates
import GroupWL.IncidenceCoordinates

/-! Scalar-first incidence coordinates using explicitly computed radical bases. -/
namespace GroupWL.ConstructiveIncidence

open IncidenceTensor ConstructiveCoordinates
variable {F I J : Type} [Field F] [DecidableEq F]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [FiniteCode I] [FiniteCode J]
variable {V : J → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module F (V j)]
variable (A : AffineSystem F I J V) (R : ∀ j, Coordinates F (ReadoutRadical A j)) (q : ℕ)

def RadicalIndex : I ⊕ J → Type
  | .inl _ => PUnit
  | .inr j => Fin (R j).dimension

instance radicalCode (v : I ⊕ J) : FiniteCode (RadicalIndex A R v) := by
  cases v <;> dsimp [RadicalIndex] <;> infer_instance

def radicalEquiv (v : I ⊕ J) : Radical A v ≃ₗ[F] (RadicalIndex A R v → F) := by
  cases v with
  | inl i => exact (LinearEquiv.funUnique PUnit F F).symm
  | inr j => exact (R j).equiv

def squareZeroEquiv {N η : Type} [AddCommGroup N] [Module F N]
    (e : N ≃ₗ[F] (η → F)) : TrivSqZeroExt F N ≃ₗ[F] (Option η → F) where
  toFun x c := match c with | none => x.fst | some i => e x.snd i
  invFun x := (x none, e.symm (fun i => x (some i)))
  left_inv x := by
    apply TrivSqZeroExt.ext
    · rfl
    · exact e.symm_apply_apply _
  right_inv x := by
    funext c
    cases c with
    | none => rfl
    | some i => exact congrFun (e.apply_symm_apply _) i
  map_add' x y := by funext c; cases c <;> simp
  map_smul' c x := by funext i; cases i <;> simp

def ringEquiv (v : I ⊕ J) : RingAt A v ≃ₗ[F] (Option (RadicalIndex A R v) → F) :=
  squareZeroEquiv (radicalEquiv A R v)

def edgeEquiv : EdgeRing (F := F) ≃ₗ[F] (Option PUnit → F) :=
  squareZeroEquiv (LinearEquiv.funUnique PUnit F F).symm

abbrev OldInputIndex : Type := Σ v : I ⊕ J, Fin q × Option (RadicalIndex A R v)
abbrev OldOutputIndex : Type := (Σ v : I ⊕ J, Pair q × Option (RadicalIndex A R v)) ⊕
  (Incidence A × (Fin q × Fin q) × Option PUnit)
abbrev InputIndex : Type := OldInputIndex A R q ⊕ OldOutputIndex A R q
abbrev OutputIndex : Type := OldOutputIndex A R q ⊕ InputIndex A R q

instance inputDecidableEq : DecidableEq (InputIndex A R q) :=
  (FiniteCode.equiv (α := InputIndex A R q)).decidableEq
instance outputDecidableEq : DecidableEq (OutputIndex A R q) :=
  (FiniteCode.equiv (α := OutputIndex A R q)).decidableEq
instance inputFintype : Fintype (InputIndex A R q) := FiniteCode.fintype _
instance outputFintype : Fintype (OutputIndex A R q) := FiniteCode.fintype _

def oldInputEquiv : OldInput A q ≃ₗ[F] (OldInputIndex A R q → F) where
  toFun x c := ringEquiv A R c.1 (x c.1 c.2.1) c.2.2
  invFun x v a := (ringEquiv A R v).symm (fun c => x ⟨v,(a,c)⟩)
  left_inv x := by funext v a; exact (ringEquiv A R v).symm_apply_apply _
  right_inv x := by funext c; exact congrFun ((ringEquiv A R c.1).apply_symm_apply _) c.2.2
  map_add' x y := by funext c; simp
  map_smul' a x := by funext c; simp

def oldOutputEquiv : OldOutput A q ≃ₗ[F] (OldOutputIndex A R q → F) where
  toFun x c := match c with
    | .inl c => ringEquiv A R c.1 (x.1 c.1 c.2.1) c.2.2
    | .inr c => edgeEquiv (x.2 c.1 c.2.1) c.2.2
  invFun x :=
    (fun v ab => (ringEquiv A R v).symm (fun c => x (.inl ⟨v,(ab,c)⟩)),
     fun e ab => edgeEquiv.symm (fun c => x (.inr (e,ab,c))))
  left_inv x := by
    apply Prod.ext
    · funext v ab; exact (ringEquiv A R v).symm_apply_apply _
    · funext e ab; exact edgeEquiv.symm_apply_apply _
  right_inv x := by
    funext c
    cases c with
    | inl c => exact congrFun ((ringEquiv A R c.1).apply_symm_apply _) c.2.2
    | inr c => exact congrFun (edgeEquiv.apply_symm_apply _) c.2.2
  map_add' x y := by funext c; cases c <;> simp
  map_smul' a x := by funext c; cases c <;> simp

def inputEquiv : PaddedInput A q ≃ₗ[F] (InputIndex A R q → F) :=
  ((oldInputEquiv A R q).prodCongr (oldOutputEquiv A R q)).trans
    (LinearEquiv.sumArrowLequivProdArrow _ _ F F).symm

def outputEquiv : PaddedOutput A q ≃ₗ[F] (OutputIndex A R q → F) :=
  ((oldOutputEquiv A R q).prodCongr (inputEquiv A R q)).trans
    (LinearEquiv.sumArrowLequivProdArrow _ _ F F).symm

def oldInputCoordinates : Coordinates F (OldInput A q) :=
  ⟨FiniteCode.size (OldInputIndex A R q),
    (oldInputEquiv A R q).trans (Coordinates.pi (OldInputIndex A R q)).equiv⟩

def inputCoordinates : Coordinates F (PaddedInput A q) :=
  ⟨FiniteCode.size (InputIndex A R q),
    (inputEquiv A R q).trans (Coordinates.pi (InputIndex A R q)).equiv⟩

def outputCoordinates : Coordinates F (PaddedOutput A q) :=
  ⟨FiniteCode.size (OutputIndex A R q),
    (outputEquiv A R q).trans (Coordinates.pi (OutputIndex A R q)).equiv⟩

def scalarIndex (v : I ⊕ J) (a : Fin q) : InputIndex A R q := .inl ⟨v,(a,none)⟩

def chargeIndex (hq : 2 ≤ q) (i : I) : OutputIndex A R q :=
  .inl (.inl ⟨.inl i,(firstPair q hq,some PUnit.unit)⟩)

@[simp] theorem inputEquiv_scalar (x : PaddedInput A q) (v : I ⊕ J) (a : Fin q) :
    inputEquiv A R q x (scalarIndex A R q v a) = (x.1 v a).fst := rfl

@[simp] theorem outputEquiv_charge (hq : 2 ≤ q) (x : PaddedOutput A q) (i : I) :
    outputEquiv A R q x (chargeIndex A R q hq i) =
      (x.1.1 (.inl i) (firstPair q hq)).snd := rfl

@[simp] theorem ringEquiv_one (v : I ⊕ J) (c : Option (RadicalIndex A R v)) :
    ringEquiv A R v 1 c = if c = none then 1 else 0 := by
  cases c <;> simp [ringEquiv,squareZeroEquiv]

theorem inputEquiv_unit (v : I ⊕ J) (a : Fin q) :
    inputEquiv A R q (IncidenceTensor.unitInput A v a,0) = Pi.single (scalarIndex A R q v a) 1 := by
  classical
  funext c
  cases c with
  | inl c =>
    rcases c with ⟨w,b,d⟩
    by_cases hw : w = v
    · subst w
      simp [inputEquiv,oldInputEquiv,IncidenceTensor.unitInput,scalarIndex,Pi.single_apply,
        ringEquiv_one,ite_apply]
      split_ifs <;> simp_all
    · simp [inputEquiv,oldInputEquiv,IncidenceTensor.unitInput,scalarIndex,Pi.single_apply,
        hw,Ne.symm hw,ite_apply]
  | inr c => simp [inputEquiv,scalarIndex,Pi.single_apply]

theorem outputEquiv_chargeOutput (hq : 2 ≤ q) (i : I) :
    outputEquiv A R q (chargeOutput A q hq i) = Pi.single (chargeIndex A R q hq i) 1 := by
  classical
  funext c
  cases c with
  | inl c =>
    cases c with
    | inl c =>
      rcases c with ⟨w,ab,d⟩
      by_cases hw : w = .inl i
      · subst w
        cases d with
        | none =>
          simp [outputEquiv,oldOutputEquiv,chargeOutput,chargeIndex,Pi.single_apply,
            ringEquiv,squareZeroEquiv,ite_apply]
          split_ifs <;> rfl
        | some d =>
          cases d
          simp [outputEquiv,oldOutputEquiv,chargeOutput,chargeIndex,Pi.single_apply,
            ringEquiv,squareZeroEquiv,radicalEquiv,ite_apply]
          split_ifs <;> rfl
      · simp [outputEquiv,oldOutputEquiv,chargeOutput,chargeIndex,Pi.single_apply,
          hw,Ne.symm hw,ite_apply]
    | inr c => simp [outputEquiv,oldOutputEquiv,chargeOutput,chargeIndex,Pi.single_apply]
  | inr c => simp [outputEquiv,chargeOutput,chargeIndex,Pi.single_apply]

def scalarTests (hq : 0 < q) : OldInput A q →ₗ[F] (I ⊕ J → F) where
  toFun x v := (x v ⟨0,hq⟩).fst
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem scalarTests_ker (hq : 0 < q) :
    LinearMap.ker (scalarTests A q hq) = chosenSpace A q hq := by
  ext x
  rw [mem_chosenSpace_iff,LinearMap.mem_ker]
  simp [scalarTests,funext_iff]

def chosenCoordinates (hq : 0 < q) : Coordinates F (chosenSpace A q hq) :=
  let D := Coordinates.kernel (oldInputCoordinates A R q) (Coordinates.pi (I ⊕ J))
    (scalarTests A q hq)
  ⟨D.dimension, (LinearEquiv.ofEq _ _ (scalarTests_ker A q hq).symm).trans D.equiv⟩

end GroupWL.ConstructiveIncidence
