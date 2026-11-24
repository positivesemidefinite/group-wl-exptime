import GroupWL.ConstructiveIncidenceCoefficients
import GroupWL.ChosenCoordinateEncoding
import GroupWL.ConstructiveOutputEncoding

/-! Every incidence output is the sum of at most two wedges of explicit
coordinate forms and readout endpoint forms. -/
namespace GroupWL.ConstructiveIncidence
open IncidenceTensor ConstructiveCoordinates
open scoped BigOperators
variable {F I J : Type} [Field F] [DecidableEq F]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [FiniteCode I] [FiniteCode J]
variable {V : J → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module F (V j)]
variable (A : AffineSystem F I J V) (R : ∀ j, Coordinates F (ReadoutRadical A j)) (q : ℕ)

abbrev FormIndex : Type := OldInputIndex A R q ⊕ (Incidence A × Fin q × Option PUnit.{1})
def formValue (x : OldInputIndex A R q → F) : FormIndex A R q → F
  | .inl i => x i
  | .inr (e,b,c) => endpointCoordinates A R q e x b c

def formU0 : OldOutputIndex A R q → FormIndex A R q
  | .inl ⟨v,ab,c⟩ => .inl ⟨v,(ab.val.1,none)⟩
  | .inr (e,ab,c) => .inl ⟨.inl e.val.1,(ab.1,none)⟩
def formV0 : OldOutputIndex A R q → FormIndex A R q
  | .inl ⟨v,ab,c⟩ => .inl ⟨v,(ab.val.2,c)⟩
  | .inr (e,ab,c) => .inr (e,ab.2,c)
def formU1 : OldOutputIndex A R q → FormIndex A R q
  | .inl ⟨v,ab,c⟩ => .inl ⟨v,(ab.val.1,c)⟩
  | .inr (e,ab,c) => .inl ⟨.inl e.val.1,(ab.1,c)⟩
def formV1 : OldOutputIndex A R q → FormIndex A R q
  | .inl ⟨v,ab,c⟩ => .inl ⟨v,(ab.val.2,none)⟩
  | .inr (e,ab,c) => .inr (e,ab.2,none)
def formSecond : OldOutputIndex A R q → Bool
  | .inl ⟨v,ab,c⟩ => c.isSome
  | .inr (e,ab,c) => c.isSome

theorem omega_formValue (x y : OldInputIndex A R q → F) (z : OldOutputIndex A R q) :
    omegaCoordinates A R q x y z=
      (formValue A R q x (formU0 A R q z)*formValue A R q y (formV0 A R q z)-
        formValue A R q x (formV0 A R q z)*formValue A R q y (formU0 A R q z))+
      if formSecond A R q z then
        (formValue A R q x (formU1 A R q z)*formValue A R q y (formV1 A R q z)-
          formValue A R q x (formV1 A R q z)*formValue A R q y (formU1 A R q z)) else 0 := by
  cases z with
  | inl z =>
    rcases z with ⟨v,ab,c⟩
    cases c <;> simp [omegaCoordinates,formValue,formU0,formV0,formU1,formV1,formSecond,squareZeroProduct,endpointCoordinates] <;> ring
  | inr z =>
    rcases z with ⟨e,ab,c⟩
    cases c with
    | none => simp [omegaCoordinates,formValue,formU0,formV0,formU1,formV1,formSecond,squareZeroProduct,endpointCoordinates]; ring
    | some c =>
      cases c
      simp [omegaCoordinates,formValue,formU0,formV0,formU1,formV1,formSecond,squareZeroProduct,endpointCoordinates]
      ring_nf
      rfl

def formMap : (OldInputIndex A R q → F) →ₗ[F] (FormIndex A R q → F) where
  toFun := formValue A R q
  map_add' x y := by
    funext f
    cases f with
    | inl i => rfl
    | inr f =>
      rcases f with ⟨e,b,c⟩
      cases c <;> simp [formValue,endpointCoordinates,add_mul,Finset.sum_add_distrib]
  map_smul' a x := by
    funext f
    cases f with
    | inl i => rfl
    | inr f =>
      rcases f with ⟨e,b,c⟩
      cases c <;> simp [formValue,endpointCoordinates,smul_eq_mul,Finset.mul_sum,mul_assoc]

def numericFormMap : (Fin (FiniteCode.size (OldInputIndex A R q)) → F) →ₗ[F]
    (Fin (FiniteCode.size (FormIndex A R q)) → F) :=
  (Coordinates.pi (FormIndex A R q)).equiv.toLinearMap.comp
    ((formMap A R q).comp (Coordinates.pi (OldInputIndex A R q)).equiv.symm.toLinearMap)

theorem numericFormMap_apply (x : Fin (FiniteCode.size (OldInputIndex A R q)) → F)
    (f : FormIndex A R q) :
    numericFormMap A R q x (FiniteCode.equiv f)=
      formValue A R q (fun i=>x (FiniteCode.equiv i)) f := by
  change formValue A R q _ ((FiniteCode.equiv (α:=FormIndex A R q)).symm (FiniteCode.equiv f))=_
  rw [Equiv.symm_apply_apply]
  rfl

theorem formIndex_endpoint (e : Incidence A) (b : Fin q) (c : Option PUnit) :
    (FiniteCode.equiv (α:=FormIndex A R q) (.inr (e,b,c))).val=
      FiniteCode.size (OldInputIndex A R q)+((FiniteCode.equiv e).val*q+b.val)*2+(FiniteCode.equiv c).val := by
  rw [FiniteCode.sum_inr_val]
  simp only [FiniteCode.prod_val,FiniteCode.fin_val]
  change _+((FiniteCode.equiv e).val*(q*2)+(b.val*2+(FiniteCode.equiv c).val))=_
  ring

end GroupWL.ConstructiveIncidence
