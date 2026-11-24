import GroupWL.ConstructiveTensor

/-! Scalar-first formulas for the obstruction entries. The only nontrivial
endpoint operation is multiplication by a materialized radical lift matrix. -/
namespace GroupWL.ConstructiveIncidence
open IncidenceTensor ConstructiveCoordinates
open scoped BigOperators
variable {F I J : Type} [Field F] [DecidableEq F]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [FiniteCode I] [FiniteCode J]
variable {V : J → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module F (V j)]
variable (A : AffineSystem F I J V) (R : ∀ j, Coordinates F (ReadoutRadical A j)) (q : ℕ)

theorem ringEquiv_mul (v : I ⊕ J) (x y : RingAt A v) (c : Option (RadicalIndex A R v)) :
    ringEquiv A R v (x*y) c = match c with
    | none => ringEquiv A R v x none * ringEquiv A R v y none
    | some c => ringEquiv A R v x none * ringEquiv A R v y (some c) +
        ringEquiv A R v y none * ringEquiv A R v x (some c) := by
  cases c with
  | none => rfl
  | some c => simp [ringEquiv,squareZeroEquiv,TrivSqZeroExt.snd_mul,smul_eq_mul]

def radicalLift (e : Incidence A) (j : Fin (R e.1.2).dimension) : F :=
  ((R e.1.2).equiv.symm (Pi.single j 1)).val ⟨e.1.1,e.2⟩

theorem readoutProjection_coordinates (e : Incidence A) (x : ReadoutRadical A e.1.2) :
    readoutProjection A e x = ∑j, (R e.1.2).equiv x j * radicalLift A R e j := by
  let f := (readoutProjection A e).comp (R e.1.2).equiv.symm.toLinearMap
  have h := LinearMap.pi_apply_eq_sum_univ f ((R e.1.2).equiv x)
  have he (i : Fin (R e.1.2).dimension) :
      (fun j : Fin (R e.1.2).dimension => if i=j then (1:F) else 0) = Pi.single i 1 := by
    funext j
    simp [Pi.single_apply,eq_comm]
  simpa only [f,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply,
    he,radicalLift,readoutProjection,LinearMap.coe_mk,AddHom.coe_mk,smul_eq_mul] using h

def endpointCoordinates (e : Incidence A) (x : OldInputIndex A R q → F) (b : Fin q) :
    Option PUnit → F
  | none => x ⟨.inr e.1.2,(b,none)⟩
  | some _ => ∑j : Fin (R e.1.2).dimension, x ⟨.inr e.1.2,(b,some j)⟩ * radicalLift A R e j

theorem endpointMap_coordinates (e : Incidence A) (x : OldInput A q) (b : Fin q)
    (c : Option PUnit) :
    edgeEquiv (endpointMap A e (x (.inr e.1.2) b)) c =
      endpointCoordinates A R q e (oldInputEquiv A R q x) b c := by
  cases c with
  | none => simp [edgeEquiv,endpointMap,squareZeroEquiv,endpointCoordinates,oldInputEquiv,ringEquiv]
  | some c =>
    cases c
    simpa [edgeEquiv,endpointMap,squareZeroEquiv,endpointCoordinates,oldInputEquiv,ringEquiv,radicalEquiv] using readoutProjection_coordinates A R e (x (.inr e.1.2) b).snd

def squareZeroProduct {η : Type} (x y : Option η → F) : Option η → F
  | none => x none*y none
  | some c => x none*y (some c)+y none*x (some c)

def omegaCoordinates (x y : OldInputIndex A R q → F) : OldOutputIndex A R q → F
  | .inl ⟨v,ab,c⟩ =>
      squareZeroProduct (fun d => x ⟨v,(ab.1.1,d)⟩) (fun d => y ⟨v,(ab.1.2,d)⟩) c -
      squareZeroProduct (fun d => y ⟨v,(ab.1.1,d)⟩) (fun d => x ⟨v,(ab.1.2,d)⟩) c
  | .inr ⟨e,ab,c⟩ =>
      squareZeroProduct (fun d => x ⟨.inl e.1.1,(ab.1,d)⟩)
        (endpointCoordinates A R q e y ab.2) c -
      squareZeroProduct (fun d => y ⟨.inl e.1.1,(ab.1,d)⟩)
        (endpointCoordinates A R q e x ab.2) c

theorem omega_coordinates (x y : OldInput A q) :
    oldOutputEquiv A R q (omega A q x y) =
      omegaCoordinates A R q (oldInputEquiv A R q x) (oldInputEquiv A R q y) := by
  funext c
  cases c with
  | inl c =>
    rcases c with ⟨v,ab,c⟩
    change ringEquiv A R v (x v ab.1.1*y v ab.1.2-y v ab.1.1*x v ab.1.2) c = _
    rw [map_sub,Pi.sub_apply,ringEquiv_mul,ringEquiv_mul]
    cases c <;> rfl
  | inr c =>
    rcases c with ⟨e,ab,c⟩
    change edgeEquiv (x (.inl e.1.1) ab.1 * endpointMap A e (y (.inr e.1.2) ab.2) -
      y (.inl e.1.1) ab.1 * endpointMap A e (x (.inr e.1.2) ab.2)) c = _
    rw [map_sub,Pi.sub_apply]
    have hm (u v : EdgeRing (F:=F)) : edgeEquiv (u*v) = squareZeroProduct (edgeEquiv u) (edgeEquiv v) := by
      funext d
      cases d with
      | none => rfl
      | some d => cases d; simp [edgeEquiv,squareZeroEquiv,squareZeroProduct,TrivSqZeroExt.snd_mul,smul_eq_mul,mul_comm]
    rw [hm,hm]
    change squareZeroProduct (edgeEquiv (x (.inl e.1.1) ab.1)) (edgeEquiv (endpointMap A e (y (.inr e.1.2) ab.2))) c -
      squareZeroProduct (edgeEquiv (y (.inl e.1.1) ab.1)) (edgeEquiv (endpointMap A e (x (.inr e.1.2) ab.2))) c = _
    have hxe : edgeEquiv (endpointMap A e (x (.inr e.1.2) ab.2)) =
        endpointCoordinates A R q e (oldInputEquiv A R q x) ab.2 := funext (endpointMap_coordinates A R q e x ab.2)
    have hye : edgeEquiv (endpointMap A e (y (.inr e.1.2) ab.2)) =
        endpointCoordinates A R q e (oldInputEquiv A R q y) ab.2 := funext (endpointMap_coordinates A R q e y ab.2)
    rw [hxe,hye]
    rfl

def paddedSliceCoordinates (a : OldInputIndex A R q → F) (x : InputIndex A R q → F) :
    OutputIndex A R q → F
  | .inl z => omegaCoordinates A R q a (fun i => x (.inl i)) z
  | .inr _ => 0

theorem slice_coordinates (a : OldInput A q) (x : PaddedInput A q) :
    outputEquiv A R q (sliceMap A q a x) =
      paddedSliceCoordinates A R q (oldInputEquiv A R q a) (inputEquiv A R q x) := by
  funext z
  cases z with
  | inl z => exact congrFun (omega_coordinates A R q a x.1) z
  | inr z => simp [outputEquiv,sliceMap_apply,paddedSliceCoordinates]

theorem obstruction_entry (hq : 0<q) (a : chosenSpace A q hq)
    (i : InputIndex A R q) (z : OutputIndex A R q) :
    ConstructiveTensor.obstructionMap A R q hq a i z =
      paddedSliceCoordinates A R q (oldInputEquiv A R q a.val) (Pi.single i 1) z := by
  change outputEquiv A R q (sliceMap A q a.val ((inputEquiv A R q).symm (Pi.single i 1))) z = _
  rw [slice_coordinates,LinearEquiv.apply_symm_apply]

end GroupWL.ConstructiveIncidence
