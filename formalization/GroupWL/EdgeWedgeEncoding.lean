import GroupWL.InternalWedgeForms
import GroupWL.MachinePrograms.EdgeWedgeDescriptors

/-! Constant-width edge descriptors agree with canonical incidence-output form indices. -/
namespace GroupWL.ConstructiveIncidence
open IncidenceTensor ConstructiveCoordinates MachinePrograms
variable {F I J : Type} [Field F] [DecidableEq F]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [FiniteCode I] [FiniteCode J]
variable {V : J → Type} [∀j,AddCommGroup (V j)] [∀j,Module F (V j)]
variable (A : AffineSystem F I J V) (R : ∀j,Coordinates F (ReadoutRadical A j)) (q : ℕ)

abbrev EdgeIndex := Incidence A×(Fin q×Fin q)×Option PUnit.{1}

def edgeIncidences : List ℕ := List.ofFn (fun i : Fin (FiniteCode.size (Incidence A)) =>
  (FiniteCode.equiv (α:=I×J) ((FiniteCode.equiv (α:=Incidence A)).symm i).val).val)

def edgeData : EdgeWedgeDescriptors.Data where
  frames := q
  readouts := FiniteCode.size J
  blocks := FiniteCode.size I
  edges := FiniteCode.size (Incidence A)
  oldInput := FiniteCode.size (OldInputIndex A R q)
  offsets := inputOffsets A R q
  incidences := edgeIncidences A

def edgeKey (e : Incidence A) (a b : Fin q) (c : Option PUnit.{1}) : ℕ :=
  (((FiniteCode.equiv e).val*q+a.val)*q+b.val)*2+(FiniteCode.equiv c).val

theorem edgeIndex_code (e : Incidence A) (a b : Fin q) (c : Option PUnit.{1}) :
    (FiniteCode.equiv (α:=EdgeIndex A q) (e,(a,b),c)).val=edgeKey A q e a b c := by
  simp only [FiniteCode.prod_val,FiniteCode.fin_val,edgeKey]
  change (FiniteCode.equiv e).val*(q*q*2)+((a.val*q+b.val)*2+(FiniteCode.equiv c).val)=_
  ring

theorem edgeIndex_size : FiniteCode.size (EdgeIndex A q)=FiniteCode.size (Incidence A)*q*q*2 := by
  change FiniteCode.size (Incidence A)*(q*q*2)=_
  ring

theorem edgeIncidences_read (e : Incidence A) :
    (edgeIncidences A)[(FiniteCode.equiv e).val]?.getD 0=
      (FiniteCode.equiv e.val.1).val*FiniteCode.size J+(FiniteCode.equiv e.val.2).val := by
  simp only [edgeIncidences,List.getElem?_ofFn,(FiniteCode.equiv e).isLt,dif_pos,Option.getD_some]
  erw [Equiv.symm_apply_apply]
  exact FiniteCode.prod_val _ _

theorem edgeKey_parts (e : Incidence A) (a b : Fin q) (c : Option PUnit.{1}) :
    edgeKey A q e a b c/2/q/q=(FiniteCode.equiv e).val ∧
    edgeKey A q e a b c/2/q%q=a.val ∧ edgeKey A q e a b c/2%q=b.val ∧
    edgeKey A q e a b c%2=(FiniteCode.equiv c).val := by
  have hc : (FiniteCode.equiv c).val<2 := (FiniteCode.equiv c).isLt
  have hq : 0<q := by have := a.isLt; omega
  have h2 : edgeKey A q e a b c/2=((FiniteCode.equiv e).val*q+a.val)*q+b.val := by
    unfold edgeKey
    rw [Nat.mul_comm _ 2,Nat.mul_add_div (by decide),Nat.div_eq_of_lt hc,Nat.add_zero]
  have hb : (((FiniteCode.equiv e).val*q+a.val)*q+b.val)/q=(FiniteCode.equiv e).val*q+a.val := by
    rw [Nat.mul_comm _ q,Nat.mul_add_div hq,Nat.div_eq_of_lt b.isLt,Nat.add_zero]
  rw [h2,hb]
  refine ⟨?_,?_,?_,?_⟩
  · rw [Nat.mul_comm _ q,Nat.mul_add_div hq,Nat.div_eq_of_lt a.isLt,Nat.add_zero]
  · rw [Nat.mul_add_mod',Nat.mod_eq_of_lt a.isLt]
  · rw [Nat.mul_add_mod',Nat.mod_eq_of_lt b.isLt]
  · rw [edgeKey,Nat.mul_add_mod',Nat.mod_eq_of_lt hc]

theorem edgeValue_form (e : Incidence A) (a b : Fin q) (c : Option PUnit.{1}) (f : EdgeWedgeDescriptors.Field) :
    EdgeWedgeDescriptors.value (edgeData A R q) f (edgeKey A q e a b c)=
      descriptorValue A R q f (.inr (e,(a,b),c)) := by
  obtain ⟨he,ha,hb,hc⟩ := edgeKey_parts A q e a b c
  have hread : ((FiniteCode.equiv e.val.1).val*FiniteCode.size J+(FiniteCode.equiv e.val.2).val)/FiniteCode.size J=
      (FiniteCode.equiv e.val.1).val := by
    rw [Nat.mul_comm _ (FiniteCode.size J),Nat.mul_add_div (by have := (FiniteCode.equiv e.val.2).isLt; omega),
      Nat.div_eq_of_lt (FiniteCode.equiv e.val.2).isLt,Nat.add_zero]
  have ho : (inputOffsets A R q)[(FiniteCode.equiv e.val.1).val]?.getD 0=inputOffset A R q (.inl e.val.1) := by
    simpa only [FiniteCode.sum_inl_val] using inputOffsets_read A R q (.inl e.val.1)
  cases f <;> simp only [EdgeWedgeDescriptors.value,edgeData,he,ha,hb,hc,
    EdgeWedgeDescriptors.read,edgeIncidences_read,hread,ho,descriptorValue,
    formU0,formV0,formU1,formV1,formSecond,FiniteCode.sum_inl_val,inputIndex_val,
    ringDimension_block,FiniteCode.option_none_val,Nat.add_zero,formIndex_endpoint]
  all_goals first
    | rfl
    | cases c <;> simp only [FiniteCode.option_none_val,FiniteCode.option_some_val,Option.isSome_none,Option.isSome_some,Bool.false_eq_true,↓reduceIte,Nat.lt_add_one,zero_lt_one]
      all_goals rfl

def edgeRaw (f : EdgeWedgeDescriptors.Field) : List ℕ :=
  List.ofFn (fun i : Fin (FiniteCode.size (Incidence A)*q*q*2) => EdgeWedgeDescriptors.value (edgeData A R q) f i)

theorem edgeRaw_form (f : EdgeWedgeDescriptors.Field) : edgeRaw A R q f=
    List.ofFn (fun i : Fin (FiniteCode.size (EdgeIndex A q)) =>
      descriptorValue A R q f (.inr (FiniteCode.equiv.symm i))) := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i<FiniteCode.size (EdgeIndex A q)
  · have hi' : i<FiniteCode.size (Incidence A)*q*q*2 := by rwa [edgeIndex_size] at hi
    simp only [edgeRaw,List.getElem?_ofFn,dif_pos hi,dif_pos hi']
    congr 1
    let z : EdgeIndex A q := FiniteCode.equiv.symm ⟨i,hi⟩
    have hk : edgeKey A q z.1 z.2.1.1 z.2.1.2 z.2.2=i := by
      rw [←edgeIndex_code]
      simp [z]
    exact (congrArg (EdgeWedgeDescriptors.value (edgeData A R q) f) hk).symm.trans
      (edgeValue_form A R q z.1 z.2.1.1 z.2.1.2 z.2.2 f)
  · have hi' : ¬i<FiniteCode.size (Incidence A)*q*q*2 := by rwa [edgeIndex_size] at hi
    simp only [edgeRaw,List.getElem?_ofFn,dif_neg hi,dif_neg hi']

theorem descriptor_tables_correct (cap : ℕ) (bound : ∀v,ringDimension A R v≤cap)
    (f : InternalWedgeDescriptors.Field) :
    SelectArray.selectedPrefix (internalRaw A R q cap .keep) (internalRaw A R q cap f)
      (internalRaw A R q cap .keep).length++edgeRaw A R q f=
      List.ofFn (fun i : Fin (FiniteCode.size (OldOutputIndex A R q)) =>
        descriptorValue A R q f (FiniteCode.equiv.symm i)) := by
  rw [internal_compaction_form A R q cap bound,edgeRaw_form]
  exact (FiniteCode.ofFn_sum (descriptorValue A R q f)).symm

end GroupWL.ConstructiveIncidence
