import GroupWL.ConstructiveInputBounds
import GroupWL.SourceFormWords
import GroupWL.MachinePrograms.WedgeDescriptorTables

/-! Safety and exact values of the descriptor and form tables in canonical coordinates. -/
namespace GroupWL.MachinePrograms.DescriptorPipeline
open ConstructiveIncidence IncidenceTensor ConstructiveCoordinates NatArrayLanguage NatArrayExpressions
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [FiniteCode I] [FiniteCode J]
variable (p : ℕ) [Fact p.Prime]
variable {V : J → Type} [∀j, AddCommGroup (V j)] [∀j, Module (ZMod p) (V j)]
variable (A : AffineSystem (ZMod p) I J V) (R : ∀j, Coordinates (ZMod p) (ReadoutRadical A j)) (q cap : ℕ)
abbrev Field := InternalWedgeDescriptors.Field
def canonicalField (f : Field) := List.ofFn (fun i : Fin (FiniteCode.size (OldOutputIndex A R q)) =>
  descriptorValue A R q f (FiniteCode.equiv.symm i))

private theorem codes (j : ℕ) (hj : j < FiniteCode.size (Incidence A)) :
    (edgeIncidences A)[j]?.getD 0 < FiniteCode.size I * FiniteCode.size J := by
  let e := (FiniteCode.equiv (α := Incidence A)).symm ⟨j,hj⟩
  change (List.ofFn _)[j]?.getD 0 < _
  simp only [List.getElem?_ofFn, dif_pos hj, Option.getD_some]
  exact (FiniteCode.equiv (α := I × J) e.val).isLt

theorem edgeValid (M : ℕ) (hq : 0 < q) (hJ : 0 < FiniteCode.size J) (hM : 2 ≤ M)
    (size : inputTotal A R q + q*2+1 ≤ M)
    (forms : FiniteCode.size (OldInputIndex A R q) + FiniteCode.size (Incidence A)*q*2 ≤ M) :
    EdgeWedgeDescriptors.Valid (edgeData A R q) M := by
  refine ⟨hq,hJ,?_,?_,?_,codes p A,forms,hM⟩
  · simp [edgeData,inputOffsets]; change _ ≤ FiniteCode.size I + FiniteCode.size J; omega
  · simp [edgeData,edgeIncidences]
  · intro v hv
    let i := (FiniteCode.equiv (α := I)).symm ⟨v,hv⟩
    have hi : (FiniteCode.equiv (α := I⊕J) (.inl i)).val = v := by simp [FiniteCode.sum_inl_val,i]
    change (inputOffsets A R q)[v]?.getD 0 + q*2+1 ≤ M
    rw [←hi,inputOffsets_read]
    have := inputOffset_le_total A R q (.inl i)
    omega

theorem formValid (radicals : List ℕ) (hq : 0 < q) (hJ : 0 < FiniteCode.size J)
    (hN : 0 < FiniteCode.size (OldInputIndex A R q))
    (hr : radicals.length = FiniteCode.size I * FiniteCode.size J * FiniteCode.size I)
    (dims : ∀v,ringDimension A R v ≤ FiniteCode.size I+1) :
    IncidenceFormMatrix.Valid (formData p A R q radicals) := by
  refine ⟨hq,hJ,hN,?_,?_,?_,hr,?_,?_,codes p A⟩
  · simp [formData,ringDimensions]; rfl
  · simp [formData,inputOffsets]; rfl
  · simp [formData,edgeIncidences]
  · intro v hv
    let i := (FiniteCode.equiv (α := I⊕J)).symm ⟨v,hv⟩
    have hi : (FiniteCode.equiv i).val = v := by simp [i]
    change (ringDimensions A R)[v]?.getD 0 ≤ _
    rw [←hi,ringDimensions_read]
    exact dims i
  · intro v hv
    let i := (FiniteCode.equiv (α := I⊕J)).symm ⟨v,hv⟩
    have hi : (FiniteCode.equiv i).val = v := by simp [i]
    change (inputOffsets A R q)[v]?.getD 0 + q*(ringDimensions A R)[v]?.getD 0 ≤ _
    rw [←hi,inputOffsets_read,ringDimensions_read]
    exact (inputOffset_segment_le_total A R q i).trans (inputTotal_eq A R q).le

theorem field_runs (f : Field) (M : ℕ) (dims : ∀v,ringDimension A R v ≤ cap)
    (di : InternalWedgeDescriptors.Valid (internalData A R q cap) M)
    (de : EdgeWedgeDescriptors.Valid (edgeData A R q) M)
    (S : WedgeDescriptorTables.State f) (bounded : S.Bounded M)
    (ri : InternalWedgeDescriptors.Ready (internalData A R q cap) (inputs S.left.left.left))
    (re : EdgeWedgeDescriptors.Ready (edgeData A R q) (inputs S.left.right))
    (ti : S.left.left.left.scalar (.inl .total)=FiniteCode.size (I⊕J)*FiniteCode.size (Pair q)*cap)
    (te : S.left.right.scalar (.inl .total)=FiniteCode.size (Incidence A)*q*q*2)
    (flags : S.left.left.right.array .flags=internalRaw A R q cap .keep)
    (count : S.left.left.right.scalar .selected=FiniteCode.size (InternalIndex A R q))
    (size : FiniteCode.size (InternalIndex A R q)+FiniteCode.size (Incidence A)*q*q*2≤M) :
    ∃t≤(FiniteCode.size (I⊕J)*FiniteCode.size (Pair q)*cap)*((InternalWedgeDescriptors.expression f).cost+12)+
      (FiniteCode.size (Incidence A)*q*q*2)*((EdgeWedgeDescriptors.expression f).cost+4)+8*M+32,∃T,
      Runs (storageBound (WedgeDescriptorTables.Reg f) WedgeDescriptorTables.Arr M) (WedgeDescriptorTables.program f) S t T ∧ T.Bounded M ∧
      T.right.array 2=canonicalField p A R q f := by
  obtain ⟨t,ht,T,run,hT,out⟩ := WedgeDescriptorTables.program_runs (internalData A R q cap) (edgeData A R q) f
    M di de S bounded ri re ti te (by rw [flags];exact List.length_ofFn)
    (by rw [flags];exact internalKeep_binary A R q cap)
    (by rw [flags,count,internalKeep_total A R q cap dims])
    (by rw [count];exact size)
  change t ≤ _ * _ + _ * _ + 8*(S.left.left.right.scalar .selected+FiniteCode.size (Incidence A)*q*q*2)+32 at ht
  rw [count] at ht
  rw [flags] at out
  exact ⟨t,by dsimp only [internalData,edgeData] at ht; omega,T,run,hT,
    out.trans (descriptor_tables_correct A R q cap dims f)⟩

theorem matrix_runs (radicals : List ℕ) (M : ℕ) (v : IncidenceFormMatrix.Valid (formData p A R q radicals))
    (room : 2≤M) (spec : RadicalTableSpec p A R radicals) (values : ∀x∈radicals,x<p)
    (S : Store (Registers IncidenceFormMatrix.Reg IncidenceFormMatrix.expression.need) IncidenceFormMatrix.Arr)
    (bounded : S.Bounded M) (ready : IncidenceFormMatrix.Ready (formData p A R q radicals) (inputs S))
    (total : S.scalar (.inl .total)=IncidenceFormMatrix.forms (formData p A R q radicals)*FiniteCode.size (OldInputIndex A R q)) :
    ∃t≤(IncidenceFormMatrix.forms (formData p A R q radicals)*FiniteCode.size (OldInputIndex A R q))*
      (IncidenceFormMatrix.expression.cost+4)+6,∃T,
      Runs (storageBound (Registers IncidenceFormMatrix.Reg IncidenceFormMatrix.expression.need) IncidenceFormMatrix.Arr M) IncidenceFormMatrix.program S t T ∧ T.Bounded M ∧
      T.array .output=formMatrix p A R q := by
  obtain ⟨t,ht,T,run,hT,_,out⟩ := IncidenceFormMatrix.program_runs (formData p A R q radicals) M
    v room S bounded ready total
  exact ⟨t,ht,T,run,hT,out.trans (formData_word p A R q radicals spec values)⟩

end GroupWL.MachinePrograms.DescriptorPipeline
