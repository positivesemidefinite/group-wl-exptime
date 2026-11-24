import GroupWL.ConstructiveOutputEncoding
import GroupWL.MachinePrograms.InternalWedgeDescriptors
import GroupWL.FiniteCodeCompaction
import GroupWL.FiniteCodeFlatRanks

/-! Canonical meanings of the operational internal-wedge descriptor rows. -/
namespace GroupWL.ConstructiveIncidence
open IncidenceTensor ConstructiveCoordinates MachinePrograms
variable {F I J : Type} [Field F] [DecidableEq F]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [FiniteCode I] [FiniteCode J]
variable {V : J → Type} [∀j,AddCommGroup (V j)] [∀j,Module F (V j)]
variable (A : AffineSystem F I J V) (R : ∀j,Coordinates F (ReadoutRadical A j)) (q cap : ℕ)

def inputOffsets : List ℕ := List.ofFn (fun i : Fin (FiniteCode.size (I⊕J)) =>
  inputOffset A R q (FiniteCode.equiv.symm i))

def internalData : InternalWedgeDescriptors.Data where
  frames := q
  cap := cap
  vertices := FiniteCode.size (I⊕J)
  pairs := FiniteCode.size (Pair q)
  dimensions := ringDimensions A R
  offsets := inputOffsets A R q
  pairCodes := FramePairEncoding.word q

def internalKey (v : I⊕J) (ab : Pair q) (c : Option (RadicalIndex A R v)) : ℕ :=
  ((FiniteCode.equiv v).val*FiniteCode.size (Pair q)+(FiniteCode.equiv ab).val)*cap+(FiniteCode.equiv c).val

theorem ringDimensions_read (v : I⊕J) :
    (ringDimensions A R)[(FiniteCode.equiv v).val]?.getD 0=ringDimension A R v := by
  simp only [ringDimensions,List.getElem?_ofFn,(FiniteCode.equiv v).isLt,dif_pos,Option.getD_some]
  erw [Equiv.symm_apply_apply]

theorem inputOffsets_read (v : I⊕J) :
    (inputOffsets A R q)[(FiniteCode.equiv v).val]?.getD 0=inputOffset A R q v := by
  simp only [inputOffsets,List.getElem?_ofFn,(FiniteCode.equiv v).isLt,dif_pos,Option.getD_some]
  erw [Equiv.symm_apply_apply]

theorem internalKey_parts (bound : ∀v,ringDimension A R v≤cap)
    (v : I⊕J) (ab : Pair q) (c : Option (RadicalIndex A R v)) :
    internalKey A R q cap v ab c/cap/FiniteCode.size (Pair q)=(FiniteCode.equiv v).val ∧
    internalKey A R q cap v ab c/cap%FiniteCode.size (Pair q)=(FiniteCode.equiv ab).val ∧
    internalKey A R q cap v ab c%cap=(FiniteCode.equiv c).val := by
  have hc : (FiniteCode.equiv c).val<cap := (FiniteCode.equiv c).isLt.trans_le (bound v)
  have hd : internalKey A R q cap v ab c/cap=
      (FiniteCode.equiv v).val*FiniteCode.size (Pair q)+(FiniteCode.equiv ab).val := by
    unfold internalKey
    rw [Nat.mul_comm _ cap,Nat.mul_add_div (by omega),Nat.div_eq_of_lt hc,Nat.add_zero]
  rw [hd]
  refine ⟨?_,?_,?_⟩
  · rw [Nat.mul_comm _ (FiniteCode.size (Pair q)),Nat.mul_add_div (by have := (FiniteCode.equiv ab).isLt; omega),Nat.div_eq_of_lt (FiniteCode.equiv ab).isLt,Nat.add_zero]
  · simp only [Nat.mul_add_mod',Nat.mod_eq_of_lt (FiniteCode.equiv ab).isLt]
  · simp only [internalKey,Nat.mul_add_mod',Nat.mod_eq_of_lt hc]

theorem internalValue (bound : ∀v,ringDimension A R v≤cap)
    (v : I⊕J) (ab : Pair q) (c : Option (RadicalIndex A R v)) (f : InternalWedgeDescriptors.Field) :
    InternalWedgeDescriptors.value (internalData A R q cap) f (internalKey A R q cap v ab c)=
      match f with
      | .u0 => inputOffset A R q v+ab.val.1.val*ringDimension A R v
      | .v0 => inputOffset A R q v+ab.val.2.val*ringDimension A R v+(FiniteCode.equiv c).val
      | .u1 => inputOffset A R q v+ab.val.1.val*ringDimension A R v+(FiniteCode.equiv c).val
      | .v1 => inputOffset A R q v+ab.val.2.val*ringDimension A R v
      | .second => if 0<(FiniteCode.equiv c).val then 1 else 0
      | .keep => 1 := by
  obtain ⟨hv,hab,hc⟩ := internalKey_parts A R q cap bound v ab c
  have ha : (ab.val.1.val*q+ab.val.2.val)/q=ab.val.1.val := by
    rw [Nat.mul_comm _ q,Nat.mul_add_div (by have := ab.val.2.isLt; omega),Nat.div_eq_of_lt ab.val.2.isLt,Nat.add_zero]
  have hb : (ab.val.1.val*q+ab.val.2.val)%q=ab.val.2.val := by
    simp only [Nat.mul_add_mod',Nat.mod_eq_of_lt ab.val.2.isLt]
  have hcsize : (FiniteCode.equiv c).val<ringDimension A R v := (FiniteCode.equiv c).isLt
  cases f <;> simp only [InternalWedgeDescriptors.value,internalData,hv,hab,hc,InternalWedgeDescriptors.read,
    FramePairEncoding.word_read,ringDimensions_read,inputOffsets_read,ha,hb,if_pos hcsize]

end GroupWL.ConstructiveIncidence
