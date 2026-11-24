import GroupWL.InternalWedgeEncoding
import GroupWL.MachinePrograms.PaddedFlags

/-! The uniform internal-wedge candidate scan compacts into canonical internal-output order. -/
namespace GroupWL.ConstructiveIncidence
open IncidenceTensor ConstructiveCoordinates MachinePrograms
variable {F I J : Type} [Field F] [DecidableEq F]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [FiniteCode I] [FiniteCode J]
variable {V : J → Type} [∀j,AddCommGroup (V j)] [∀j,Module F (V j)]
variable (A : AffineSystem F I J V) (R : ∀j,Coordinates F (ReadoutRadical A j)) (q cap : ℕ)

abbrev InternalIndex := Σv : I⊕J,Pair q×Option (RadicalIndex A R v)

def internalRaw (f : InternalWedgeDescriptors.Field) : List ℕ :=
  List.ofFn (fun i : Fin (FiniteCode.size (I⊕J)*FiniteCode.size (Pair q)*cap) =>
    InternalWedgeDescriptors.value (internalData A R q cap) f i)

theorem internalKey_lt (bound : ∀v,ringDimension A R v≤cap)
    (v : I⊕J) (ab : Pair q) (c : Option (RadicalIndex A R v)) :
    internalKey A R q cap v ab c<FiniteCode.size (I⊕J)*FiniteCode.size (Pair q)*cap := by
  have hv := (FiniteCode.equiv v).isLt
  have hab := (FiniteCode.equiv ab).isLt
  have hc := (FiniteCode.equiv c).isLt.trans_le (bound v)
  have hm := Nat.mul_le_mul_right (FiniteCode.size (Pair q)) (Nat.succ_le_of_lt hv)
  have hx : (FiniteCode.equiv v).val*FiniteCode.size (Pair q)+(FiniteCode.equiv ab).val<FiniteCode.size (I⊕J)*FiniteCode.size (Pair q) := by nlinarith
  have := Nat.mul_le_mul_right cap (Nat.succ_le_of_lt hx)
  unfold internalKey
  nlinarith

theorem internalRaw_read (bound : ∀v,ringDimension A R v≤cap)
    (v : I⊕J) (ab : Pair q) (c : Option (RadicalIndex A R v)) (f : InternalWedgeDescriptors.Field) :
    (internalRaw A R q cap f)[internalKey A R q cap v ab c]?.getD 0=
      InternalWedgeDescriptors.value (internalData A R q cap) f (internalKey A R q cap v ab c) := by
  simp only [internalRaw,List.getElem?_ofFn,dif_pos (internalKey_lt A R q cap bound v ab c),Option.getD_some]

theorem internalKeep_binary : ∀x∈internalRaw A R q cap .keep,x≤1 := by
  intro x hx
  rcases List.mem_ofFn.mp hx with ⟨i,rfl⟩
  change (if _ then 1 else 0)≤1
  split_ifs <;> omega

theorem internalKeep_block (v : I⊕J) (j : ℕ) (hj : j<FiniteCode.size (Pair q)*cap) :
    (internalRaw A R q cap .keep)[(FiniteCode.equiv v).val*(FiniteCode.size (Pair q)*cap)+j]?.getD 0=
      (PaddedFlags.word (ringDimension A R v) (FiniteCode.size (Pair q)) cap)[j]?.getD 0 := by
  have hb : (FiniteCode.equiv v).val*(FiniteCode.size (Pair q)*cap)+j<
      FiniteCode.size (I⊕J)*FiniteCode.size (Pair q)*cap := by
    have := Nat.mul_le_mul_right (FiniteCode.size (Pair q)*cap) (Nat.succ_le_of_lt (FiniteCode.equiv v).isLt)
    nlinarith
  have hpos : 0<FiniteCode.size (Pair q)*cap := by omega
  have hd : ((FiniteCode.equiv v).val*(FiniteCode.size (Pair q)*cap)+j)/cap/FiniteCode.size (Pair q)=
      (FiniteCode.equiv v).val := by
    rw [Nat.div_div_eq_div_mul,Nat.mul_comm cap (FiniteCode.size (Pair q)),Nat.mul_comm (FiniteCode.equiv v).val _,
      Nat.mul_add_div hpos,Nat.div_eq_of_lt hj,Nat.add_zero]
  have hm : ((FiniteCode.equiv v).val*(FiniteCode.size (Pair q)*cap)+j)%cap=j%cap := by
    rw [←Nat.mul_assoc,Nat.mul_add_mod']
  simp only [internalRaw,List.getElem?_ofFn,dif_pos hb,Option.getD_some,
    InternalWedgeDescriptors.value,internalData,hd,hm,InternalWedgeDescriptors.read,ringDimensions_read,
    PaddedFlags.word,List.getElem?_ofFn,dif_pos hj,Option.getD_some]

theorem internalKeep_total (bound : ∀v,ringDimension A R v≤cap) :
    FilterRanks.count (internalRaw A R q cap .keep) (internalRaw A R q cap .keep).length=
      FiniteCode.size (InternalIndex A R q) := by
  have h := FiniteCode.sigma_flat_size
    (β:=fun v : I⊕J => Pair q×Option (RadicalIndex A R v))
    (FiniteCode.size (Pair q)*cap) (internalRaw A R q cap .keep)
    (fun v => PaddedFlags.word (ringDimension A R v) (FiniteCode.size (Pair q)) cap)
    (internalKeep_block A R q cap)
    (fun v => (PaddedFlags.count_blocks (ringDimension A R v) (FiniteCode.size (Pair q)) cap
      (FiniteCode.size (Pair q)) (bound v) le_rfl).symm)
  simpa only [internalRaw,List.length_ofFn,Nat.mul_assoc] using h.symm

theorem internalKeep_rank (bound : ∀v,ringDimension A R v≤cap)
    (v : I⊕J) (ab : Pair q) (c : Option (RadicalIndex A R v)) :
    FilterRanks.count (internalRaw A R q cap .keep) (internalKey A R q cap v ab c)=
      (FiniteCode.equiv (α:=InternalIndex A R q) ⟨v,ab,c⟩).val := by
  have h := FiniteCode.sigma_flat_rank
    (β:=fun v : I⊕J => Pair q×Option (RadicalIndex A R v))
    (FiniteCode.size (Pair q)*cap) (internalRaw A R q cap .keep)
    (fun v => PaddedFlags.word (ringDimension A R v) (FiniteCode.size (Pair q)) cap)
    (fun _ z => (FiniteCode.equiv z.1).val*cap+(FiniteCode.equiv z.2).val)
    (internalKeep_block A R q cap)
    (fun v => (PaddedFlags.count_blocks (ringDimension A R v) (FiniteCode.size (Pair q)) cap
      (FiniteCode.size (Pair q)) (bound v) le_rfl).symm)
    (fun v z => by
      rw [FiniteCode.prod_val,PaddedFlags.count_key _ _ _ _ _ (bound v) (FiniteCode.equiv z.1).isLt (FiniteCode.equiv z.2).isLt.le]
      rfl)
    (fun v z => by
      have hc := (FiniteCode.equiv z.2).isLt.trans_le (bound v)
      have hm := Nat.mul_le_mul_right cap (Nat.succ_le_of_lt (FiniteCode.equiv z.1).isLt)
      nlinarith)
    v (ab,c)
  convert h.symm using 1
  unfold internalKey
  congr 1
  ring

theorem internal_compaction (bound : ∀v,ringDimension A R v≤cap)
    (f : InternalWedgeDescriptors.Field) :
    SelectArray.selectedPrefix (internalRaw A R q cap .keep) (internalRaw A R q cap f)
      (internalRaw A R q cap .keep).length=
      List.ofFn (fun i : Fin (FiniteCode.size (InternalIndex A R q)) =>
        let z := (FiniteCode.equiv (α:=InternalIndex A R q)).symm i
        InternalWedgeDescriptors.value (internalData A R q cap) f (internalKey A R q cap z.1 z.2.1 z.2.2)) := by
  apply FiniteCode.selectedPrefix_eq_ofFn (α:=InternalIndex A R q)
    _ _ _ (fun z => internalKey A R q cap z.1 z.2.1 z.2.2)
    (fun z => InternalWedgeDescriptors.value (internalData A R q cap) f (internalKey A R q cap z.1 z.2.1 z.2.2))
    (internalKeep_binary A R q cap) (internalKeep_total A R q cap bound)
  · intro z
    simpa only [internalRaw,List.length_ofFn] using internalKey_lt A R q cap bound z.1 z.2.1 z.2.2
  · intro z
    rw [internalRaw_read A R q cap bound,internalValue A R q cap bound]
  · intro z
    exact internalKeep_rank A R q cap bound z.1 z.2.1 z.2.2
  · intro z
    exact internalRaw_read A R q cap bound z.1 z.2.1 z.2.2 f

end GroupWL.ConstructiveIncidence
