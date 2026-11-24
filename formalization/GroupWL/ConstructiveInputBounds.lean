import GroupWL.InternalWedgeEncoding

/-! The generated input segments lie within the total input coordinate range. -/
namespace GroupWL.ConstructiveIncidence
open IncidenceTensor ConstructiveCoordinates MachinePrograms
variable {F I J : Type} [Field F] [DecidableEq F]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [FiniteCode I] [FiniteCode J]
variable {V : J → Type} [∀j,AddCommGroup (V j)] [∀j,Module F (V j)]
variable (A : AffineSystem F I J V) (R : ∀j,Coordinates F (ReadoutRadical A j)) (q : ℕ)

theorem inputOffset_segment_le_total (v : I⊕J) :
    inputOffset A R q v+q*ringDimension A R v ≤ inputTotal A R q := by
  have h := FilterRanks.count_mono (inputSizes A R q) (show (FiniteCode.equiv v).val+1 ≤ FiniteCode.size (I⊕J) by
    exact (FiniteCode.equiv v).isLt)
  simpa [inputOffset,inputTotal,FilterRanks.count,inputSizes,(FiniteCode.equiv v).isLt] using h

theorem inputOffset_le_total (v : I⊕J) : inputOffset A R q v ≤ inputTotal A R q :=
  (Nat.le_add_right _ _).trans (inputOffset_segment_le_total A R q v)

theorem internalData_valid (cap M : ℕ) (hq : 2 ≤ q) (hcap : 0<cap) (room : 1 ≤ M)
    (dims : ∀v,ringDimension A R v ≤ cap) (size : inputTotal A R q+(q+1)*cap ≤ M) :
    InternalWedgeDescriptors.Valid (internalData A R q cap) M := by
  let ab : Pair q := ⟨(⟨0,by omega⟩,⟨1,by omega⟩),by change (0 : ℕ) < 1; omega⟩
  have hpairs : 0<FiniteCode.size (Pair q) := by have := (FiniteCode.equiv ab).isLt; omega
  refine ⟨by simpa [internalData] using (show 0<q by omega),hcap,hpairs,
    ?_,?_,?_,?_,?_,?_,room⟩
  · simp [internalData,ringDimensions]
  · simp [internalData,inputOffsets]
  · simp [internalData,FramePairEncoding.word]
  · intro i hi
    let v : I⊕J := FiniteCode.equiv.symm ⟨i,hi⟩
    have vi : (FiniteCode.equiv v).val=i := by simp [v]
    change (ringDimensions A R)[i]?.getD 0 ≤ cap
    rw [←vi,ringDimensions_read]
    exact dims v
  · intro i hi
    let v : I⊕J := FiniteCode.equiv.symm ⟨i,hi⟩
    have vi : (FiniteCode.equiv v).val=i := by simp [v]
    change (inputOffsets A R q)[i]?.getD 0+q*cap+cap ≤ M
    rw [←vi,inputOffsets_read]
    have hv := inputOffset_le_total A R q v
    nlinarith
  · intro i hi
    let b : Pair q := FiniteCode.equiv.symm ⟨i,hi⟩
    have bi : (FiniteCode.equiv b).val=i := by simp [b]
    change (FramePairEncoding.word q)[i]?.getD 0<q*q
    rw [←bi,FramePairEncoding.word_read]
    have ha := b.val.1.isLt
    have hb := b.val.2.isLt
    have hm := Nat.mul_le_mul_right q (show b.val.1.val+1 ≤ q by omega)
    nlinarith

end GroupWL.ConstructiveIncidence
