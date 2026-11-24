import GroupWL.ConstructiveInputEncoding
import GroupWL.FramePairEncoding

/-! Arithmetic offsets of internal and incidence output coordinates. -/
namespace GroupWL.ConstructiveIncidence
open IncidenceTensor ConstructiveCoordinates
variable {F I J : Type} [Field F] [DecidableEq F]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [FiniteCode I] [FiniteCode J]
variable {V : J → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module F (V j)]
variable (A : AffineSystem F I J V) (R : ∀ j, Coordinates F (ReadoutRadical A j)) (q : ℕ)

def internalOffset (v : I⊕J) := inputOffset A R (FiniteCode.size (Pair q)) v
def internalTotal := inputTotal A R (FiniteCode.size (Pair q))
def oldOutputTotal := internalTotal A R q+FiniteCode.size (Incidence A)*q*q*2

theorem internalTotal_eq : internalTotal A R q=
    FiniteCode.size (Σ v : I⊕J,Pair q×Option (RadicalIndex A R v)) :=
  inputTotal_eq A R (FiniteCode.size (Pair q))

theorem internalIndex_val (v : I⊕J) (ab : Pair q) (c : Option (RadicalIndex A R v)) :
    (FiniteCode.equiv (α:=OldOutputIndex A R q) (.inl ⟨v,(ab,c)⟩)).val=
      internalOffset A R q v+(FiniteCode.equiv ab).val*ringDimension A R v+(FiniteCode.equiv c).val := by
  rw [FiniteCode.sum_inl_val,FiniteCode.sigma_val,FiniteCode.prod_val]
  have h := inputIndex_val A R (FiniteCode.size (Pair q)) v (FiniteCode.equiv ab) c
  rw [FiniteCode.sigma_val,FiniteCode.prod_val,FiniteCode.fin_val] at h
  exact h

theorem edgeIndex_val (e : Incidence A) (a b : Fin q) (c : Option PUnit) :
    (FiniteCode.equiv (α:=OldOutputIndex A R q) (.inr (e,(a,b),c))).val=
      internalTotal A R q+((FiniteCode.equiv e).val*q*q+a.val*q+b.val)*2+(FiniteCode.equiv c).val := by
  rw [FiniteCode.sum_inr_val,←internalTotal_eq]
  simp only [FiniteCode.prod_val,FiniteCode.fin_val]
  change internalTotal A R q+((FiniteCode.equiv e).val*(q*q*2)+((a.val*q+b.val)*2+(FiniteCode.equiv c).val))=_
  ring

theorem oldOutputTotal_eq : oldOutputTotal A R q=FiniteCode.size (OldOutputIndex A R q) := by
  unfold oldOutputTotal
  rw [internalTotal_eq]
  change _+FiniteCode.size (Incidence A)*q*q*2=_+FiniteCode.size (Incidence A)*(q*q*2)
  congr 1
  ring

theorem paddedInput_size : FiniteCode.size (InputIndex A R q)=inputTotal A R q+oldOutputTotal A R q := by
  rw [inputTotal_eq,oldOutputTotal_eq]
  rfl

theorem paddedOutput_size : FiniteCode.size (OutputIndex A R q)=oldOutputTotal A R q+
    (inputTotal A R q+oldOutputTotal A R q) := by
  rw [inputTotal_eq,oldOutputTotal_eq]
  rfl

end GroupWL.ConstructiveIncidence
