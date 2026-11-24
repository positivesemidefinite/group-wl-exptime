import GroupWL.MachinePrograms.InitialMatrixSemantics
import GroupWL.MachinePrograms.WordTypeComparator

/-! Numeric tuple indices retain the complete word type used by Version II. -/
namespace GroupWL.MachinePrograms.WordMatrixSemantics
open InitialMatrixPrograms

variable (G H : Type)
def Select (second : Bool) : Type := if second then H else G
instance (priority := low) [Group G] [Group H] (second : Bool) : Group (Select G H second) := by
  cases second <;> assumption
instance (priority := low) [Fintype G] [Fintype H] (second : Bool) : Fintype (Select G H second) := by
  cases second <;> assumption
instance (priority := low) [DecidableEq G] [DecidableEq H] (second : Bool) : DecidableEq (Select G H second) := by
  cases second <;> assumption

variable {G H} {n m k : ℕ}
def selectEquiv (e : G≃Fin n) (e' : H≃Fin m) (second : Bool) :
    Select G H second ≃ Fin (selectBase n m second) := by cases second;exact e;exact e'

def pointTuple (e : G≃Fin n) (e' : H≃Fin m) (i : Fin (n^k+m^k)) :
    Fin k→Select G H (decide (n^k ≤ i.val)) :=
  (selectEquiv e e' (decide (n^k ≤ i.val))).symm ∘ finFunctionFinEquiv.symm (pointCode i)

noncomputable def pointInitial [Group G] [Group H] (e : G≃Fin n) (e' : H≃Fin m)
    (i : Fin (n^k+m^k)) : Refinement.GroupWord k → Bool := Refinement.initialII k (pointTuple e e' i)

def initialEq [Group G] [Group H] [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H]
    (e : G≃Fin n) (e' : H≃Fin m) (i j : Fin (n^k+m^k)) : Bool :=
  FiniteWordTypes.sameWordType (pointTuple e e' i) (pointTuple e e' j)

theorem initialEq_correct [Group G] [Group H] [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H]
    (e : G≃Fin n) (e' : H≃Fin m) (i j : Fin (n^k+m^k)) :
    initialEq e e' i j=true ↔ pointInitial e e' i=pointInitial e e' j :=
  FiniteWordTypes.sameWordType_correct _ _

def indexEquiv (e : G≃Fin n) (e' : H≃Fin m) : FiniteWL.Index G H k≃Fin (n^k+m^k) :=
  (Equiv.sumCongr (Equiv.arrowCongr (Equiv.refl (Fin k)) e)
    (Equiv.arrowCongr (Equiv.refl (Fin k)) e')).trans (IndexedTuples.enumeration n m k)

theorem pointInitial_left [Group G] [Group H] (e : G≃Fin n) (e' : H≃Fin m) (a : Fin k→G) :
    pointInitial e e' (indexEquiv e e' (.inl a))=Refinement.initialII k a := by
  have index : (indexEquiv e e' (.inl a)).val=(finFunctionFinEquiv (e ∘ a)).val := rfl
  have hd : decide (n^k ≤ (indexEquiv e e' (.inl a)).val)=false := by
    rw [index]
    exact decide_eq_false (Nat.not_le_of_lt (finFunctionFinEquiv (e ∘ a)).isLt)
  unfold pointInitial pointTuple pointCode
  generalize_proofs bound
  generalize hb : decide (n^k ≤ (indexEquiv e e' (.inl a)).val)=b at bound ⊢
  rw [hd] at hb
  cases hb
  simp only [selectEquiv,selectBase,selectCode,Bool.false_eq_true,if_false,index]
  change Refinement.initialII k (e.symm ∘ finFunctionFinEquiv.symm (finFunctionFinEquiv (e ∘ a)))=_
  rw [Equiv.symm_apply_apply]
  congr 1
  funext i
  simp

theorem pointInitial_right [Group G] [Group H] (e : G≃Fin n) (e' : H≃Fin m) (a : Fin k→H) :
    pointInitial e e' (indexEquiv e e' (.inr a))=Refinement.initialII k a := by
  have index : (indexEquiv e e' (.inr a)).val=n^k+(finFunctionFinEquiv (e' ∘ a)).val := rfl
  have hd : decide (n^k ≤ (indexEquiv e e' (.inr a)).val)=true := by rw [index];simp
  unfold pointInitial pointTuple pointCode
  generalize_proofs bound
  generalize hb : decide (n^k ≤ (indexEquiv e e' (.inr a)).val)=b at bound ⊢
  rw [hd] at hb
  cases hb
  simp only [selectEquiv,selectBase,selectCode,if_true,index,Nat.add_sub_cancel_left]
  change Refinement.initialII k (e'.symm ∘ finFunctionFinEquiv.symm (finFunctionFinEquiv (e' ∘ a)))=_
  rw [Equiv.symm_apply_apply]
  congr 1
  funext i
  simp

theorem pointInitial_enumeration [Group G] [Group H] (e : G≃Fin n) (e' : H≃Fin m)
    (a : FiniteWL.Index G H k) : pointInitial e e' (indexEquiv e e' a)=
      FiniteWL.initial (Refinement.initialII k) (Refinement.initialII k) a := by
  cases a with
  | inl a =>exact pointInitial_left e e' a
  | inr a =>exact pointInitial_right e e' a

end GroupWL.MachinePrograms.WordMatrixSemantics
