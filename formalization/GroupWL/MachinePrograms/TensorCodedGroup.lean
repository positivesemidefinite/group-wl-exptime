import GroupWL.MachinePrograms.TensorGroupInterface
import Mathlib.Algebra.Group.TransferInstance

/-! The finite indexed carrier and its multiplication-preserving equivalence. -/
namespace GroupWL.MachinePrograms.TensorGroupProgram
open TensorGroupCode

variable (p : ℕ) [Fact p.Prime]

def CodedCarrier (T : Statement.TensorDescription p) := Fin (p^(T.inputDimension+T.outputDimension))

instance codedFintype (T : Statement.TensorDescription p) : Fintype (CodedCarrier p T) :=
  inferInstanceAs (Fintype (Fin _))
instance codedDecidableEq (T : Statement.TensorDescription p) : DecidableEq (CodedCarrier p T) :=
  inferInstanceAs (DecidableEq (Fin _))
instance codedGroup (T : Statement.TensorDescription p) : Group (CodedCarrier p T) :=
  (groupEquiv p T).symm.group

def codedEquiv (T : Statement.TensorDescription p) : T.Carrier ≃* CodedCarrier p T :=
  { groupEquiv p T with
    map_mul' := by
      intro x y
      change groupEquiv p T (x*y)=groupEquiv p T
        ((groupEquiv p T).symm (groupEquiv p T x)*(groupEquiv p T).symm (groupEquiv p T y))
      simp }

theorem coded_mul (T : Statement.TensorDescription p) (x y : CodedCarrier p T) :
    x*y=codedMul p T x y := rfl

theorem codedEquiv_one_val (T : Statement.TensorDescription p) :
    ((codedEquiv p T) 1).val=0 := by
  change (groupEquiv p T 1).val=0
  rw [groupEquiv_val]
  apply Finset.sum_eq_zero
  intro i hi
  induction i using Fin.addCases with
  | left i => simp
  | right i => simp

theorem coded_one_val (T : Statement.TensorDescription p) :
    (1 : CodedCarrier p T).val=0 := codedEquiv_one_val p T

end GroupWL.MachinePrograms.TensorGroupProgram
