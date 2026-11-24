import GroupWL.MachinePrograms.TensorGroupMaterialize
import GroupWL.MachinePrograms.GroupInitial

/-! The operational table matches the table interface used by the WL programs. -/
namespace GroupWL.MachinePrograms.TensorGroupProgram
open NatArrayLanguage
open TensorGroupCode

variable (p : ℕ) [Fact p.Prime]

def codedMul (T : Statement.TensorDescription p)
    (g h : Fin (p^(T.inputDimension+T.outputDimension))) : Fin (p^(T.inputDimension+T.outputDimension)) :=
  groupEquiv p T ((groupEquiv p T).symm g*(groupEquiv p T).symm h)

theorem tableWord_correct (T : Statement.TensorDescription p) :
    tableWord (TensorSerialization.coefficientList (T.coefficient p)) p T.inputDimension T.outputDimension
      ((2:ZMod p)⁻¹).val=GroupInitial.tableWord (codedMul p T) := by
  unfold tableWord GroupInitial.tableWord
  simp only [pow_two]
  congr 1
  funext i
  exact multiplication_correct p T (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

theorem materialize_tensor_runs (S : State) (M : ℕ) (T : Statement.TensorDescription p)
    (bounded : S.Bounded M) (modulus : S.scalar (l .modulus)=p)
    (inputDimension : S.scalar (l .inputDimension)=T.inputDimension)
    (outputDimension : S.scalar (l .outputDimension)=T.outputDimension)
    (coefficients : S.array (.inl .coefficients)=TensorSerialization.coefficientList (T.coefficient p))
    (room : p^3+3*p≤M) (dimension : T.inputDimension+T.outputDimension≤M)
    (power : (p^(T.inputDimension+T.outputDimension))^2≤M) :
    ∃t≤tableCost p T.inputDimension T.outputDimension,∃U,
      Runs (storageBound Reg Arr M) (materialize ((2:ZMod p)⁻¹).val) S t U ∧ U.Bounded M ∧
      U.scalar (a .order)=p^(T.inputDimension+T.outputDimension) ∧
      U.array (.inr ())=GroupInitial.tableWord (codedMul p T) := by
  have hp : 0<p := (Fact.out : p.Prime).pos
  obtain ⟨t,ht,U,run,hU,order,table⟩ := materialize_runs S M ((2:ZMod p)⁻¹).val bounded
    (by omega) (by simpa only [modulus] using room)
    (by simpa only [coefficients,inputDimension,outputDimension] using BilinearEvaluation.coefficientList_length p (T.coefficient p))
    (by simpa only [coefficients,modulus] using BilinearEvaluation.coefficientList_lt p (T.coefficient p))
    (by rw [modulus];exact ZMod.val_lt _) (by omega)
    (by simpa only [modulus,inputDimension,outputDimension] using power)
  refine ⟨t,by simpa only [modulus,inputDimension,outputDimension] using ht,U,run,hU,?_,?_⟩
  · simpa only [modulus,inputDimension,outputDimension] using order
  · simpa only [coefficients,modulus,inputDimension,outputDimension,tableWord_correct] using table

end GroupWL.MachinePrograms.TensorGroupProgram
