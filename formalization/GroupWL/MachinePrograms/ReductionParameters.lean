import GroupWL.MachinePrograms.NatArrayProofs
import GroupWL.CircuitReductionWords

namespace GroupWL.MachinePrograms.ReductionParameters
open NatArrayLanguage Refinement
inductive Reg where | arity | wire | frame | dimension | tmp | extra
  deriving Fintype, DecidableEq

abbrev State := Store Reg Empty
open Reg

def instructions (v : Version) : List (Atom Reg Empty) :=
  [.const .tmp 4, .binary .mul .wire .arity .tmp, .const .tmp 3, .binary .add .wire .wire .tmp,
   .const .tmp 100, .binary .add .frame .arity .tmp, .const .tmp 1,
   .binary .add .dimension .arity .tmp, .binary .mul .dimension .frame .dimension,
   .const .tmp 40, .binary .add .dimension .dimension .tmp] ++
  match v with
  | .one => [.const .tmp 6, .binary .add .dimension .dimension .tmp]
  | .two => []
  | .three => [.const .tmp 1, .binary .add .dimension .dimension .tmp, .const .tmp 2,
    .divmod .dimension .extra .dimension .tmp, .binary .add .dimension .dimension .tmp]

def program (v : Version) : Program Reg Empty := atoms (instructions v)

theorem run (v : Version) (n m : ℕ) (S : State) (hS : S.Bounded m)
    (hr : S.scalar .arity=n+3) (room : 146*(n+3+1)^2≤m) :
    ∃ t ≤ 16, ∃ U, Runs (storageBound Reg Empty m) (program v) S t U ∧
      U.Bounded m ∧ U.scalar .wire = CircuitGroupReduction.wireLength n ∧
      U.scalar .frame = Parameters.frameWidth (n+3) ∧
      U.scalar .dimension = CircuitGroupReduction.dimension v (n+3) := by
  have bounds : 100≤m ∧ (n+3)*4+3≤m ∧ n+3+100≤m ∧ n+3+1≤m ∧
      (n+3+100)*(n+3+1)+46≤m := by
    refine ⟨?_,?_,?_,?_,?_⟩ <;> nlinarith [Nat.zero_le (n*n)]
  have divBound : ((n+3+100)*(n+3+1)+40+1)/2 ≤ (n+3+100)*(n+3+1)+41 :=
    Nat.div_le_self _ _
  have valid : ValidAtoms m (instructions v) S := by
    cases v <;> simp [instructions,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,
      BinaryOp.eval,Store.setScalar,Function.update,hr] <;> omega
  obtain ⟨run,bound⟩ := atoms_runs hS _ valid
  refine ⟨_,by cases v <;> decide,_,run,bound,?_⟩
  cases v <;> simp [instructions,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Function.update,
    hr,CircuitGroupReduction.wireLength,CircuitGroupReduction.dimension,Parameters.dimensionI,
    Parameters.dimensionII,Parameters.dimensionIII,Parameters.ringBudget,Parameters.frameWidth,
    Parameters.blockBudget] <;> omega
end GroupWL.MachinePrograms.ReductionParameters
