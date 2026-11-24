import GroupWL.MachinePrograms.TableWLSetup
import GroupWL.MachinePrograms.GroupTupleSemantics

/-! The complete I/II table client, including its exact final semantic decision. -/
namespace GroupWL.MachinePrograms.TableWL
open NatArrayLanguage IndexedRefinement
set_option maxRecDepth 8192
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
variable {G H : Type} [Group G] [Group H] [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H]
variable {n m k : ℕ}

private theorem boolNat_nonzero (flag : Bool) : boolNat flag≠0 ↔ flag=true := by
  cases flag <;> decide

theorem numeric_correct (word : Bool) (e : G≃Fin n) (e' : H≃Fin m) (hn : 0<n) :
    IndexedRefinement.run (IndexedTuples.data n m k hn)
      (matrixWord (relation (k:=k) word e e' (GroupInitial.encodedMul e) (GroupInitial.encodedMul e')))
      ((IndexedTuples.leftSelection n m k).map Fin.val)
      ((IndexedTuples.rightSelection n m k).map Fin.val)=true ↔
      if word then Refinement.EquivalentII k G H else Refinement.EquivalentI k G H := by
  classical
  rw [relation_zero word e e' (GroupInitial.encodedMul e) (GroupInitial.encodedMul e') (IndexedTuples.data n m k hn).edges]
  cases word
  · simp only [initialEq, Bool.false_eq_true, if_false, if_true]
    rw [IndexedRefinement.run_correct _
      (InitialMatrixPrograms.pointSignature (GroupInitial.encodedMul e) (GroupInitial.encodedMul e'))
      (InitialMatrixPrograms.initialEq (GroupInitial.encodedMul e) (GroupInitial.encodedMul e'))
      (InitialMatrixPrograms.initialEq_correct _ _)]
    exact GroupTupleSemantics.original_histograms_correct e e'
  · simp only [initialEq, if_true]
    rw [IndexedRefinement.run_correct _ (WordMatrixSemantics.pointInitial e e')
      (WordMatrixSemantics.initialEq e e') (WordMatrixSemantics.initialEq_correct e e')]
    exact GroupTupleSemantics.word_histograms_correct e e'

theorem decide_runs (word : Bool) (e : G≃Fin n) (e' : H≃Fin m)
    (leftZero : (e 1).val=0) (rightZero : (e' 1).val=0)
    (S : State) (B : ℕ)
    (input : Input (k:=k) (GroupInitial.encodedMul e) (GroupInitial.encodedMul e') B S)
    (matrixRoom : InitialMatrixPrograms.Room n m k B) (productRoom : (max n m)^4≤B)
    (room : IndexedWL.Room (n^k+m^k) k (max n m) B) :
    ∃t≤1000*(B+1)^7,∃T,Runs (storageBound Reg Arr B) (decide word) S t T ∧ T.Bounded B ∧
      (T.scalar (wl .result)≠0 ↔ if word then Refinement.EquivalentII k G H else Refinement.EquivalentI k G H) := by
  obtain ⟨t,ht,U,first,hU,ready,lefts,rights⟩ := setup_runs word e e'
    (GroupInitial.encodedMul e) (GroupInitial.encodedMul e')
    (by intro x y; simp [GroupInitial.encodedMul]) (by intro x y; simp [GroupInitial.encodedMul])
    leftZero rightZero S B input matrixRoom productRoom room
  let D := IndexedTuples.data n m k matrixRoom.left_positive
  have prepared : IndexedWL.Input D (CompressedRefinement.table D.edges
      (initialEq word e e' (GroupInitial.encodedMul e) (GroupInitial.encodedMul e')) 0) B (core U) := by
    simpa only [←relation_zero] using ready
  have lengthsL : (IndexedTuples.leftSelection n m k).length≤B := by
    simp only [IndexedTuples.leftSelection_length]
    exact (Nat.le_add_right _ _).trans ((Nat.le_mul_self _).trans matrixRoom.matrix)
  have lengthsR : (IndexedTuples.rightSelection n m k).length≤B := by
    simp only [IndexedTuples.rightSelection_length]
    exact (Nat.le_add_left _ _).trans ((Nat.le_mul_self _).trans matrixRoom.matrix)
  obtain ⟨u,hu,V,last,hV,result⟩ := IndexedWL.decide_runs D
    (initialEq word e e' (GroupInitial.encodedMul e) (GroupInitial.encodedMul e')) (core U) room prepared
    (IndexedTuples.leftSelection n m k) (IndexedTuples.rightSelection n m k) lefts rights lengthsL lengthsR
  let T := ((U.left.left.left.left.join V).join U.left.left.right).join U.left.right |>.join U.right
  have run := (((last.right_bounded hU.left.left.left).left_bounded hU.left.left).left_bounded hU.left).left_bounded hU
  have run' : Runs (storageBound Reg Arr B) (IndexedWL.decide.map wl array) U u T := by
    simpa only [Program.map_map,Function.comp_def,wl,array,WordMatrixPrograms.wl,WordMatrixPrograms.array] using run
  have hT : T.Bounded B := (((hU.left.left.left.left.join hV).join hU.left.left.right).join hU.left.right).join hU.right
  have budget := hu.trans (IndexedWL.decisionCost_le_common_bound room lengthsL lengthsR)
  have power : (B+1)^4≤(B+1)^7 := pow_le_pow_right' (by omega) (by omega)
  refine ⟨t+u,by nlinarith,T,.seq first run',hT,?_⟩
  change V.scalar .result≠0 ↔ _
  rw [result,boolNat_nonzero,←relation_zero,numeric_correct word e e' matrixRoom.left_positive]

end GroupWL.MachinePrograms.TableWL
