import GroupWL.MachinePrograms.GraphWLCoreSetup
import GroupWL.MachinePrograms.GraphGadgetSemantics

/-! The full selected-tuple graph client, specialized to the manuscript's multiplication gadgets. -/
namespace GroupWL.MachinePrograms.GraphWLCore
open NatArrayLanguage IndexedRefinement
set_option maxRecDepth 8192
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
variable {n m k : ℕ}

theorem decide_runs (f : Fin n→Fin n→Bool) (g : Fin m→Fin m→Bool)
    (S : State) (B : ℕ) (input : Input (k:=k) f g B S)
    (matrixRoom : GraphMatrixPrograms.Room n m k B)
    (room : IndexedWL.Room (n^k+m^k) k (max n m) B)
    (left right : List (Fin (n^k+m^k)))
    (hl : S.array (array .leftSelection)=left.map Fin.val)
    (hr : S.array (array .rightSelection)=right.map Fin.val)
    (lengthL : left.length≤B) (lengthR : right.length≤B) :
    ∃t≤1000*(B+1)^7,∃T,Runs (storageBound Reg Arr B) decide S t T ∧ T.Bounded B ∧
      (T.scalar (wl .result)≠0 ↔ ∀r,
        (left : Multiset _).map (CompressedRefinement.labels (IndexedTuples.data n m k matrixRoom.left_positive).edges
          (GraphMatrixPrograms.pointSignature f g) r)=
        (right : Multiset _).map (CompressedRefinement.labels (IndexedTuples.data n m k matrixRoom.left_positive).edges
          (GraphMatrixPrograms.pointSignature f g) r)) := by
  obtain ⟨t,ht,U,first,hU,ready,lefts,rights⟩ := setup_runs f g S B input matrixRoom room
  let D := IndexedTuples.data n m k matrixRoom.left_positive
  have prepared : IndexedWL.Input D (CompressedRefinement.table D.edges (GraphMatrixPrograms.initialEq f g) 0) B (core U) := ready
  obtain ⟨u,hu,V,last,hV,correct⟩ := IndexedWL.decide_runs_correct D (GraphMatrixPrograms.pointSignature f g)
    (GraphMatrixPrograms.initialEq f g) (GraphMatrixPrograms.initialEq_correct f g) (core U) room prepared left right
    (lefts.trans hl) (rights.trans hr) lengthL lengthR
  let T := ((U.left.left.left.join V).join U.left.right).join U.right
  have run := ((last.right_bounded hU.left.left).left_bounded hU.left).left_bounded hU
  have run' : Runs (storageBound Reg Arr B) (IndexedWL.decide.map wl array) U u T := by
    simpa only [NatArrayLanguage.Program.map_map,Function.comp_def,wl,array] using run
  have hT : T.Bounded B := ((hU.left.left.left.join hV).join hU.left.right).join hU.right
  have budget := hu.trans (IndexedWL.decisionCost_le_common_bound room lengthL lengthR)
  have power : (B+1)^4≤(B+1)^7 := pow_le_pow_right' (by omega) (by omega)
  exact ⟨t+u,by nlinarith,T,.seq first run',hT,correct⟩

variable {G H : Type} [Group G] [Group H] [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H]

theorem gadget_decide_runs (e : G≃Fin n) (e' : H≃Fin m) (hk : k≠1)
    (S : State) (B : ℕ)
    (input : Input (k:=k) (IndexedGadget.numericAdj (GroupInitial.encodedMul e))
      (IndexedGadget.numericAdj (GroupInitial.encodedMul e')) B S)
    (matrixRoom : GraphMatrixPrograms.Room (IndexedGadget.size n) (IndexedGadget.size m) k B)
    (room : IndexedWL.Room ((IndexedGadget.size n)^k+(IndexedGadget.size m)^k) k
      (max (IndexedGadget.size n) (IndexedGadget.size m)) B)
    (hl : S.array (array .leftSelection)=(IndexedGadget.leftGroupSelection n m k).map Fin.val)
    (hr : S.array (array .rightSelection)=(IndexedGadget.rightGroupSelection n m k).map Fin.val)
    (lengthL : n^k≤B) (lengthR : m^k≤B) :
    ∃t≤1000*(B+1)^7,∃T,Runs (storageBound Reg Arr B) decide S t T ∧ T.Bounded B ∧
      (T.scalar (wl .result)≠0 ↔ Refinement.EquivalentIII k G H) := by
  obtain ⟨t,ht,T,run,hT,result⟩ := decide_runs _ _ S B input matrixRoom room
    (IndexedGadget.leftGroupSelection n m k) (IndexedGadget.rightGroupSelection n m k) hl hr
    (by simpa using lengthL) (by simpa using lengthR)
  refine ⟨t,ht,T,run,hT,?_⟩
  rw [result,GraphMatrixPrograms.gadget_histograms_correct e e',Refinement.EquivalentIII,if_neg hk]

end GroupWL.MachinePrograms.GraphWLCore
