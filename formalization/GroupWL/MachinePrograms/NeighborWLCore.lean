import GroupWL.MachinePrograms.NeighborArrays
import GroupWL.MachinePrograms.IndexedWLCost
import GroupWL.IndexedNeighborSemantics

/-! Complete ordinary-neighbor refinement from a graph table and selected vertices. -/
namespace GroupWL.MachinePrograms.NeighborWLCore
open NatArrayLanguage IndexedRefinement
abbrev Reg := NeighborArrays.Reg ⊕ IndexedWL.Reg
abbrev Arr := NeighborArrays.Arr ⊕ IndexedWL.Arr
abbrev State := Store Reg Arr
abbrev Code := NatArrayLanguage.Program Reg Arr
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

def prepare : List (Atom Reg Arr) := [
  .copy (.inr .n) (.inl (.inl 0)),.copy (.inr .width) (.inl (.inl 0)),
  .const (.inr .arity) 1,.const (.inr .one) 1,
  .binary .mul (.inr .square) (.inr .n) (.inr .n),
  .allocate (.inr .matrix) (.inr .square) (.inr .one),
  .copyArray (.inr .fanouts) (.inl (.inr 0)),.copyArray (.inr .targets) (.inl (.inr 1))]
def decide : Code := .seq (NeighborArrays.generate.map Sum.inl Sum.inl)
  (.seq (atoms prepare) (IndexedWL.decide.map Sum.inr Sum.inr))

theorem initial_word {n : ℕ} (edges : Fin n→Multiset (Fin 1→Fin n)) :
    matrixWord (CompressedRefinement.table edges (fun _ _=>true) 0)=List.replicate (n*n) 1 := by
  simp [matrixWord,CompressedRefinement.table,IndexedRefinement.boolNat,List.ofFn_const]

theorem decide_runs {n : ℕ} (adj : Fin n→Fin n→Bool) (hn : 0<n)
    (S : State) (B : ℕ) (bounded : S.Bounded B) (order : S.scalar (.inl (.inl 0))=n)
    (table : S.array (.inl (.inl ()))=GraphInitial.tableWord adj) (square : n*n≤B)
    (left right : List (Fin n)) (hl : S.array (.inr .leftSelection)=left.map Fin.val)
    (hr : S.array (.inr .rightSelection)=right.map Fin.val) (lenL : left.length≤B) (lenR : right.length≤B) :
    ∃t≤500*(B+1)^7,∃T,Runs (storageBound Reg Arr B) decide S t T ∧ T.Bounded B ∧
      (T.scalar (.inr .result)≠0 ↔ ∀r,
        (left : Multiset _).map (CompressedRefinement.labels (IndexedNeighbors.data hn adj).edges (fun _=>()) r)=
        (right : Multiset _).map (CompressedRefinement.labels (IndexedNeighbors.data hn adj).edges (fun _=>()) r)) := by
  have nB : n≤B := (Nat.le_mul_self _).trans square
  have one : 1≤B := by omega
  obtain ⟨t,ht,U,first,hU,ctx,fanouts,targets⟩ := NeighborArrays.generate_runs adj hn S.left B bounded.left ⟨order,table⟩ square
  let A := U.join S.right
  have first' := first.left_bounded bounded
  have hA : A.Bounded B := hU.join bounded.right
  have valid : ValidAtoms B prepare A := by
    simp [prepare,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar,A,ctx.order_eq,one,square]
  obtain ⟨middle,hV⟩ := atoms_runs hA prepare valid
  let V := applyAtoms prepare A
  let D := IndexedNeighbors.data hn adj
  have room : IndexedWL.Room n 1 n B := ⟨square,by simpa using square,square,one,nB,one,by simpa using nB⟩
  have ready : IndexedWL.Input D (CompressedRefinement.table D.edges (fun _ _=>true) 0) B V.right := by
    refine ⟨hV.right,?_,?_,?_,?_,?_,?_⟩
    · simp [V,A,applyAtoms,prepare,Atom.apply,Store.right,Store.setScalar,Store.setArray,ctx.order_eq]
    · simp [V,A,applyAtoms,prepare,Atom.apply,Store.right,Store.setScalar,Store.setArray]
    · simp [V,A,applyAtoms,prepare,Atom.apply,Store.right,Store.setScalar,Store.setArray,ctx.order_eq]
    · simp [V,A,applyAtoms,prepare,Atom.apply,BinaryOp.eval,Store.right,Store.setScalar,Store.setArray,ctx.order_eq,initial_word]
    · simp [V,A,applyAtoms,prepare,Atom.apply,Store.right,Store.setScalar,Store.setArray,fanouts,D]
    · simp [V,A,applyAtoms,prepare,Atom.apply,Store.right,Store.setScalar,Store.setArray,targets,D]
  have vl : V.right.array .leftSelection=left.map Fin.val := by
    simpa [V,A,applyAtoms,prepare,Atom.apply,Store.right,Store.setScalar,Store.setArray] using hl
  have vr : V.right.array .rightSelection=right.map Fin.val := by
    simpa [V,A,applyAtoms,prepare,Atom.apply,Store.right,Store.setScalar,Store.setArray] using hr
  obtain ⟨u,hu,W,last,hW,correct⟩ := IndexedWL.decide_runs_correct D (fun _=>()) (fun _ _=>true)
    (by intros; simp) V.right room ready left right vl vr lenL lenR
  have budget := hu.trans (IndexedWL.decisionCost_le_common_bound room lenL lenR)
  have power : (n+1)^3≤(B+1)^7 := (Nat.pow_le_pow_left (by omega : n+1≤B+1) 3).trans (pow_le_pow_right' (by omega) (by omega))
  have pos : 1≤(B+1)^7 := one_le_pow₀ (by omega)
  exact ⟨t+(8+u),by nlinarith,V.left.join W,.seq first' (.seq middle (last.right_bounded hV)),hV.left.join hW,correct⟩


theorem gadget_decide_runs {G H : Type} [Group G] [Group H] [Fintype G] [Fintype H]
    [DecidableEq G] [DecidableEq H] {n m : ℕ} (e : G≃Fin n) (e' : H≃Fin m)
    (S : State) (B : ℕ) (bounded : S.Bounded B)
    (order : S.scalar (.inl (.inl 0))=IndexedGadget.size n+IndexedGadget.size m)
    (table : S.array (.inl (.inl ()))=GraphInitial.tableWord (IndexedNeighbors.unionNumericAdj e e'))
    (square : (IndexedGadget.size n+IndexedGadget.size m)^2≤B)
    (hl : S.array (.inr .leftSelection)=(IndexedNeighbors.leftVertexSelection n m).map Fin.val)
    (hr : S.array (.inr .rightSelection)=(IndexedNeighbors.rightVertexSelection n m).map Fin.val)
    (lenL : n≤B) (lenR : m≤B) :
    ∃t≤500*(B+1)^7,∃T,Runs (storageBound Reg Arr B) decide S t T ∧ T.Bounded B ∧
      (T.scalar (.inr .result)≠0 ↔ Refinement.EquivalentIII 1 G H) := by
  have hn : 0<IndexedGadget.size n+IndexedGadget.size m := by
    have := (e 1).isLt
    unfold IndexedGadget.size
    omega
  obtain ⟨t,ht,T,run,hT,result⟩ := decide_runs (IndexedNeighbors.unionNumericAdj e e') hn S B bounded order table
    (by simpa only [pow_two] using square) (IndexedNeighbors.leftVertexSelection n m)
    (IndexedNeighbors.rightVertexSelection n m) hl hr
    (by simpa [IndexedNeighbors.leftVertexSelection] using lenL)
    (by simpa [IndexedNeighbors.rightVertexSelection] using lenR)
  refine ⟨t,ht,T,run,hT,?_⟩
  rw [result]
  simpa only [IndexedNeighbors.neighborData,Refinement.EquivalentIII,if_pos rfl] using
    IndexedNeighbors.neighbor_histograms_correct e e'

end GroupWL.MachinePrograms.NeighborWLCore
