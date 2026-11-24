import GroupWL.MachinePrograms.RadixSelection
import GroupWL.IndexedGadgetSelections
import GroupWL.IndexedNeighborSemantics

/-! Materialize both group-only tuple selections inside the multiplication gadgets. -/
namespace GroupWL.MachinePrograms.GadgetSelectionBuilder
open NatArrayLanguage
abbrev Reg := RadixSelection.Reg ⊕ Fin 3
abbrev Arr := RadixSelection.Arr ⊕ Unit
abbrev Code := NatArrayLanguage.Program Reg Arr
set_option maxRecDepth 4096

def between : List (Atom Reg Arr) := [
  .copyArray (.inr ()) (.inl (.inr ())),.copy (.inl (.inl 0)) (.inr 0),
  .copy (.inl (.inl 1)) (.inr 1),.copy (.inl (.inr 1)) (.inr 2)]
def generate : Code := .seq (RadixSelection.generate.map Sum.inl Sum.inl)
  (.seq (atoms between) (RadixSelection.generate.map Sum.inl Sum.inl))

theorem generate_runs (n m k : ℕ) (hn : 0<n) (hm : 0<m)
    (S : Store Reg Arr) (B : ℕ) (bounded : S.Bounded B)
    (left : RadixSelection.Context n (IndexedGadget.size n) k 0 S.left)
    (right : S.scalar (.inr 0)=m) (rightSize : S.scalar (.inr 1)=IndexedGadget.size m)
    (offset : S.scalar (.inr 2)=(IndexedGadget.size n)^k)
    (room : (IndexedGadget.size n)^k+(IndexedGadget.size m)^k≤B) :
    ∃t≤(n^k+m^k)*(7*k+11)+6*k+28,∃T,Runs (storageBound Reg Arr B) generate S t T ∧
      T.Bounded B ∧ T.array (.inr ())=(IndexedGadget.leftGroupSelection n m k).map Fin.val ∧
      T.array (.inl (.inr ()))=(IndexedGadget.rightGroupSelection n m k).map Fin.val := by
  obtain ⟨t,ht,U,first,hU,ctx,wordU⟩ := RadixSelection.generate_runs n (IndexedGadget.size n) k 0 hn
    (Nat.le_add_right _ _) S.left B bounded.left left (by omega)
  let A := U.join S.right
  have first' := first.left_bounded bounded
  have hA : A.Bounded B := hU.join bounded.right
  obtain ⟨middle,hV⟩ := atoms_runs hA between (by simp [between,ValidAtoms,Atom.Valid,Atom.SmallResult])
  let V := applyAtoms between A
  have context : RadixSelection.Context m (IndexedGadget.size m) k ((IndexedGadget.size n)^k) V.left := by
    refine ⟨?_,?_,?_,?_⟩
    · simpa [V,A,applyAtoms,between,Atom.apply,Store.left,Store.right,Store.setScalar,Store.setArray] using right
    · simpa [V,A,applyAtoms,between,Atom.apply,Store.left,Store.right,Store.setScalar,Store.setArray] using rightSize
    · simpa [V,A,applyAtoms,between,Atom.apply,Store.left,Store.right,Store.setScalar,Store.setArray] using ctx.width_eq
    · simpa [V,A,applyAtoms,between,Atom.apply,Store.left,Store.right,Store.setScalar,Store.setArray] using offset
  have saved : V.right.array ()=RadixSelection.word n (IndexedGadget.size n) k 0 := by
    simp [V,A,applyAtoms,between,Atom.apply,Store.left,Store.right,Store.setScalar,Store.setArray,wordU]
  obtain ⟨u,hu,W,last,hW,_,wordW⟩ := RadixSelection.generate_runs m (IndexedGadget.size m) k ((IndexedGadget.size n)^k) hm
    (Nat.le_add_right _ _) V.left B hV.left context room
  refine ⟨t+(4+u),by nlinarith,W.join V.right,.seq first' (.seq middle (last.left_bounded hV)),hW.join hV.right,?_,?_⟩
  · rw [IndexedGadget.leftGroupSelection_word n m k hn]
    exact saved
  · rw [IndexedGadget.rightGroupSelection_word n m k hm]
    exact wordW


theorem radix_word_one (n N offset : ℕ) :
    RadixSelection.word n N 1 offset=NatArrayRange.word n offset := by
  simp only [RadixSelection.word,NatArrayRange.word,pow_one]
  apply congrArg List.ofFn
  funext i
  simp [NatArrayRadix.recode,Nat.mod_eq_of_lt i.isLt]

theorem left_word_one (n m : ℕ) (hn : 0<n) :
    (IndexedGadget.leftGroupSelection n m 1).map Fin.val=
      (IndexedNeighbors.leftVertexSelection n m).map Fin.val := by
  rw [IndexedGadget.leftGroupSelection_word n m 1 hn,radix_word_one,IndexedNeighbors.leftVertexSelection_word]

theorem right_word_one (n m : ℕ) (hm : 0<m) :
    (IndexedGadget.rightGroupSelection n m 1).map Fin.val=
      (IndexedNeighbors.rightVertexSelection n m).map Fin.val := by
  rw [IndexedGadget.rightGroupSelection_word n m 1 hm,radix_word_one,IndexedNeighbors.rightVertexSelection_word,pow_one]

end GroupWL.MachinePrograms.GadgetSelectionBuilder
