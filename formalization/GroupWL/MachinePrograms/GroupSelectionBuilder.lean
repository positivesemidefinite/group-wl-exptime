import GroupWL.IndexedTupleEdges
import GroupWL.MachinePrograms.NatArrayComponents

/-! Construct both disjoint tuple selections by counted interval loops. -/
namespace GroupWL.MachinePrograms.GroupSelectionBuilder
open NatArrayLanguage
abbrev Reg := NatArrayRange.Reg ⊕ Unit
abbrev Arr := Unit ⊕ Unit
abbrev Code := Program Reg Arr

def between : List (Atom Reg Arr) := [
  .copyArray (.inr ()) (.inl ()),.copy (.inl 1) (.inl 0),.copy (.inl 0) (.inr ())]
def generate : Code := .seq (NatArrayRange.generate.map Sum.inl Sum.inl)
  (.seq (atoms between) (NatArrayRange.generate.map Sum.inl Sum.inl))

theorem generate_ranges (S : Store Reg Arr) (B l r : ℕ) (hS : S.Bounded B)
    (hl : S.scalar (.inl 0)=l) (hr : S.scalar (.inr ())=r) (hoff : S.scalar (.inl 1)=0)
    (hroom : l+r≤B) (h1 : 1≤B) :
    ∃ t≤5*(l+r)+15,∃ T,Runs (storageBound Reg Arr B) generate S t T ∧ T.Bounded B ∧
      T.array (.inr ())=NatArrayRange.word l 0 ∧ T.array (.inl ())=NatArrayRange.word r l := by
  obtain ⟨t,ht,U,first,hU,hleft⟩ := NatArrayRange.generate_runs S.left B l 0 hS.left hl hoff (by omega) h1
  let A := U.join S.right
  have first' : Runs (storageBound Reg Arr B) (NatArrayRange.generate.map Sum.inl Sum.inl) S t A :=
    first.left_bounded hS
  have hA : A.Bounded B := hU.join hS.right
  have ulen : U.scalar 0=l := by
    rw [first.scalar_eq_of_not_mem 0 (by
      simp [NatArrayRange.generate,NatArrayRange.prelude,NatArrayRange.fill,NatArrayRange.body,
        NatArrayRange.bodyAtoms,countedLoop,atoms,NatArrayLanguage.sequence,Program.scalarWrites,Atom.scalarWrites])]
    exact hl
  have valid : ValidAtoms B between A := by simp [between,ValidAtoms,Atom.Valid,Atom.SmallResult]
  obtain ⟨middle,hV⟩ := atoms_runs hA between valid
  let V := applyAtoms between A
  have vn : V.left.scalar 0=r := by
    simp [V,applyAtoms,between,Atom.apply,Store.left,Store.setScalar,A,Store.right,hr]
  have vo : V.left.scalar 1=l := by
    simp [V,applyAtoms,between,Atom.apply,Store.left,Store.setScalar,A,ulen]
  have vsaved : V.right.array ()=NatArrayRange.word l 0 := by
    simp [V,applyAtoms,between,Atom.apply,Store.right,Store.setArray,A,hleft]
  obtain ⟨u,hu,W,last,hW,hright⟩ := NatArrayRange.generate_runs V.left B r l hV.left vn vo hroom h1
  have last' := last.left_bounded hV
  exact ⟨t+(3+u),by omega,W.join V.right,Runs.seq first' (Runs.seq middle last'),
    hW.join hV.right,vsaved,hright⟩

theorem generate_runs (n m k : ℕ) (S : Store Reg Arr) (B : ℕ) (hS : S.Bounded B)
    (hl : S.scalar (.inl 0)=n^k) (hr : S.scalar (.inr ())=m^k) (hoff : S.scalar (.inl 1)=0)
    (hroom : n^k+m^k≤B) (h1 : 1≤B) :
    ∃ t≤5*(n^k+m^k)+15,∃ T,Runs (storageBound Reg Arr B) generate S t T ∧ T.Bounded B ∧
      T.array (.inr ())=(IndexedTuples.leftSelection n m k).map Fin.val ∧
      T.array (.inl ())=(IndexedTuples.rightSelection n m k).map Fin.val := by
  simpa only [IndexedTuples.leftSelection_word,IndexedTuples.rightSelection_word] using
    generate_ranges S B (n^k) (m^k) hS hl hr hoff hroom h1
end GroupWL.MachinePrograms.GroupSelectionBuilder
