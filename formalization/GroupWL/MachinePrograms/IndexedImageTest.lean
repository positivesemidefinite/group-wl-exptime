import GroupWL.MachinePrograms.GroupImageTest
import GroupWL.MachinePrograms.IndexedWLDecode
import GroupWL.MachinePrograms.NatArrayProjection

/-! Decode a target generator-image tuple index and run the concrete map test. -/
namespace GroupWL.MachinePrograms.IndexedImageTest
open NatArrayLanguage
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

abbrev Reg := IndexedWL.Reg ⊕ GroupImageTest.Reg
abbrev Arr := IndexedWL.Arr ⊕ GroupImageTest.Arr
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

instance : DecidableEq Reg := inferInstance
instance : DecidableEq Arr := inferInstance
instance : Fintype Reg := inferInstance
instance : Fintype Arr := inferInstance

def resultReg : Reg := .inr (.inr .result)
def targetTuple : Arr := .inr (.inl (.inl .right))
def sourceTuple : Arr := .inr (.inl (.inl .left))

def test : Code := sequence [
  IndexedWL.decodeVector.map Sum.inl Sum.inl,
  .atom (.copyArray targetTuple (.inl .vector)),
  GroupImageTest.test.map Sum.inr Sum.inr]

structure Ready {n m k : ℕ} (op : Fin n→Fin n→Fin n) (op' : Fin m→Fin m→Fin m)
    (identity : Fin n) (identity' : Fin m) (a : Fin k→Fin n) (S : State) : Prop where
  base : S.scalar (.inl .n)=m
  arity : S.scalar (.inl .arity)=k
  one : S.scalar (.inl .one)=1
  vector : (S.array (.inl .vector)).length=k
  image : GroupImageTest.Ready op op' identity identity' S.right
  tuple : S.array sourceTuple=List.ofFn (fun i => (a i).val)

def Accepts {n m k : ℕ} (op : Fin n→Fin n→Fin n) (op' : Fin m→Fin m→Fin m)
    (identity : Fin n) (identity' : Fin m) (a : Fin k→Fin n) (i : ℕ) : Prop :=
  if hi : i<m^k then GroupImageTest.Valid op op' identity identity' a
    (finFunctionFinEquiv.symm (⟨i,hi⟩ : Fin (m^k))) else False
instance {n m k : ℕ} (op : Fin n→Fin n→Fin n) (op' : Fin m→Fin m→Fin m)
    (identity : Fin n) (identity' : Fin m) (a : Fin k→Fin n) :
    DecidablePred (Accepts op op' identity identity' a) := fun i => by unfold Accepts; infer_instance

theorem ready_setValue {n m k : ℕ} {op : Fin n→Fin n→Fin n} {op' : Fin m→Fin m→Fin m}
    {identity : Fin n} {identity' : Fin m} {a : Fin k→Fin n} {S : State}
    (h : Ready op op' identity identity' a S) (i : ℕ) :
    Ready op op' identity identity' a (S.setScalar (.inl .value) i) := by
  refine ⟨by simpa using h.base,by simpa using h.arity,by simpa using h.one,h.vector,?_,h.tuple⟩
  exact h.image

theorem test_runs {n m k : ℕ} (S : State) (M : ℕ)
    (op : Fin n→Fin n→Fin n) (op' : Fin m→Fin m→Fin m)
    (identity : Fin n) (identity' : Fin m) (a : Fin k→Fin n) (v : Fin (m^k))
    (hb : S.Bounded M) (hready : Ready op op' identity identity' a S)
    (hv : S.scalar (.inl .value)=v.val) (hroom : (n*m)*(n*m)≤M) :
    ∃t≤10*(n*m)^3+8*(n*m)+19*k+n*(9*m+13)+19*n*n+40,∃T,
      Runs (storageBound Reg Arr M) test S t T ∧ T.Bounded M ∧
      Ready op op' identity identity' a T ∧
      (T.scalar resultReg=1 ↔ Accepts op op' identity identity' a v.val) := by
  obtain ⟨t,ht,U,decode,hU,ho⟩ := IndexedWL.decodeVector_runs S.left M m k v.val hb.left
    hready.base (Nat.zero_lt_of_lt identity'.isLt) hready.arity hv hready.one hready.vector
  let V := U.join S.right
  have hV : V.Bounded M := hU.join hb.right
  let W := (Atom.copyArray targetTuple (Sum.inl IndexedWL.Arr.vector)).apply V
  have hW : W.Bounded M := Atom.apply_bounded hV _ trivial
  have copy := atom_runs hV (.copyArray targetTuple (.inl .vector)) trivial trivial
  have htuple : W.right.array (.inl (.inl .right))=
      List.ofFn (fun i => ((finFunctionFinEquiv.symm v) i).val) := by
    simpa [W,Atom.apply,Store.right,V,targetTuple,IndexedRefinement.vectorWord,IndexedRefinement.digit_equiv] using ho
  have hsource : W.right.array (.inl (.inl .left))=List.ofFn (fun i => (a i).val) := by
    simpa [W,Atom.apply,Store.right,V,targetTuple,sourceTuple] using hready.tuple
  have hr : GroupImageTest.Ready op op' identity identity' W.right := by
    rcases hready.image with ⟨he,hn,hm,hs,ht⟩
    refine ⟨?_,?_,?_,?_,?_⟩
    · rcases he with ⟨hc,hseed,hi,hclo,htab,hr,hc',hi'⟩
      constructor <;> simp_all [W,Atom.apply,Store.right,Store.left,V,targetTuple,
        GroupImageExpansion.imageArray,PairedImageExpansion.seedReg,PairedImageExpansion.closureReg,
        PairedImageExpansion.seedArray,PairedImageExpansion.closureArray,PairedImageExpansion.imageReg]
    · simpa [W,Atom.apply,Store.right,V,targetTuple] using hn
    · simpa [W,Atom.apply,Store.right,V,targetTuple] using hm
    · simpa [W,Atom.apply,Store.right,V,targetTuple] using hs
    · simpa [W,Atom.apply,Store.right,V,targetTuple] using ht
  obtain ⟨u,hu,X,check,hX,hout⟩ := GroupImageTest.test_runs W.right M op op' identity identity' a
    (finFunctionFinEquiv.symm v) hW.right hr hsource htuple hroom
  have checked := check.right_bounded hW
  let T := W.left.join X
  have hT : T.Bounded M := hW.left.join hX
  have scalarFrame (r : IndexedWL.Reg) (h : r∉IndexedWL.decodeVector.scalarWrites) : U.scalar r=S.left.scalar r :=
    decode.scalar_eq_of_not_mem r h
  refine ⟨t+(1+(u+0)),by omega,T,.seq (decode.left_bounded hb)
    (.seq copy (.seq checked (.skip checked.end_bound))),hT,?_,?_⟩
  · refine ⟨?_,?_,?_,?_,?_,?_⟩
    · simpa [T,W,Atom.apply,Store.left,V,targetTuple] using (scalarFrame .n (by decide)).trans hready.base
    · simpa [T,W,Atom.apply,Store.left,V,targetTuple] using (scalarFrame .arity (by decide)).trans hready.arity
    · simpa [T,W,Atom.apply,Store.left,V,targetTuple] using (scalarFrame .one (by decide)).trans hready.one
    · simp [T,W,Atom.apply,Store.left,V,targetTuple,ho,IndexedRefinement.vectorWord]
    · exact GroupImageTest.ready_frame check hr
    · exact (GroupImageTest.sourceTuple_frame check).trans hsource
  · simpa [T,resultReg,Accepts,v.isLt] using hout

end GroupWL.MachinePrograms.IndexedImageTest
