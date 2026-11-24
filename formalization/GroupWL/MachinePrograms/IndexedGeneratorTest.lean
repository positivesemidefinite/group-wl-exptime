import GroupWL.MachinePrograms.GeneratorTest
import GroupWL.MachinePrograms.IndexedWLDecode

/-! Decode a bounded numeric tuple index and execute the actual generator test. -/
namespace GroupWL.MachinePrograms.IndexedGeneratorTest
open NatArrayLanguage IndexedRefinement
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

abbrev Reg := IndexedWL.Reg ⊕ GeneratorTest.Reg
abbrev Arr := IndexedWL.Arr ⊕ GeneratorTest.Arr
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def test : Code := sequence [
  IndexedWL.decodeVector.map Sum.inl Sum.inl,
  .atom (.copyArray (.inr (.inl (.inl .generators))) (.inl .vector)),
  GeneratorTest.test.map Sum.inr Sum.inr]

def sourceReg (r : GeneratorMask.Reg) : Reg := .inr (.inl (.inl r))
def closureReg (r : GroupSaturation.Reg) : Reg := .inr (.inl (.inr r))
def sourceArr (a : GeneratorMask.Arr) : Arr := .inr (.inl (.inl a))
def closureArr (a : GroupSaturation.Arr) : Arr := .inr (.inl (.inr a))
def resultReg : Reg := .inr (.inr .result)

theorem test_runs (S : State) (n k M : ℕ) (v : Fin (n^k)) (e : Fin n)
    (op : Fin n → Fin n → Fin n)
    (hb : S.Bounded M) (hn : S.scalar (.inl .n)=n) (hk : S.scalar (.inl .arity)=k)
    (hv : S.scalar (.inl .value)=v.val) (hone : S.scalar (.inl .one)=1)
    (hvector : (S.array (.inl .vector)).length=k)
    (hn' : S.scalar (sourceReg .order)=n) (he : S.scalar (sourceReg .identity)=e.val)
    (hn'' : S.scalar (closureReg .order)=n) (hlen : (S.array (closureArr .table)).length=n*n)
    (hread : ∀ i : Fin (n*n),(S.array (closureArr .table))[i.val]?.getD 0=
      (op (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2).val)
    (hroom : n*n≤M) :
    ∃t≤10*n^3+13*n+11*k+26,∃T,Runs (storageBound Reg Arr M) test S t T ∧
      T.Bounded M ∧ (T.array (.inl .vector)).length=k ∧
      (T.scalar resultReg=1 ↔ GroupSaturation.closureSet op
        (insert e (Finset.univ.image (finFunctionFinEquiv.symm v))) n=Finset.univ) := by
  have hnpos : 0<n := by have := e.isLt; omega
  obtain ⟨t,ht,U,decode,hU,ho⟩ := IndexedWL.decodeVector_runs S.left M n k v.val hb.left hn hnpos hk hv hone hvector
  let V := U.join S.right
  have hV : V.Bounded M := hU.join hb.right
  let W := (Atom.copyArray (sourceArr .generators) (Sum.inl IndexedWL.Arr.vector)).apply V
  have hW : W.Bounded M := Atom.apply_bounded hV _ trivial
  have copy := atom_runs hV (.copyArray (sourceArr .generators) (.inl .vector)) trivial trivial
  have hgs : W.right.array (.inl (.inl .generators))=(List.ofFn (finFunctionFinEquiv.symm v)).map Fin.val := by
    simpa [W,Atom.apply,sourceArr,Store.right,V,vectorWord,List.map_ofFn,digit_equiv] using ho
  obtain ⟨u,hu,X,generate,hX,hout⟩ := GeneratorTest.test_runs W.right n M e
    (List.ofFn (finFunctionFinEquiv.symm v)) op hW.right
    (by simpa [W,Atom.apply,Store.right,V,sourceReg] using hn')
    (by simpa [W,Atom.apply,Store.right,V,sourceReg] using he) hgs
    (by simpa [W,Atom.apply,Store.right,V,closureReg] using hn'')
    (by simpa [W,Atom.apply,Store.right,V,closureArr,sourceArr] using hlen)
    (by simpa [W,Atom.apply,Store.right,V,closureArr,sourceArr] using hread) hroom
  have generated := generate.right_bounded hW
  refine ⟨t+(1+(u+0)),by simp only [List.length_ofFn] at hu; omega,W.left.join X,
    .seq (decode.left_bounded hb) (.seq copy (.seq generated (.skip generated.end_bound))),hW.left.join hX,?_,?_⟩
  · simpa [W,Atom.apply,Store.left,V,sourceArr,ho,vectorWord]
  · have hset : (List.ofFn (finFunctionFinEquiv.symm v)).toFinset=Finset.univ.image (finFunctionFinEquiv.symm v) := by
      ext x; simp
    simpa [resultReg,hset] using hout

theorem scalarFrame {B S T t} (h : Runs B test S t T) (r : Reg)
    (hr : r∈({.inl .n,.inl .arity,.inl .one,sourceReg .order,sourceReg .identity,closureReg .order} : Finset Reg)) :
    T.scalar r=S.scalar r := by
  exact h.scalar_eq_of_not_mem r ((by decide : ∀r∈({.inl .n,.inl .arity,.inl .one,sourceReg .order,sourceReg .identity,closureReg .order} : Finset Reg),r∉test.scalarWrites) r hr)

theorem tableFrame {B S T t} (h : Runs B test S t T) :
    T.array (closureArr .table)=S.array (closureArr .table) := h.array_eq_of_not_mem _ (by decide)

end GroupWL.MachinePrograms.IndexedGeneratorTest
