import GroupWL.MachinePrograms.GeneratorChoice
import GroupWL.MachinePrograms.GroupImageClient
import GroupWL.NumericPGroupCandidates

/-! From a numeric tail group and a proposed image-tuple index, compute the
exact image map used by the compact candidate decoder. -/
namespace GroupWL.MachinePrograms.CandidateImages
open NatArrayLanguage
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

abbrev Reg := GeneratorChoice.Reg ⊕ GroupImageClient.Reg
abbrev Arr := GeneratorChoice.Arr ⊕ GroupImageClient.Arr
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr
instance : DecidableEq Reg := inferInstance
instance : DecidableEq Arr := inferInstance
instance : Fintype Reg := inferInstance
instance : Fintype Arr := inferInstance

def imageIndex : Reg := .inr (.inl 18)
def outputArray : Arr := .inr GroupImageClient.imageArray

def saveGenerators : List (Atom Reg Arr) := [
  .copyArray (.inr GroupImageClient.leftTuple) (.inl (GeneratorChoice.decoderArr .vector)),
  .copy (.inl (GeneratorChoice.decoderReg .value)) imageIndex]
def imageSetup : List (Atom Reg Arr) := [
  .copyArray (.inr GroupImageClient.rightTuple) (.inl (GeneratorChoice.decoderArr .vector)),
  .copy (.inr (.inl 0)) (.inl (GeneratorChoice.decoderReg .n)),
  .copy (.inr (.inl 1)) (.inl (GeneratorChoice.decoderReg .n)),
  .copy (.inr GroupImageClient.identityReg) (.inl (GeneratorChoice.seedReg .identity)),
  .copy (.inr GroupImageClient.identityReg') (.inl (GeneratorChoice.seedReg .identity)),
  .copyArray (.inr (.inl 0)) (.inl (GeneratorChoice.closureArr .table)),
  .copyArray (.inr (.inl 1)) (.inl (GeneratorChoice.closureArr .table))]
def compute : Code := sequence [
  GeneratorChoice.choose.map Sum.inl Sum.inl,atoms saveGenerators,
  GeneratorChoice.decode.map Sum.inl Sum.inl,atoms imageSetup,
  GroupImageClient.expand.map Sum.inr Sum.inr]

def choiceBudget (n D : ℕ) := n^D*(10*n^3+13*n+11*D+35)+9*D+20
def imageBudget (n D : ℕ) := 10*(n*n)^3+15*((n*n)*(n*n))+8*(n*n)+13*D+n*(9*n+13)+44

theorem compute_runs {p D : ℕ} [Fact p.Prime] (g : Group (Fin (p^D)))
    (S : State) (M : ℕ) (v : Fin ((p^D)^D)) (hb : S.Bounded M)
    (hn : S.scalar (.inl (GeneratorChoice.decoderReg .n))=p^D)
    (hk : S.scalar (.inl (GeneratorChoice.decoderReg .arity))=D)
    (he : S.scalar (.inl (GeneratorChoice.seedReg .identity))=(NumericGroupGenerators.identity g).val)
    (htable : S.array (.inl (GeneratorChoice.closureArr .table))=
      GroupInitial.tableWord (NumericGroupGenerators.operation g))
    (hv : S.scalar imageIndex=v.val) (hroom : ((p^D)*(p^D))*((p^D)*(p^D))≤M)
    (hpow : (p^D)^D≤M) :
    ∃t≤choiceBudget (p^D) D+6*D+13+imageBudget (p^D) D,∃T,
      Runs (storageBound Reg Arr M) compute S t T ∧ T.Bounded M ∧
      T.array outputArray=GroupInitial.tupleWord
        (NumericPGroupCandidates.expand g (finFunctionFinEquiv.symm v)) := by
  have hsq : (p^D)*(p^D)≤M := (Nat.le_mul_self _).trans hroom
  obtain ⟨tc,htc,U,choose,hU,ready,hfound,hresult,hgen,hlimit⟩ :=
    GeneratorChoice.choose_numeric_runs g S.left M hb.left hn hk he htable hsq hpow
  let V := U.join S.right
  have hV : V.Bounded M := hU.join hb.right
  have hsave : ValidAtoms M saveGenerators V := by
    simp [saveGenerators,ValidAtoms,Atom.Valid,Atom.SmallResult]
  obtain ⟨save,hW⟩ := atoms_runs hV saveGenerators hsave
  let W := applyAtoms saveGenerators V
  obtain ⟨td,htd,X,decode,hX,himages⟩ := IndexedWL.decodeVector_runs W.left.left.left M (p^D) D v.val
    hW.left.left.left
    (by simpa [W,applyAtoms,saveGenerators,Atom.apply,Store.setScalar,Store.setArray,Store.left,
      GeneratorChoice.decoderReg,GeneratorChoice.decoderArr,V] using ready.base)
    (pow_pos (Fact.out : p.Prime).pos D)
    (by simpa [W,applyAtoms,saveGenerators,Atom.apply,Store.setScalar,Store.setArray,Store.left,
      GeneratorChoice.decoderReg,GeneratorChoice.decoderArr,V] using ready.arity)
    (by simpa [W,applyAtoms,saveGenerators,Atom.apply,Store.setScalar,Store.setArray,Store.left,
      GeneratorChoice.decoderReg,GeneratorChoice.decoderArr,V,imageIndex,Store.right] using hv)
    (by simpa [W,applyAtoms,saveGenerators,Atom.apply,Store.setScalar,Store.setArray,Store.left,
      GeneratorChoice.decoderReg,GeneratorChoice.decoderArr,V] using ready.one)
    (by simpa [W,applyAtoms,saveGenerators,Atom.apply,Store.setScalar,Store.setArray,Store.left,
      GeneratorChoice.decoderReg,GeneratorChoice.decoderArr,V] using ready.vector)
  let Y := ((X.join W.left.left.right).join W.left.right).join W.right
  have hY : Y.Bounded M := ((hX.join hW.left.left.right).join hW.left.right).join hW.right
  have decoded : Runs (storageBound Reg Arr M) (GeneratorChoice.decode.map Sum.inl Sum.inl) W td Y :=
    ((decode.left_bounded hW.left.left).left_bounded hW.left).left_bounded hW
  have tailRun : Runs (storageBound Reg Arr M)
      (.seq (atoms saveGenerators) (GeneratorChoice.decode.map Sum.inl Sum.inl)) V (2+td) Y := .seq save decoded
  have hyn : Y.scalar (.inl (GeneratorChoice.decoderReg .n))=p^D :=
    (tailRun.scalar_eq_of_not_mem _ (by decide)).trans ready.base
  have hye : Y.scalar (.inl (GeneratorChoice.seedReg .identity))=(NumericGroupGenerators.identity g).val :=
    (tailRun.scalar_eq_of_not_mem _ (by decide)).trans ready.identity
  have hyt : Y.array (.inl (GeneratorChoice.closureArr .table))=
      GroupInitial.tableWord (NumericGroupGenerators.operation g) :=
    (tailRun.array_eq_of_not_mem _ (by decide)).trans ready.table_eq
  have hygen : Y.array (.inr GroupImageClient.leftTuple)=GroupInitial.tupleWord (NumericGroupGenerators.generators g) := by
    simpa [Y,W,applyAtoms,saveGenerators,Atom.apply,Store.setScalar,Store.setArray,V,
      GeneratorChoice.decoderArr,Store.left,Store.right] using hgen
  have hyimages : Y.array (.inl (GeneratorChoice.decoderArr .vector))=
      GroupInitial.tupleWord (finFunctionFinEquiv.symm v) := by
    simpa [Y,GeneratorChoice.decoderArr,IndexedRefinement.vectorWord,IndexedRefinement.digit_equiv,
      GroupInitial.tupleWord] using himages
  have hsetup : ValidAtoms M imageSetup Y := by
    simp [imageSetup,ValidAtoms,Atom.Valid,Atom.SmallResult]
  obtain ⟨setup,hZ⟩ := atoms_runs hY imageSetup hsetup
  let Z := applyAtoms imageSetup Y
  obtain ⟨ti,hti,T,images,hT,hout⟩ := GroupImageClient.expand_runs Z.right M
    (NumericGroupGenerators.operation g) (NumericGroupGenerators.operation g)
    (NumericGroupGenerators.identity g) (NumericGroupGenerators.identity g)
    (NumericGroupGenerators.generators g) (finFunctionFinEquiv.symm v) hZ.right
    (by simpa [Z,applyAtoms,imageSetup,Atom.apply,Store.setScalar,Store.setArray,Store.right] using hyn)
    (by simpa [Z,applyAtoms,imageSetup,Atom.apply,Store.setScalar,Store.setArray,Store.right] using hyn)
    (by simpa [Z,applyAtoms,imageSetup,Atom.apply,Store.setScalar,Store.setArray,Store.right] using hye)
    (by simpa [Z,applyAtoms,imageSetup,Atom.apply,Store.setScalar,Store.setArray,Store.right] using hye)
    (by simpa [Z,applyAtoms,imageSetup,Atom.apply,Store.setScalar,Store.setArray,Store.right] using hyt)
    (by simpa [Z,applyAtoms,imageSetup,Atom.apply,Store.setScalar,Store.setArray,Store.right] using hyt)
    (by simpa [Z,applyAtoms,imageSetup,Atom.apply,Store.setScalar,Store.setArray,Store.right] using hygen)
    (by simpa [Z,applyAtoms,imageSetup,Atom.apply,Store.setScalar,Store.setArray,Store.right] using hyimages) hroom
  have expanded := images.right_bounded hZ
  refine ⟨tc+(2+(td+(7+(ti+0)))),by unfold choiceBudget imageBudget; omega,Z.left.join T,
    .seq (choose.left_bounded hb) (.seq save (.seq decoded (.seq setup (.seq expanded (.skip expanded.end_bound))))),
    hZ.left.join hT,?_⟩
  exact hout

end GroupWL.MachinePrograms.CandidateImages
