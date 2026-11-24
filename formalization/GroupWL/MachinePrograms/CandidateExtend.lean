import GroupWL.MachinePrograms.CandidateImages
import GroupWL.MachinePrograms.ExtensionCheck
import GroupWL.CandidateTableEncoding

/-! One complete compact-candidate stage: canonical generators, proposed
image map, cyclic-extension multiplication table, and finite group validation. -/
namespace GroupWL.MachinePrograms.CandidateExtend
open NatArrayLanguage
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

abbrev Reg := CandidateImages.Reg ⊕ ExtensionCheck.Reg
abbrev Arr := CandidateImages.Arr ⊕ ExtensionCheck.Arr
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr
instance : DecidableEq Reg := inferInstance
instance : DecidableEq Arr := inferInstance
instance : Fintype Reg := inferInstance
instance : Fintype Arr := inferInstance

def nReg : Reg := .inl (.inl (GeneratorChoice.decoderReg .n))
def dimensionReg : Reg := .inl (.inl (GeneratorChoice.decoderReg .arity))
def identityReg : Reg := .inl (.inl (GeneratorChoice.seedReg .identity))
def tableArray : Arr := .inl (.inl (GeneratorChoice.closureArr .table))
def imageIndex : Reg := .inl CandidateImages.imageIndex
def primeReg : Reg := .inr (.inl .prime)
def carryReg : Reg := .inr (.inl .carry)
def outputArray : Arr := .inr (.inl .output)
def resultReg : Reg := .inr (.inr .result)

def prepare : List (Atom Reg Arr) := [
  .copy (.inr (.inl .tail)) nReg,.copy (.inr (.inl .identity)) identityReg,
  .copyArray (.inr (.inl .table)) tableArray,
  .copyArray (.inr (.inl .image)) (.inl CandidateImages.outputArray)]
def compute : Code := sequence [CandidateImages.compute.map Sum.inl Sum.inl,
  atoms prepare,ExtensionCheck.compute.map Sum.inr Sum.inr]

def budget (p n D : ℕ) := CandidateImages.choiceBudget n D+6*D+17+CandidateImages.imageBudget n D+
  (36*(p*n)^3+(p*n)*(p*n)*(4*p+23)+18)

theorem compute_runs {p D : ℕ} [Fact p.Prime] (g : Group (Fin (p^D)))
    (S : State) (M : ℕ) (v : Fin ((p^D)^D)) (c : Fin (p^D))
    (hid : NumericPGroupCandidates.identity g=NumericPGroupCandidates.zero p D)
    (hb : S.Bounded M) (hn : S.scalar nReg=p^D) (hk : S.scalar dimensionReg=D)
    (he : S.scalar identityReg=(NumericGroupGenerators.identity g).val)
    (ht : S.array tableArray=GroupInitial.tableWord (NumericGroupGenerators.operation g))
    (hv : S.scalar imageIndex=v.val) (hp : S.scalar primeReg=p) (hc : S.scalar carryReg=c.val)
    (hroom : ((p^D)*(p^D))*((p^D)*(p^D))≤M) (hpow : (p^D)^D≤M)
    (hexp : 2*p≤M) (hcube : (p*(p^D))^3≤M) :
    ∃t≤budget p (p^D) D,∃T,Runs (storageBound Reg Arr M) compute S t T ∧ T.Bounded M ∧
      T.array outputArray=GroupInitial.tableWord (NumericPGroupCandidates.nextOperation g (finFunctionFinEquiv.symm v) c) ∧
      T.scalar resultReg=(if (NumericPGroupCandidates.extend g (finFunctionFinEquiv.symm v) c).isSome then 1 else 0) := by
  obtain ⟨t,htime,U,images,hU,hout⟩ := CandidateImages.compute_runs g S.left M v hb.left hn hk he ht hv hroom hpow
  let V := U.join S.right
  have hV : V.Bounded M := hU.join hb.right
  have hnV : V.scalar nReg=p^D := (images.scalar_eq_of_not_mem _ (by decide)).trans hn
  have heV : V.scalar identityReg=(NumericGroupGenerators.identity g).val :=
    (images.scalar_eq_of_not_mem _ (by decide)).trans he
  have htV : V.array tableArray=GroupInitial.tableWord (NumericGroupGenerators.operation g) :=
    (images.array_eq_of_not_mem _ (by decide)).trans ht
  have hpV : V.scalar primeReg=p := hp
  have hcV : V.scalar carryReg=c.val := hc
  have hvprep : ValidAtoms M prepare V := by simp [prepare,ValidAtoms,Atom.Valid,Atom.SmallResult]
  obtain ⟨prep,hW⟩ := atoms_runs hV prepare hvprep
  let W := applyAtoms prepare V
  have hinput : ExtensionTablePrograms.Input (p:=p) (NumericGroupGenerators.operation g)
      (NumericPGroupCandidates.expand g (finFunctionFinEquiv.symm v)) c (NumericGroupGenerators.identity g) M W.right.left := by
    refine ⟨hW.right.left,?_,?_,?_,?_,?_,?_⟩
    · simpa [W,applyAtoms,prepare,Atom.apply,Store.setScalar,Store.setArray,Store.right,Store.left] using hnV
    · simpa [W,applyAtoms,prepare,Atom.apply,Store.setScalar,Store.setArray,Store.right,Store.left,primeReg] using hpV
    · simpa [W,applyAtoms,prepare,Atom.apply,Store.setScalar,Store.setArray,Store.right,Store.left,carryReg] using hcV
    · simpa [W,applyAtoms,prepare,Atom.apply,Store.setScalar,Store.setArray,Store.right,Store.left] using heV
    · simpa [W,applyAtoms,prepare,Atom.apply,Store.setScalar,Store.setArray,Store.right,Store.left] using htV
    · simpa [W,applyAtoms,prepare,Atom.apply,Store.setScalar,Store.setArray,Store.right,Store.left,V,
        ExtensionTablePrograms.mapWord,GroupInitial.tupleWord] using hout
  obtain ⟨u,hu,X,check,hX,hword,hresult⟩ := ExtensionCheck.compute_runs (Fact.out : p.Prime).pos
    (pow_pos (Fact.out : p.Prime).pos D) (NumericGroupGenerators.operation g)
    (NumericPGroupCandidates.expand g (finFunctionFinEquiv.symm v)) c (NumericGroupGenerators.identity g)
    W.right M hW.right hinput hexp ((Nat.le_mul_self _).trans hroom) hcube
  have checked := check.right_bounded hW
  refine ⟨t+(4+(u+0)),by unfold budget; omega,W.left.join X,
    .seq (images.left_bounded hb) (.seq prep (.seq checked (.skip checked.end_bound))),hW.left.join hX,?_,?_⟩
  · simpa [outputArray,NumericPGroupCandidates.nextOperation_tableWord] using hword
  · change X.scalar (.inr .result)=_
    rw [hresult]
    simp only [NumericPGroupCandidates.raw_valid_iff g (finFunctionFinEquiv.symm v) c hid]

end GroupWL.MachinePrograms.CandidateExtend
