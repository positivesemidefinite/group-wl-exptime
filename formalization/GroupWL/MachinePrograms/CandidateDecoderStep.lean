import GroupWL.MachinePrograms.CandidateDecoder

namespace GroupWL.MachinePrograms.CandidateDecoder
open NatArrayLanguage
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

theorem extend_runs {p j : ℕ} [Fact p.Prime] (g : Group (Fin (p^j)))
    (S : State) (M : ℕ) (v : Fin ((p^j)^j)) (c : Fin (p^j))
    (hid : NumericPGroupCandidates.identity g=NumericPGroupCandidates.zero p j)
    (hb : S.Bounded M) (hn : S.scalar (.inr .order)=p^j) (hj : S.scalar (.inr .level)=j)
    (hp : S.scalar (.inr .prime)=p)
    (ht : S.array (.inr .table)=GroupInitial.tableWord (NumericGroupGenerators.operation g))
    (hv : S.scalar (.inr .imageCode)=v.val) (hc : S.scalar (.inr .carry)=c.val)
    (hroom : ((p^j)*(p^j))*((p^j)*(p^j))≤M) (hpow : (p^j)^j≤M)
    (hexp : 2*p≤M) (hcube : (p*(p^j))^3≤M) :
    ∃t≤CandidateExtend.budget p (p^j) j+9,∃T,Runs (storageBound Reg Arr M) extend S t T ∧ T.Bounded M ∧
      T.array (.inr .table)=GroupInitial.tableWord (NumericPGroupCandidates.nextOperation g (finFunctionFinEquiv.symm v) c) ∧
      T.scalar (.inr .valid)=(if (NumericPGroupCandidates.extend g (finFunctionFinEquiv.symm v) c).isSome then 1 else 0) := by
  have hprep : ValidAtoms M setupAtoms S := by simp [setupAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult]
  obtain ⟨prep,hW⟩ := atoms_runs hb setupAtoms hprep
  let W := applyAtoms setupAtoms S
  have hidentity : (NumericGroupGenerators.identity g).val=0 := congrArg Fin.val hid
  obtain ⟨t,htime,U,compute,hU,ho,hresult⟩ := CandidateExtend.compute_runs g W.left M v c hid hW.left
    (by simp [W,applyAtoms,setupAtoms,Atom.apply,Store.setScalar,Store.setArray,Store.left,CandidateExtend.nReg,CandidateExtend.dimensionReg,CandidateExtend.identityReg,
      CandidateExtend.imageIndex,CandidateExtend.primeReg,CandidateExtend.carryReg,CandidateImages.imageIndex,
      GeneratorChoice.decoderReg,GeneratorChoice.seedReg,IndexedGeneratorTest.sourceReg,hn])
    (by simp [W,applyAtoms,setupAtoms,Atom.apply,Store.setScalar,Store.setArray,Store.left,CandidateExtend.nReg,CandidateExtend.dimensionReg,CandidateExtend.identityReg,
      CandidateExtend.imageIndex,CandidateExtend.primeReg,CandidateExtend.carryReg,CandidateImages.imageIndex,
      GeneratorChoice.decoderReg,GeneratorChoice.seedReg,IndexedGeneratorTest.sourceReg,hj])
    (by simp [W,applyAtoms,setupAtoms,Atom.apply,Store.setScalar,Store.setArray,Store.left,CandidateExtend.nReg,CandidateExtend.dimensionReg,CandidateExtend.identityReg,
      CandidateExtend.imageIndex,CandidateExtend.primeReg,CandidateExtend.carryReg,CandidateImages.imageIndex,
      GeneratorChoice.decoderReg,GeneratorChoice.seedReg,IndexedGeneratorTest.sourceReg,hidentity])
    (by simp [W,applyAtoms,setupAtoms,Atom.apply,Store.setScalar,Store.setArray,Store.left,CandidateExtend.nReg,CandidateExtend.dimensionReg,CandidateExtend.identityReg,
      CandidateExtend.imageIndex,CandidateExtend.primeReg,CandidateExtend.carryReg,CandidateImages.imageIndex,
      GeneratorChoice.decoderReg,GeneratorChoice.seedReg,IndexedGeneratorTest.sourceReg,ht])
    (by simp [W,applyAtoms,setupAtoms,Atom.apply,Store.setScalar,Store.setArray,Store.left,CandidateExtend.nReg,CandidateExtend.dimensionReg,CandidateExtend.identityReg,
      CandidateExtend.imageIndex,CandidateExtend.primeReg,CandidateExtend.carryReg,CandidateImages.imageIndex,
      GeneratorChoice.decoderReg,GeneratorChoice.seedReg,IndexedGeneratorTest.sourceReg,hv])
    (by simp [W,applyAtoms,setupAtoms,Atom.apply,Store.setScalar,Store.setArray,Store.left,CandidateExtend.nReg,CandidateExtend.dimensionReg,CandidateExtend.identityReg,
      CandidateExtend.imageIndex,CandidateExtend.primeReg,CandidateExtend.carryReg,CandidateImages.imageIndex,
      GeneratorChoice.decoderReg,GeneratorChoice.seedReg,IndexedGeneratorTest.sourceReg,hp])
    (by simp [W,applyAtoms,setupAtoms,Atom.apply,Store.setScalar,Store.setArray,Store.left,CandidateExtend.nReg,CandidateExtend.dimensionReg,CandidateExtend.identityReg,
      CandidateExtend.imageIndex,CandidateExtend.primeReg,CandidateExtend.carryReg,CandidateImages.imageIndex,
      GeneratorChoice.decoderReg,GeneratorChoice.seedReg,IndexedGeneratorTest.sourceReg,hc]) hroom hpow hexp hcube
  let V := U.join W.right
  have hV : V.Bounded M := hU.join hW.right
  have hfinish : ValidAtoms M finishAtoms V := by simp [finishAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult]
  obtain ⟨finish,hT⟩ := atoms_runs hV finishAtoms hfinish
  refine ⟨7+(t+2),by omega,applyAtoms finishAtoms V,.seq prep (.seq (compute.left_bounded hW) finish),hT,?_,?_⟩
  · simpa [applyAtoms,finishAtoms,Atom.apply,Store.setScalar,Store.setArray,V] using ho
  · simpa [applyAtoms,finishAtoms,Atom.apply,Store.setScalar,Store.setArray,V] using hresult

theorem extend_frame {B S T t} (h : Runs B extend S t T) (r : Control) (hr : r≠.valid) :
    T.scalar (.inr r)=S.scalar (.inr r) :=
  h.scalar_eq_of_not_mem _ ((by decide : ∀r:Control,r≠.valid → (Sum.inr r : Reg)∉extend.scalarWrites) r hr)

end GroupWL.MachinePrograms.CandidateDecoder
