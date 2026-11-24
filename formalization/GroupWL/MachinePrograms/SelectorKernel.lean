import GroupWL.MachinePrograms.SelectorMatrix
import GroupWL.MachinePrograms.KernelCost

/-! Selected-coordinate equations followed by the concrete Gaussian kernel. -/
namespace GroupWL.MachinePrograms.SelectorKernel
open NatArrayLanguage
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048

abbrev Reg := SelectorMatrix.Reg ⊕ KernelProgram.Reg
abbrev Arr := SelectorMatrix.Arr ⊕ KernelProgram.Arr
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def setup (p : ℕ) : List (Atom Reg Arr) := [
  .copy (.inr (KernelProgram.wr .ambient)) (.inl .columns),
  .arrayLength (.inr (KernelProgram.wr .rows)) (.inl .selectors),
  .copyArray (.inr (KernelProgram.wa .input)) (.inl .output),
  .const (.inr (KernelProgram.wr .modulus)) p]
def program (p : ℕ) : Code := .seq (SelectorMatrix.program.map Sum.inl Sum.inl)
  (.seq (atoms (setup p)) ((KernelProgram.program p).map Sum.inr Sum.inr))

theorem word_values (selectors : List ℕ) (n p : ℕ) (hp : 1<p) :
    ∀ x∈SelectorMatrix.word selectors n,x<p := by
  intro x hx
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  unfold SelectorMatrix.entry
  split_ifs <;> omega

theorem program_runs (p : ℕ) [NeZero p] (selectors : List ℕ) (n M : ℕ)
    (hp : 1<p) (hsize : selectors.length*n≤M) (hpM : p*p+p≤M) (hnM : n*n≤M)
    (S : State) (bounded : S.Bounded M) (hs : S.left.array .selectors=selectors)
    (hn : S.left.scalar .columns=n) :
    ∃ t≤selectors.length*n*7+12+220*(selectors.length+n+p+1)^4, ∃ T,
      Runs (storageBound Reg Arr M) (program p) S t T ∧ T.Bounded M ∧
      KernelProgram.Represents p n 0 (SelectorMatrix.word selectors n)
        (KernelProgram.executeRows (SelectorMatrix.word selectors n) p n selectors.length
          (KernelProgram.initial n)) T.right := by
  obtain ⟨t,ht,U,selected,hUB,hUR,hUout⟩ := SelectorMatrix.program_runs selectors n M
    (by omega) hsize S.left bounded.left hs hn
  have sourceRun := selected.left_bounded bounded
  let V := U.join S.right
  have hVB : V.Bounded M := hUB.join bounded.right
  have hvalid : ValidAtoms M (setup p) V := by
    simp [setup,ValidAtoms,Atom.Valid,Atom.SmallResult]
    omega
  obtain ⟨prepared,hWB⟩ := atoms_runs hVB (setup p) hvalid
  let W := applyAtoms (setup p) V
  have ambient : W.right.scalar (KernelProgram.wr .ambient)=n := by
    simpa [W,setup,applyAtoms,Atom.apply,Store.setScalar,Store.setArray,Store.right,V,Store.join,
      -Sum.elim_update_left,-Sum.elim_update_right] using hUR.2.1
  have rows : W.right.scalar (KernelProgram.wr .rows)=selectors.length := by
    simpa [W,setup,applyAtoms,Atom.apply,Store.setScalar,Store.setArray,Store.right,V,Store.join,
      -Sum.elim_update_left,-Sum.elim_update_right] using congrArg List.length hUR.1
  have modulus : W.right.scalar (KernelProgram.wr .modulus)=p := by
    simp [W,setup,applyAtoms,Atom.apply,Store.setScalar,Store.setArray,Store.right]
  have input : W.right.array (KernelProgram.wa .input)=SelectorMatrix.word selectors n := by
    simpa [W,setup,applyAtoms,Atom.apply,Store.setScalar,Store.setArray,Store.right,V,Store.join,
      -Sum.elim_update_left,-Sum.elim_update_right] using hUout
  obtain ⟨u,hu,X,kernel,hXB,hrep⟩ := KernelProgram.program_runs p n selectors.length M
    (SelectorMatrix.word selectors n) W.right hWB.right ambient rows modulus input hp hpM hnM
    List.length_ofFn (word_values selectors n p hp)
  have finalRun := kernel.right_bounded hWB
  refine ⟨t+(4+u),?_,W.left.join X,sourceRun.seq (prepared.seq finalRun),hWB.left.join hXB,hrep⟩
  have hu' := hu.trans (KernelProgram.programCost_le selectors.length n p)
  omega

end GroupWL.MachinePrograms.SelectorKernel
