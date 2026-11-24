import GroupWL.MachinePrograms.InputCoordinateMetadata
import GroupWL.MachinePrograms.SelectorKernel

/-! The complete chosen-space kernel construction from readout radical widths. -/
namespace GroupWL.MachinePrograms.ChosenKernel
open NatArrayLanguage
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048

abbrev Reg := InputCoordinateMetadata.Reg ⊕ SelectorKernel.Reg
abbrev Arr := InputCoordinateMetadata.Arr ⊕ SelectorKernel.Arr
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def sizes (widths : List ℕ) (b q : ℕ) := ArrayScaledOffsets.scaled (RingDimensions.dimensions widths b) q
def total (widths : List ℕ) (b q : ℕ) := FilterRanks.count (sizes widths b q) (sizes widths b q).length
def selectors (widths : List ℕ) (b q : ℕ) :=
  List.ofFn (fun i : Fin (sizes widths b q).length => FilterRanks.count (sizes widths b q) i.val)
def data (p : ℕ) (widths : List ℕ) (b q : ℕ) :=
  KernelProgram.executeRows (SelectorMatrix.word (selectors widths b q) (total widths b q))
    p (total widths b q) (b+widths.length) (KernelProgram.initial (total widths b q))

def setup : List (Atom Reg Arr) := [
  .copyArray (.inr (.inl .selectors)) (.inl (.inr (.inr .ranks))),
  .copy (.inr (.inl .columns)) (.inl (.inr (.inr .count)))]
def program (p : ℕ) : Code := .seq (InputCoordinateMetadata.program.map Sum.inl Sum.inl)
  (.seq (atoms setup) ((SelectorKernel.program p).map Sum.inr Sum.inr))

theorem program_runs (p : ℕ) [NeZero p] (widths : List ℕ) (b q M : ℕ)
    (hp : 1<p) (hq : 1≤q) (hM : b+2≤M) (hsize : (b+widths.length)*(b+2)*q≤M)
    (hv : ∀ x∈widths,x≤b) (hmatrix : (b+widths.length)*total widths b q≤M)
    (hpM : p*p+p≤M) (hnM : total widths b q*total widths b q≤M)
    (S : State) (bounded : S.Bounded M) (hws : S.left.left.array .widths=widths)
    (hb : S.left.left.scalar .blocks=b) (hf : S.left.right.left.scalar .factor=q) :
    ∃ t≤(b+widths.length)*22+39+(b+widths.length)*total widths b q*7+
        220*(b+widths.length+total widths b q+p+1)^4, ∃ T,
      Runs (storageBound Reg Arr M) (program p) S t T ∧ T.Bounded M ∧
      KernelProgram.Represents p (total widths b q) 0
        (SelectorMatrix.word (selectors widths b q) (total widths b q))
        (data p widths b q) T.right.right := by
  have hlen : (selectors widths b q).length=b+widths.length := by
    simp [selectors,sizes,ArrayScaledOffsets.scaled,RingDimensions.dimensions]
  obtain ⟨t,ht,U,metadata,hUB,hUdim,hUsize,hUtotal,hUoffsets⟩ :=
    InputCoordinateMetadata.program_runs widths b q M hq hM hsize hv S.left bounded.left hws hb hf
  have first := metadata.left_bounded bounded
  let V := U.join S.right
  have hVB : V.Bounded M := hUB.join bounded.right
  obtain ⟨prepared,hWB⟩ := atoms_runs hVB setup (by simp [setup,ValidAtoms,Atom.Valid,Atom.SmallResult])
  let W := applyAtoms setup V
  have hs : W.right.left.array .selectors=selectors widths b q := by
    simpa [W,setup,applyAtoms,Atom.apply,Store.setScalar,Store.setArray,Store.right,V,Store.join,
      selectors,sizes,-Sum.elim_update_left,-Sum.elim_update_right] using hUoffsets
  have hn : W.right.left.scalar .columns=total widths b q := by
    simpa [W,setup,applyAtoms,Atom.apply,Store.setScalar,Store.setArray,Store.right,V,Store.join,
      total,sizes,-Sum.elim_update_left,-Sum.elim_update_right] using hUtotal
  obtain ⟨u,hu,X,kernel,hXB,hrep⟩ := SelectorKernel.program_runs p (selectors widths b q)
    (total widths b q) M hp (by simpa only [hlen] using hmatrix) hpM hnM W.right hWB.right hs hn
  have finalRun := kernel.right_bounded hWB
  rw [hlen] at hu hrep
  refine ⟨t+(2+u),by omega,W.left.join X,first.seq (prepared.seq finalRun),hWB.left.join hXB,hrep⟩

end GroupWL.MachinePrograms.ChosenKernel
