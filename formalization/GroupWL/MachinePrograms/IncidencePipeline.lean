import GroupWL.SourceInputMetadata
import GroupWL.ChosenCoordinateEncoding
import GroupWL.FormMatrixComposition
import GroupWL.InternalWedgeEncoding
import GroupWL.MachinePrograms.SourceRadicalCollection

/-! Concrete composition of radical-table elimination and the chosen-space kernel.
The results expose the coordinate arrays needed by descriptor generation and matrix multiplication. -/
namespace GroupWL.MachinePrograms.ChosenKernel
open NatArrayLanguage
set_option synthInstance.maxSize 4096
set_option maxRecDepth 8192

theorem program_runs_metadata (p : ℕ) [NeZero p] (widths : List ℕ) (b q M : ℕ)
    (hp : 1<p) (hq : 1≤q) (hM : b+2≤M) (hsize : (b+widths.length)*(b+2)*q≤M)
    (hv : ∀ x∈widths,x≤b) (hmatrix : (b+widths.length)*total widths b q≤M)
    (hpM : p*p+p≤M) (hnM : total widths b q*total widths b q≤M)
    (S : State) (bounded : S.Bounded M) (hws : S.left.left.array .widths=widths)
    (hb : S.left.left.scalar .blocks=b) (hf : S.left.right.left.scalar .factor=q) :
    ∃ t≤(b+widths.length)*22+39+(b+widths.length)*total widths b q*7+
        220*(b+widths.length+total widths b q+p+1)^4, ∃ T,
      Runs (storageBound Reg Arr M) (program p) S t T ∧ T.Bounded M ∧
      T.left.left.array .output=RingDimensions.dimensions widths b ∧
      T.left.right.right.array .ranks=selectors widths b q ∧
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
  refine ⟨t+(2+u),by omega,W.left.join X,first.seq (prepared.seq finalRun),hWB.left.join hXB,?_,?_,hrep⟩
  · exact hUdim
  · exact hUoffsets

end GroupWL.MachinePrograms.ChosenKernel


namespace GroupWL.MachinePrograms.IncidencePipeline
open NatArrayLanguage ConstructiveIncidence SourceTableEncoding SourceLayout
set_option synthInstance.maxSize 8192
set_option maxRecDepth 8192

abbrev Reg := SourceRadicalTables.Reg ⊕ ChosenKernel.Reg
abbrev Arr := SourceRadicalTables.Arr ⊕ ChosenKernel.Arr
abbrev State := Store Reg Arr

def transfer : List (Atom Reg Arr) := [
  .copyArray (.inr (.inl (.inl .widths))) (.inl (.inr .widths)),
  .copy (.inr (.inl (.inl .blocks))) (.inl (.inr .blocks))]

def coordinates (p : ℕ) : Program Reg Arr :=
  .seq ((SourceRadicalTables.program p).map Sum.inl Sum.inl)
    (.seq (atoms transfer) ((ChosenKernel.program p).map Sum.inr Sum.inr))

variable {X E : Type} [FiniteCode X] [FiniteCode E] {r : ℕ} (p : ℕ) [Fact p.Prime]
  (C : ComparisonData (ZMod p) X E r) (L q : ℕ)
local instance : Fintype X := FiniteCode.fintype X
local instance : Fintype E := FiniteCode.fintype E
local instance : Fintype (C.Block L) := FiniteCode.fintype _
local instance : Fintype (C.Readout L) := FiniteCode.fintype _
local instance : DecidableEq (C.Block L) := (FiniteCode.equiv (α:=C.Block L)).decidableEq
local instance : DecidableEq (C.Readout L) := (FiniteCode.equiv (α:=C.Readout L)).decidableEq

local notation "A₀" => ComputableSource.affineSystem C (L:=L)
local notation "R₀" => ConstructiveSourceTensor.radicalCoordinates C L
local notation "nv" => blockCount p C L
local notation "nr" => readoutCount p C L
local notation "ni" => FiniteCode.size (OldInputIndex A₀ R₀ q)

def time (p b r n : ℕ) := r*(290*(b+p+4)^4+18)+9+2+
  ((b+r)*22+39+(b+r)*n*7+220*(b+r+n+p+1)^4)

structure Input (S : State) : Prop where
  scope : S.left.array (.inr .scope)=scopeTable p C L
  coefficients : S.left.array (.inr .coefficients)=coefficientTable p C L
  dimensions : S.left.array (.inr .dimensions)=readoutDimensions p C L
  blocks : S.left.scalar (.inr .blocks)=nv
  readouts : S.left.scalar (.inr .readouts)=nr
  frames : S.right.left.right.left.scalar .factor=q

structure Output (hq : 0<q) (S : State) : Prop where
  radicals : S.left.array (.inr .output)=radicalTable p C L
  widths : S.left.array (.inr .widths)=readoutWidths A₀ R₀
  dimensions : S.right.left.left.array .output=ringDimensions A₀ R₀
  offsets : S.right.left.right.right.array .ranks=inputOffsets A₀ R₀ q
  ambient : S.right.right.right.scalar (KernelProgram.wr .ambient)=ni
  width : S.right.right.right.scalar (KernelProgram.wr .width)=(chosenCoordinates A₀ R₀ q hq).dimension
  lift : S.right.right.right.array (KernelProgram.wa .lift)=
    MatrixEncoding.word (CachedElimination.ofLinear (chosenChart A₀ R₀ q hq).lift)

theorem coordinates_runs (hdim : ∀t,C.dim t≤2) (hq : 0<q) (M : ℕ)
    (radControl : 2*nv+2≤M) (fieldRoom : p*p+p≤M) (radSquare : nv*nv≤M)
    (radTable : nv*nr*nv≤M) (sizeRoom : (nv+nr)*(nv+2)*q≤M)
    (selectorRoom : (nv+nr)*ni≤M) (chosenRoom : ni*ni≤M)
    (S : State) (bounded : S.Bounded M) (input : Input p C L q S) :
    ∃t≤time p nv nr ni,∃T, Runs (storageBound Reg Arr M) (coordinates p) S t T ∧
      T.Bounded M ∧ Output p C L q hq T := by
  let ws := radicalWidths p C L
  have hlen : ws.length=nr := List.length_ofFn
  have hcanonical : ws=readoutWidths A₀ R₀ := radicalWidths_canonical p C L hdim
  have htotal : ChosenKernel.total ws nv q=ni := hcanonical ▸ chosenTotal_runtime A₀ R₀ q
  have dims : ∀i<nr,(readoutDimensions p C L)[i]?.getD 0≤2 := by
    intro i hi
    simpa only [readoutDimensions,List.getElem?_ofFn,hi,dif_pos,Option.getD_some]
      using readout_dimension_le p C L hdim ((FiniteCode.equiv (α:=C.Readout L)).symm ⟨i,hi⟩)
  obtain ⟨t,ht,U,rad,hUB,ready,radicals,widths⟩ := SourceRadicalTables.program_runs p
    (scopeTable p C L) (coefficientTable p C L) (readoutDimensions p C L) nv nr M
    (Fact.out : p.Prime).one_lt (by rw [scopeTable,List.length_ofFn])
    (by rw [coefficientTable,List.length_ofFn]) (coefficientTable_values p C L)
    (by rw [readoutDimensions,List.length_ofFn]) dims radControl fieldRoom radSquare radTable
    S.left bounded.left input.scope input.coefficients input.dimensions input.blocks input.readouts
  let V := U.join S.right
  have hVB := hUB.join bounded.right
  have hVblocks : U.scalar (.inr .blocks)=nv := ready.2.2.2.1
  obtain ⟨wire,hWB⟩ := atoms_runs hVB transfer (by simp [transfer,ValidAtoms,Atom.Valid,Atom.SmallResult])
  let W := applyAtoms transfer V
  have hws : W.right.left.left.array .widths=ws := widths
  have hblocks : W.right.left.left.scalar .blocks=nv := hVblocks
  have hframes : W.right.left.right.left.scalar .factor=q := input.frames
  obtain ⟨u,hu,D,kernel,hDB,dimensions,offsets,rep⟩ := ChosenKernel.program_runs_metadata p ws nv q M
    (Fact.out : p.Prime).one_lt hq (by omega) (by simpa only [hlen] using sizeRoom)
    (radicalWidths_le p C L) (by simpa only [hlen,htotal] using selectorRoom) fieldRoom
    (by simpa only [htotal] using chosenRoom) W.right hWB.right hws hblocks hframes
  have hrun := kernel.right_bounded hWB
  rw [hlen,htotal] at hu
  refine ⟨t+(2+u),by unfold time; omega,W.left.join D,(rad.left_bounded bounded).seq (wire.seq hrun),
    hWB.left.join hDB,?_,?_,?_,?_,?_,?_,?_⟩
  · exact radicals
  · exact widths.trans hcanonical
  · rw [hcanonical,←ringDimensions_runtime] at dimensions
    exact dimensions
  · rw [hcanonical,chosenSelectors_runtime A₀ R₀ q hq] at offsets
    refine offsets.trans ?_
    rw [scalarSelectors_offsets]
    simp [inputOffsets,inputOffset]
  · exact rep.ambient.trans htotal
  · have h := rep.width
    rw [hcanonical,chosenData_runtime p A₀ R₀ q hq] at h
    exact h
  · have h := rep.lift
    rw [hcanonical,chosenData_runtime p A₀ R₀ q hq] at h
    exact h

/-- Ordinary matrix multiplication specializes directly to the canonical restrictions of all forms. -/
theorem chosenForms_runs (hq : 0<q) (M : ℕ) (S : MatrixArithmetic.State) (bounded : S.Bounded M)
    (rows : S.scalar .rows=FiniteCode.size (FormIndex A₀ R₀ q)) (inner : S.scalar .inner=ni)
    (cols : S.scalar .cols=(chosenCoordinates A₀ R₀ q hq).dimension) (modulus : S.scalar .modulus=p)
    (left : S.array .left=formMatrix p A₀ R₀ q)
    (right : S.array .right=MatrixEncoding.word (CachedElimination.ofLinear (chosenChart A₀ R₀ q hq).lift))
    (fieldRoom : p*p+p≤M) (room : FiniteCode.size (FormIndex A₀ R₀ q)*(chosenCoordinates A₀ R₀ q hq).dimension≤M) :
    ∃t≤FiniteCode.size (FormIndex A₀ R₀ q)*(chosenCoordinates A₀ R₀ q hq).dimension*(12*ni+9)+7,∃T,
      Runs (storageBound MatrixArithmetic.Reg MatrixArithmetic.Arr M) MatrixArithmetic.multiply S t T ∧
      T.Bounded M ∧ T.array .output=chosenFormMatrix p A₀ R₀ q hq := by
  rw [chosenFormMatrix_product]
  exact MatrixEncoding.multiply_word_runs _ _ S M bounded rows inner cols modulus left right fieldRoom room

end GroupWL.MachinePrograms.IncidencePipeline
