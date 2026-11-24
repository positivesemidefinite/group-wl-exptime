import GroupWL.MachinePrograms.SourceRadicalData

/-! A readout column is fully compiled into its padded radical-lift slots. -/
namespace GroupWL.MachinePrograms.SourceRadicalColumn
open NatArrayLanguage
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096

abbrev Reg := SourceRadicalClient.Reg ⊕ MatrixScatter.Reg
abbrev Arr := SourceRadicalClient.Arr ⊕ MatrixScatter.Arr
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def setup : List (Atom Reg Arr) := [
  .copy (.inr .width) (.inl (.inr (KernelProgram.wr .width))),
  .binary .mul (.inr .total) (.inl (.inr (KernelProgram.wr .ambient))) (.inr .width),
  .copyArray (.inr .input) (.inl (.inr (KernelProgram.wa .lift))),
  .copyArray (.inr .neighbors) (.inl (.inl (.inl .output)))]

def program (p : ℕ) : Code := .seq ((SourceRadicalClient.program p).map Sum.inl Sum.inl)
  (.seq (atoms setup) (MatrixScatter.program.map Sum.inr Sum.inr))

def update (p : ℕ) (scope coefficients initial : List ℕ) (b r j d stride offset : ℕ) : List ℕ :=
  let D := SourceRadicalClient.data p scope coefficients b r j d
  let ns := SourceNeighbors.selected scope r j b
  MatrixScatter.scatter ns D.lift initial D.width stride offset (ns.length*D.width)

theorem program_runs (p : ℕ) [NeZero p] (scope coefficients initial : List ℕ)
    (b r j d stride offset M : ℕ)
    (hp : 1<p) (hj : j<r) (hd : d≤2) (hscope : b*r≤scope.length)
    (hcoeff : b*r*2≤coefficients.length) (values : ∀ x∈coefficients,x<p)
    (hM : 2*b+2≤M) (hpM : p*p+p≤M) (hbM : b*b≤M)
    (S : State) (bounded : S.Bounded M)
    (hinput : S.left.left.left.array .input=scope) (hblocks : S.left.left.left.scalar .length=b)
    (hstride : S.left.left.left.scalar .stride=r) (hoffset : S.left.left.left.scalar .offset=j)
    (hc : S.left.left.right.array .coefficients=coefficients) (hr : S.left.left.right.scalar .readouts=r)
    (hj' : S.left.left.right.scalar .readout=j) (hdim : S.left.left.right.scalar .total=d)
    (hrows : S.left.right.scalar (KernelProgram.wr .rows)=d)
    (houtput : S.right.array .output=initial) (hs : S.right.scalar .stride=stride)
    (ho : S.right.scalar .offset=offset)
    (htarget : ∀ i<(SourceNeighbors.selected scope r j b).length*
        (SourceRadicalClient.data p scope coefficients b r j d).width,
      MatrixScatter.target (SourceNeighbors.selected scope r j b)
        (SourceRadicalClient.data p scope coefficients b r j d).width stride offset i < initial.length) :
    ∃ t ≤ b*9+d*(SourceNeighbors.selected scope r j b).length*11+28+
        220*(d+(SourceNeighbors.selected scope r j b).length+p+1)^4+
        (SourceNeighbors.selected scope r j b).length*
          (SourceRadicalClient.data p scope coefficients b r j d).width*10, ∃ T,
      Runs (storageBound Reg Arr M) (program p) S t T ∧ T.Bounded M ∧
      T.right.array .output=update p scope coefficients initial b r j d stride offset ∧
      T.left.right.scalar (KernelProgram.wr .width)=
        (SourceRadicalClient.data p scope coefficients b r j d).width := by
  let ns := SourceNeighbors.selected scope r j b
  let D := SourceRadicalClient.data p scope coefficients b r j d
  have hdv : D.Valid p ns.length := SourceRadicalClient.data_valid p scope coefficients b r j d hp
  have hg : ns.length≤b := SourceNeighbors.selected_length_le _ _ _ _
  have hprod : ns.length*D.width≤M :=
    (Nat.mul_le_mul hg (hdv.width.trans hg)).trans hbM
  obtain ⟨t,ht,U,source,hUB,hrep,hnslen,hprefix⟩ := SourceRadicalClient.program_runs_full p
    scope coefficients b r j d M hp hj hd hscope hcoeff values hM hpM hbM S.left bounded.left
    hinput hblocks hstride hoffset hc hr hj' hdim hrows
  have sourceRun := source.left_bounded bounded
  change KernelProgram.Represents p ns.length 0 (SourceRadicalClient.relation scope coefficients b r j d) D U.right at hrep
  let V := U.join S.right
  have hVB : V.Bounded M := hUB.join bounded.right
  have hvalid : ValidAtoms M setup V := by
    simp [setup,V,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,Store.setArray,Store.join,-Sum.elim_update_left,-Sum.elim_update_right]
    change U.right.scalar (KernelProgram.wr .ambient)*U.right.scalar (KernelProgram.wr .width)≤M
    rw [hrep.ambient,hrep.width]
    exact hprod
  obtain ⟨prepared,hWB⟩ := atoms_runs hVB setup hvalid
  let W := applyAtoms setup V
  have hWL : W.left=U := by
    apply Store.ext
    · intro rr; rfl
    · intro aa; rfl
  have wi : W.right.array .input=D.lift := by
    simpa [W,setup,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,
      Store.right,V,Store.join,-Sum.elim_update_left,-Sum.elim_update_right] using hrep.lift
  have wn : W.right.array .neighbors=U.left.left.array .output := rfl
  have wo : W.right.array .output=initial := houtput
  have wt : W.right.scalar .total=ns.length*D.width := by
    simpa [W,setup,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,
      Store.right,V,Store.join,-Sum.elim_update_left,-Sum.elim_update_right] using
      congrArg₂ Nat.mul hrep.ambient hrep.width
  have ww : W.right.scalar .width=D.width := by
    simpa [W,setup,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,
      Store.right,V,Store.join,-Sum.elim_update_left,-Sum.elim_update_right] using hrep.width
  have ws : W.right.scalar .stride=stride := hs
  have woff : W.right.scalar .offset=offset := ho
  have hsame : ∀ i<ns.length*D.width,
      (U.left.left.array .output)[i/D.width]?.getD 0=ns[i/D.width]?.getD 0 := by
    intro i hi
    have hw : 0<D.width := by nlinarith
    exact SourceReadoutClient.prefix_read _ _ _ hprefix _ ((Nat.div_lt_iff_lt_mul hw).2 hi)
  have htargets : ∀ i<ns.length*D.width,
      MatrixScatter.target (U.left.left.array .output) D.width stride offset i < initial.length := by
    intro i hi
    simpa only [MatrixScatter.target,hsame i hi] using htarget i hi
  obtain ⟨u,hu,X,scatter,hXB,hXi,hXn,hXout⟩ := MatrixScatter.program_runs
    (U.left.left.array .output) D.lift initial ns.length D.width stride offset M W.right hWB.right
    (by omega) wi wn wo wt ww ws woff (by rw [hnslen]; exact hg) hdv.liftLength.ge htargets
  have finalRun := scatter.right_bounded hWB
  refine ⟨t+(4+u),?_,W.left.join X,sourceRun.seq (prepared.seq finalRun),hWB.left.join hXB,?_,?_⟩
  · change u≤(SourceNeighbors.selected scope r j b).length*
      (SourceRadicalClient.data p scope coefficients b r j d).width*10+4 at hu
    omega
  · exact hXout.trans (MatrixScatter.scatter_congr_neighbors _ _ _ _ _ _ _ _ hsame)
  · change W.left.right.scalar (KernelProgram.wr .width)=D.width
    rw [hWL]
    exact hrep.width

end GroupWL.MachinePrograms.SourceRadicalColumn
