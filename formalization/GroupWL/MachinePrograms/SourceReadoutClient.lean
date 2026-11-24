import GroupWL.MachinePrograms.SourceNeighbors
import GroupWL.MachinePrograms.SourceRelationMatrix
import GroupWL.MachinePrograms.NatArrayComponents

/-! A complete local source client: scan one scope column and materialize
its relation matrix with the same increasing neighbor enumeration. -/
namespace GroupWL.MachinePrograms.SourceReadoutClient
open NatArrayLanguage
set_option maxHeartbeats 1400000
set_option maxRecDepth 5000

abbrev Reg := SourceNeighbors.Reg ⊕ SourceRelationMatrix.Reg
abbrev Arr := SourceNeighbors.Arr ⊕ SourceRelationMatrix.Arr
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def setup : List (Atom Reg Arr) := [
  .copy (.inr .degree) (.inl .count),
  .binary .mul (.inr .total) (.inr .total) (.inr .degree),
  .copyArray (.inr .neighbors) (.inl .output),
  .const (.inr .two) 2]

def program : Code := .seq (SourceNeighbors.program.map Sum.inl Sum.inl)
  (.seq (atoms setup) (SourceRelationMatrix.program.map Sum.inr Sum.inr))

theorem selected_read_lt (xs : List ℕ) (r j b : ℕ) (i : ℕ)
    (hi : i<(SourceNeighbors.selected xs r j b).length) :
    (SourceNeighbors.selected xs r j b)[i]?.getD 0<b := by
  rw [List.getElem?_eq_getElem hi,Option.getD_some]
  have hmem := List.getElem_mem (l:=SourceNeighbors.selected xs r j b) hi
  exact List.mem_range.mp (List.mem_filter.mp hmem).1

theorem prefix_read (ns xs : List ℕ) (g : ℕ) (h : ns.take g=xs)
    (i : ℕ) (hi : i<g) : ns[i]?.getD 0=xs[i]?.getD 0 := by
  rw [← h]
  simp [List.getElem?_take,hi]

theorem program_runs_full (scope coefficients : List ℕ) (b r j d M : ℕ)
    (hj : j<r) (hd : d≤2) (hscope : b*r≤scope.length)
    (hcoeff : b*r*2≤coefficients.length) (hM : 2*b+2≤M)
    (S : State) (bounded : S.Bounded M)
    (hinput : S.left.array .input=scope) (hblocks : S.left.scalar .length=b)
    (hstride : S.left.scalar .stride=r) (hoffset : S.left.scalar .offset=j)
    (hc : S.right.array .coefficients=coefficients) (hr : S.right.scalar .readouts=r)
    (hj' : S.right.scalar .readout=j) (hdim : S.right.scalar .total=d) :
    ∃ t ≤ b*9+d*(SourceNeighbors.selected scope r j b).length*11+17, ∃ T,
      Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧
      T.left.array .input=scope ∧ T.right.array .coefficients=coefficients ∧
      T.right.scalar .degree=(SourceNeighbors.selected scope r j b).length ∧
      T.right.array .output=List.ofFn
        (fun i : Fin (d*(SourceNeighbors.selected scope r j b).length) =>
          SourceRelationMatrix.entry coefficients (SourceNeighbors.selected scope r j b) r j
            (SourceNeighbors.selected scope r j b).length i.val) ∧
      (T.left.array .output).length=b ∧
      (T.left.array .output).take (T.right.scalar .degree)=SourceNeighbors.selected scope r j b := by
  let word := SourceNeighbors.selected scope r j b
  have hg : word.length≤b := SourceNeighbors.selected_length_le _ _ _ _
  have hread : ∀ i<b, i*r+j<scope.length := by
    intro i hi
    apply lt_of_lt_of_le _ hscope
    calc i*r+j < (i+1)*r := by nlinarith
         _ ≤ b*r := Nat.mul_le_mul_right _ (by omega)
  obtain ⟨t,ht,U,scan,hUB,hUi,hUc,hUlen,hUtake⟩ :=
    SourceNeighbors.program_runs S.left scope b r j M bounded.left (by omega)
      hinput hblocks hstride hoffset hread
  have scanned := scan.left_bounded bounded
  let V := U.join S.right
  have hVB : V.Bounded M := hUB.join bounded.right
  have hprod : d*word.length≤M := by nlinarith
  have hsvalid : ValidAtoms M setup V := by
    simpa [setup,V,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,Store.setArray,Store.join,hdim,hUc,-Sum.elim_update_left,-Sum.elim_update_right] using And.intro hprod (by omega : 2≤M)
  obtain ⟨prepared,hWB⟩ := atoms_runs hVB setup hsvalid
  let W := applyAtoms setup V
  have hWL : W.left=U := by
    apply Store.ext
    · intro rr; rfl
    · intro aa; rfl
  have hready : SourceRelationMatrix.Ready coefficients (U.array .output) r j d word.length W.right := by
    simp [SourceRelationMatrix.Ready,W,setup,applyAtoms,Atom.apply,BinaryOp.eval,
      Store.setScalar,Store.setArray,Store.right,V,Store.join,hUc,-Sum.elim_update_left,-Sum.elim_update_right]
    exact ⟨hc,hr,hj',rfl,congrArg (fun a => a*word.length) hdim⟩
  have hcount : word.length≤(U.array .output).length := by rw [hUlen]; exact hg
  have hprefix : (U.array .output).take word.length=word := by simpa only [hUc] using hUtake
  have hvalues : ∀ i<word.length, (U.array .output)[i]?.getD 0<b := by
    intro i hi
    rw [prefix_read _ _ _ hprefix i hi]
    exact selected_read_lt scope r j b i hi
  obtain ⟨u,hu,X,gather,hXB,hXR,hXout⟩ := SourceRelationMatrix.program_runs
    coefficients (U.array .output) b r j d word.length M hj hd hcoeff hcount hvalues
    W.right hready hWB.right (by omega)
  have gathered := gather.right_bounded hWB
  let T := W.left.join X
  change u≤d*(SourceNeighbors.selected scope r j b).length*11+6 at hu
  refine ⟨t+(4+u),by omega,T,scanned.seq (prepared.seq gathered),hWB.left.join hXB,?_,hXR.1,hXR.2.2.2.2.1,?_,?_,?_⟩
  · simpa [T,W,setup,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,
      Store.left,V,Store.join,-Sum.elim_update_left,-Sum.elim_update_right] using hUi
  · change X.array .output = _
    rw [hXout]
    congr 1
    funext i
    have hgpos : 0<word.length := by nlinarith [i.isLt]
    unfold SourceRelationMatrix.entry
    rw [prefix_read _ _ _ hprefix (i.val%word.length) (Nat.mod_lt _ hgpos)]
  · change (W.left.array .output).length=b
    rw [hWL]
    exact hUlen
  · change (W.left.array .output).take (X.scalar .degree)=_
    rw [hWL,hXR.2.2.2.2.1]
    exact hprefix

theorem program_runs (scope coefficients : List ℕ) (b r j d M : ℕ)
    (hj : j<r) (hd : d≤2) (hscope : b*r≤scope.length)
    (hcoeff : b*r*2≤coefficients.length) (hM : 2*b+2≤M)
    (S : State) (bounded : S.Bounded M)
    (hinput : S.left.array .input=scope) (hblocks : S.left.scalar .length=b)
    (hstride : S.left.scalar .stride=r) (hoffset : S.left.scalar .offset=j)
    (hc : S.right.array .coefficients=coefficients) (hr : S.right.scalar .readouts=r)
    (hj' : S.right.scalar .readout=j) (hdim : S.right.scalar .total=d) :
    ∃ t ≤ b*9+d*(SourceNeighbors.selected scope r j b).length*11+17, ∃ T,
      Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧
      T.left.array .input=scope ∧ T.right.array .coefficients=coefficients ∧
      T.right.scalar .degree=(SourceNeighbors.selected scope r j b).length ∧
      T.right.array .output=List.ofFn
        (fun i : Fin (d*(SourceNeighbors.selected scope r j b).length) =>
          SourceRelationMatrix.entry coefficients (SourceNeighbors.selected scope r j b) r j
            (SourceNeighbors.selected scope r j b).length i.val) := by
  obtain ⟨t,ht,T,run,hT,hi,hc',hg,ho,hlen,hprefix⟩ := program_runs_full scope coefficients b r j d M
    hj hd hscope hcoeff hM S bounded hinput hblocks hstride hoffset hc hr hj' hdim
  exact ⟨t,ht,T,run,hT,hi,hc',hg,ho⟩

end GroupWL.MachinePrograms.SourceReadoutClient
