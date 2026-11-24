import GroupWL.MachinePrograms.SourceReadoutClient
import GroupWL.MachinePrograms.KernelCost

/-! The operational readout-radical client includes incidence enumeration,
relation materialization, and Gaussian elimination. -/
namespace GroupWL.MachinePrograms.SourceRadicalClient
open NatArrayLanguage
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048

abbrev Reg := SourceReadoutClient.Reg ⊕ KernelProgram.Reg
abbrev Arr := SourceReadoutClient.Arr ⊕ KernelProgram.Arr
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def setup (p : ℕ) : List (Atom Reg Arr) := [
  .copy (.inr (KernelProgram.wr .ambient)) (.inl (.inr .degree)),
  .copyArray (.inr (KernelProgram.wa .input)) (.inl (.inr .output)),
  .const (.inr (KernelProgram.wr .modulus)) p]

def program (p : ℕ) : Code := .seq (SourceReadoutClient.program.map Sum.inl Sum.inl)
  (.seq (atoms (setup p)) ((KernelProgram.program p).map Sum.inr Sum.inr))

def relation (scope coefficients : List ℕ) (b r j d : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin (d*(SourceNeighbors.selected scope r j b).length) =>
    SourceRelationMatrix.entry coefficients (SourceNeighbors.selected scope r j b) r j
      (SourceNeighbors.selected scope r j b).length i.val)

theorem relation_values (scope coefficients : List ℕ) (b r j d p : ℕ)
    (hp : 0<p) (values : ∀ x∈coefficients,x<p) : ∀ x∈relation scope coefficients b r j d,x<p := by
  intro x hx
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  have hread (k : ℕ) : coefficients[k]?.getD 0<p := by
    cases h : coefficients[k]? with
    | none => exact hp
    | some x => exact values x (List.mem_of_getElem? h)
  exact hread _

theorem program_runs_full (p : ℕ) [NeZero p] (scope coefficients : List ℕ) (b r j d M : ℕ)
    (hp : 1<p) (hj : j<r) (hd : d≤2) (hscope : b*r≤scope.length)
    (hcoeff : b*r*2≤coefficients.length) (values : ∀ x∈coefficients,x<p)
    (hM : 2*b+2≤M) (hpM : p*p+p≤M) (hbM : b*b≤M)
    (S : State) (bounded : S.Bounded M)
    (hinput : S.left.left.array .input=scope) (hblocks : S.left.left.scalar .length=b)
    (hstride : S.left.left.scalar .stride=r) (hoffset : S.left.left.scalar .offset=j)
    (hc : S.left.right.array .coefficients=coefficients) (hr : S.left.right.scalar .readouts=r)
    (hj' : S.left.right.scalar .readout=j) (hdim : S.left.right.scalar .total=d)
    (hrows : S.right.scalar (KernelProgram.wr .rows)=d) :
    ∃ t ≤ b*9+d*(SourceNeighbors.selected scope r j b).length*11+20+
        220*(d+(SourceNeighbors.selected scope r j b).length+p+1)^4, ∃ T,
      Runs (storageBound Reg Arr M) (program p) S t T ∧ T.Bounded M ∧
      KernelProgram.Represents p (SourceNeighbors.selected scope r j b).length 0
        (relation scope coefficients b r j d)
        (KernelProgram.executeRows (relation scope coefficients b r j d) p
          (SourceNeighbors.selected scope r j b).length d
          (KernelProgram.initial (SourceNeighbors.selected scope r j b).length)) T.right ∧
      (T.left.left.array .output).length=b ∧
      (T.left.left.array .output).take (SourceNeighbors.selected scope r j b).length=
        SourceNeighbors.selected scope r j b := by
  let g := (SourceNeighbors.selected scope r j b).length
  have hg : g≤b := SourceNeighbors.selected_length_le _ _ _ _
  obtain ⟨t,ht,U,source,hUB,hUi,hUc,hUg,hUout,hUlen,hUprefix⟩ := SourceReadoutClient.program_runs_full
    scope coefficients b r j d M hj hd hscope hcoeff hM S.left bounded.left
    hinput hblocks hstride hoffset hc hr hj' hdim
  have sourceRun := source.left_bounded bounded
  let V := U.join S.right
  have hVB : V.Bounded M := hUB.join bounded.right
  have hvalid : ValidAtoms M (setup p) V := by
    simp [setup,ValidAtoms,Atom.Valid,Atom.SmallResult]
    omega
  obtain ⟨prepared,hWB⟩ := atoms_runs hVB (setup p) hvalid
  let W := applyAtoms (setup p) V
  have hWL : W.left=U := by
    apply Store.ext
    · intro rr; rfl
    · intro aa; rfl
  have ambient : W.right.scalar (KernelProgram.wr .ambient)=g := by
    simpa [W,setup,applyAtoms,Atom.apply,Store.setScalar,Store.setArray,Store.right,V,Store.join,
      -Sum.elim_update_left,-Sum.elim_update_right] using hUg
  have rows : W.right.scalar (KernelProgram.wr .rows)=d := by
    simpa [W,setup,applyAtoms,Atom.apply,Store.setScalar,Store.setArray,Store.right,V,Store.join,
      -Sum.elim_update_left,-Sum.elim_update_right] using hrows
  have modulus : W.right.scalar (KernelProgram.wr .modulus)=p := by
    simp [W,setup,applyAtoms,Atom.apply,Store.setScalar,Store.setArray,Store.right]
  have input : W.right.array (KernelProgram.wa .input)=relation scope coefficients b r j d := by
    simpa [W,setup,applyAtoms,Atom.apply,Store.setScalar,Store.setArray,Store.right,V,Store.join,
      relation,-Sum.elim_update_left,-Sum.elim_update_right] using hUout
  obtain ⟨u,hu,X,kernel,hXB,hrep⟩ := KernelProgram.program_runs p g d M
    (relation scope coefficients b r j d) W.right hWB.right ambient rows modulus input hp hpM
    ((Nat.mul_le_mul hg hg).trans hbM) (List.length_ofFn)
    (relation_values scope coefficients b r j d p (by omega) values)
  have finalRun := kernel.right_bounded hWB
  refine ⟨t+(3+u),?_,W.left.join X,sourceRun.seq (prepared.seq finalRun),hWB.left.join hXB,hrep,?_,?_⟩
  · have hu' := hu.trans (KernelProgram.programCost_le d g p)
    change u≤220*(d+(SourceNeighbors.selected scope r j b).length+p+1)^4 at hu'
    omega
  · change (W.left.left.array .output).length=b
    rw [hWL]
    exact hUlen
  · change (W.left.left.array .output).take (SourceNeighbors.selected scope r j b).length=_
    rw [hWL]
    simpa only [hUg] using hUprefix

theorem program_runs (p : ℕ) [NeZero p] (scope coefficients : List ℕ) (b r j d M : ℕ)
    (hp : 1<p) (hj : j<r) (hd : d≤2) (hscope : b*r≤scope.length)
    (hcoeff : b*r*2≤coefficients.length) (values : ∀ x∈coefficients,x<p)
    (hM : 2*b+2≤M) (hpM : p*p+p≤M) (hbM : b*b≤M)
    (S : State) (bounded : S.Bounded M)
    (hinput : S.left.left.array .input=scope) (hblocks : S.left.left.scalar .length=b)
    (hstride : S.left.left.scalar .stride=r) (hoffset : S.left.left.scalar .offset=j)
    (hc : S.left.right.array .coefficients=coefficients) (hr : S.left.right.scalar .readouts=r)
    (hj' : S.left.right.scalar .readout=j) (hdim : S.left.right.scalar .total=d)
    (hrows : S.right.scalar (KernelProgram.wr .rows)=d) :
    ∃ t ≤ b*9+d*(SourceNeighbors.selected scope r j b).length*11+20+
        220*(d+(SourceNeighbors.selected scope r j b).length+p+1)^4, ∃ T,
      Runs (storageBound Reg Arr M) (program p) S t T ∧ T.Bounded M ∧
      KernelProgram.Represents p (SourceNeighbors.selected scope r j b).length 0
        (relation scope coefficients b r j d)
        (KernelProgram.executeRows (relation scope coefficients b r j d) p
          (SourceNeighbors.selected scope r j b).length d
          (KernelProgram.initial (SourceNeighbors.selected scope r j b).length)) T.right := by
  obtain ⟨t,ht,T,run,hT,hrep,hlen,hprefix⟩ := program_runs_full p scope coefficients b r j d M
    hp hj hd hscope hcoeff values hM hpM hbM S bounded hinput hblocks hstride hoffset hc hr hj' hdim hrows
  exact ⟨t,ht,T,run,hT,hrep⟩

end GroupWL.MachinePrograms.SourceRadicalClient
