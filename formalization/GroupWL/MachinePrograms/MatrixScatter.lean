import GroupWL.MachinePrograms.NatArrayCountedLoops
import GroupWL.MachinePrograms.NatArrayProofs
import GroupWL.MachinePrograms.NatArrayFrames

/-! Scatter the rows of a compact matrix into selected rows of a padded
matrix. The output may already contain other readout blocks. -/
namespace GroupWL.MachinePrograms.MatrixScatter
open NatArrayLanguage
set_option maxHeartbeats 1600000

inductive Reg where
  | total | index | remaining | one | width | stride | offset
  | row | column | block | address | value
  deriving DecidableEq,Fintype
inductive Arr where | input | neighbors | output deriving DecidableEq,Fintype
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def target (neighbors : List ℕ) (width stride offset i : ℕ) : ℕ :=
  (neighbors[i/width]?.getD 0)*stride+i%width+offset

def scatter (neighbors values initial : List ℕ) (width stride offset : ℕ) : ℕ → List ℕ
  | 0 => initial
  | i+1 => (scatter neighbors values initial width stride offset i).set
      (target neighbors width stride offset i) (values[i]?.getD 0)

@[simp] theorem scatter_length (neighbors values initial : List ℕ) (width stride offset n : ℕ) :
    (scatter neighbors values initial width stride offset n).length=initial.length := by
  induction n with
  | zero => rfl
  | succ n ih => simp [scatter,ih]

def bodyAtoms : List (Atom Reg Arr) := [
  .divmod .row .column .index .width,.read .block .neighbors .row,.read .value .input .index,
  .binary .mul .address .block .stride,.binary .add .address .address .column,
  .binary .add .address .address .offset,.write .output .address .value]

def program : Code := .seq (.atom (.const .one 1))
  (countedLoop .index .remaining .total .one (atoms bodyAtoms))

theorem program_runs (neighbors values initial : List ℕ) (rows width stride offset M : ℕ)
    (S : State) (bounded : S.Bounded M) (hM : 1≤M)
    (hinput : S.array .input=values) (hneighbors : S.array .neighbors=neighbors)
    (houtput : S.array .output=initial) (hn : S.scalar .total=rows*width)
    (hw : S.scalar .width=width) (hs : S.scalar .stride=stride) (ho : S.scalar .offset=offset)
    (hrows : rows≤neighbors.length) (hvalues : rows*width≤values.length)
    (htarget : ∀ i<rows*width, target neighbors width stride offset i< initial.length) :
    ∃ t≤rows*width*10+4, ∃ T, Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧
      T.array .input=values ∧ T.array .neighbors=neighbors ∧
      T.array .output=scatter neighbors values initial width stride offset (rows*width) := by
  have hnM : rows*width≤M := hn ▸ bounded.1 Reg.total
  let U := S.setScalar .one 1
  have hUB : U.Bounded M := bounded.setScalar _ hM
  have first : Runs (storageBound Reg Arr M) (.atom (.const .one 1)) S 1 U :=
    atom_runs bounded _ trivial hM
  let I (i : ℕ) (V : State) : Prop := V.Bounded M ∧
    V.array .input=values ∧ V.array .neighbors=neighbors ∧
    V.scalar .width=width ∧ V.scalar .stride=stride ∧ V.scalar .offset=offset ∧
    V.scalar .total=rows*width ∧ V.scalar .index=i ∧ V.scalar .remaining=rows*width-i ∧ V.scalar .one=1 ∧
    V.array .output=scatter neighbors values initial width stride offset i
  have copied : (U.setScalar .remaining (U.scalar .total)).Bounded M := hUB.setScalar _ (hUB.1 _)
  have start : I 0 ((U.setScalar .remaining (U.scalar .total)).setScalar .index 0) := by
    refine ⟨copied.setScalar _ (Nat.zero_le M),?_⟩
    simp [I,U,Store.setScalar,hinput,hneighbors,houtput,hn,hw,hs,ho,scatter]
  have control : ∀ i≤rows*width, ∀ V, I i V → V.scalar .index=i ∧
      V.scalar .remaining=rows*width-i ∧ V.scalar .one=1 ∧ V.size≤storageBound Reg Arr M := by
    intro i hi V hV
    exact ⟨hV.2.2.2.2.2.2.2.1,hV.2.2.2.2.2.2.2.2.1,hV.2.2.2.2.2.2.2.2.2.1,
      Store.size_le_of_bounded hV.1⟩
  have step : ∀ i<rows*width, ∀ V, I i V → ∃ t≤7, ∃ W,
      Runs (storageBound Reg Arr M) (atoms bodyAtoms) V t W ∧
      W.scalar .index=i ∧ W.scalar .remaining=rows*width-i ∧ W.scalar .one=1 ∧
      (W.setScalar .index (i+1)).size≤storageBound Reg Arr M ∧ I (i+1) (advance .index .remaining W) := by
    intro i hi V hV
    rcases hV with ⟨hVB,hVi,hVn,hVw,hVs,hVo,hVt,hVidx,hVrem,hVone,hVout⟩
    have hwp : 0<width := by nlinarith
    have hrow : i/width<neighbors.length :=
      ((Nat.div_lt_iff_lt_mul hwp).2 hi).trans_le hrows
    have hv : i<values.length := hi.trans_le hvalues
    have hlen : initial.length≤M := by
      have h := hVB.2.1 Arr.output
      simpa only [hVout,scatter_length] using h
    have haddr := htarget i hi
    have hwrite : target neighbors width stride offset i < (V.array .output).length := by
      simpa only [hVout,scatter_length] using haddr
    have hfinal : target neighbors width stride offset i≤M := haddr.le.trans hlen
    have hadd : (neighbors[i/width]?.getD 0)*stride+i%width≤M :=
      (Nat.le_add_right _ _).trans hfinal
    have hmul : (neighbors[i/width]?.getD 0)*stride≤M := (Nat.le_add_right _ _).trans hadd
    have valid : ValidAtoms M bodyAtoms V := by
      simp [bodyAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
        Store.setScalar,hVi,hVn,hVw,hVs,hVo,hVidx,hwp,hrow,hv]
      simpa only [target,List.getElem?_eq_getElem hrow,Option.getD_some] using
        And.intro hmul (And.intro hadd (And.intro hfinal hwrite))
    obtain ⟨run,hWB⟩ := atoms_runs hVB bodyAtoms valid
    let W := applyAtoms bodyAtoms V
    have hidx : W.scalar .index=i := (run.scalar_eq_of_not_mem .index (by decide)).trans hVidx
    have hrem : W.scalar .remaining=rows*width-i := (run.scalar_eq_of_not_mem .remaining (by decide)).trans hVrem
    have hone : W.scalar .one=1 := (run.scalar_eq_of_not_mem .one (by decide)).trans hVone
    have hnext : (advance .index .remaining W).Bounded M :=
      (hWB.setScalar _ (by rw [hidx]; omega)).setScalar _ ((Nat.sub_le _ _).trans (hWB.1 _))
    refine ⟨7,le_rfl,W,run,hidx,hrem,hone,Store.size_le_of_bounded (hWB.setScalar _ (by omega)),hnext,?_⟩
    simp [W,bodyAtoms,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,
      advance,hVi,hVn,hVw,hVs,hVo,hVt,hVidx,hVrem,hVone,hVout,scatter,target]
    omega
  obtain ⟨t,ht,T,last,hT⟩ := countedLoop_runs (storageBound Reg Arr M) .index .remaining .total .one
    (atoms bodyAtoms) (rows*width) 7 I U (Store.size_le_of_bounded hUB)
    (Store.size_le_of_bounded copied) start control (by decide) (by decide) step
  exact ⟨1+t,by omega,T,first.seq last,hT.1,hT.2.1,hT.2.2.1,hT.2.2.2.2.2.2.2.2.2.2⟩

end GroupWL.MachinePrograms.MatrixScatter
