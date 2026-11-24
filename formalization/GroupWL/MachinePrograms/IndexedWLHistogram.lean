import GroupWL.MachinePrograms.IndexedWL
import GroupWL.MachinePrograms.NatArrayFrames
import GroupWL.MachinePrograms.NatArrayCountedLoops

/-! Operational proof of the final histogram scans. -/
namespace GroupWL.MachinePrograms.IndexedWL
open NatArrayLanguage
open GroupWL.IndexedRefinement
set_option maxRecDepth 2048
set_option linter.unusedSimpArgs false

private def selectionAtoms (selection : Arr) (destination : Reg) : List (Atom Reg Arr) := [
  .read .selected selection .selectionIndex,
  .binary .add .matrixIndex .selected .rowBase,
  .read .temp .matrix .matrixIndex,
  .binary .add destination destination .temp]

def selectionBody (selection : Arr) (destination : Reg) : Code :=
  atoms (selectionAtoms selection destination)

theorem selectionBody_runs (selection : Arr) (destination : Reg)
    (hdestination : destination=.leftCount ∨ destination=.rightCount)
    (S : Store Reg Arr) (n m row index accumulated : ℕ)
    (R : Finset (Fin n×Fin n)) (selected : List (Fin n))
    (hbound : S.Bounded m) (hmatrix : S.array .matrix=matrixWord R)
    (hselection : S.array selection=selected.map Fin.val)
    (hindex : S.scalar .selectionIndex=index) (hrow : S.scalar .rowBase=n*row)
    (hdest : S.scalar destination=accumulated)
    (hrowlt : row<n) (hindexlt : index<selected.length)
    (hroom : n*n≤m) (hacc : accumulated+1≤m) :
    ∃ T, Runs (storageBound Reg Arr m) (selectionBody selection destination) S 4 T ∧
      T.Bounded m ∧
      T.scalar destination=accumulated+read (matrixWord R) ((selected[index]).val+n*row) := by
  let col := selected[index]
  have hcol : col.val<n := col.isLt
  have hcell : col.val+n*row<n*n := by
    exact (finProdFinEquiv (⟨row,hrowlt⟩,col)).isLt
  have hread : read (matrixWord R) (col.val+n*row)≤1 := by
    rw [matrixWord_read R ⟨row,hrowlt⟩ col]
    cases h : Decidable.decide ((⟨row,hrowlt⟩,col)∈R) <;> simp [boolNat]
  have hn : n≤m := by nlinarith
  have hd₁ : Reg.selected≠destination := by rcases hdestination with rfl|rfl <;> decide
  have hd₂ : Reg.matrixIndex≠destination := by rcases hdestination with rfl|rfl <;> decide
  have hd₃ : Reg.temp≠destination := by rcases hdestination with rfl|rfl <;> decide
  have hget : (selected.map Fin.val)[index]?.getD 0=col.val := by
    simp [List.getElem?_eq_getElem hindexlt,col]
  have hv : ValidAtoms m (selectionAtoms selection destination) S := by
    simp only [selectionAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,
      BinaryOp.eval,Store.setScalar,Function.update_apply]
    simp only [hindex,hselection,List.length_map]
    simp only [hget,hrow,hmatrix,hdest,Ne.symm hd₁,Ne.symm hd₂,Ne.symm hd₃,
      show Reg.rowBase≠Reg.selected by decide,if_false,if_true]
    simp only [matrixWord_length]
    change (index<selected.length) ∧ True ∧
      True ∧ col.val+n*row≤m ∧
      col.val+n*row<n*n ∧ True ∧
      True ∧ accumulated+read (matrixWord R) (col.val+n*row)≤m ∧ True
    exact ⟨hindexlt,trivial,trivial,(Nat.le_of_lt hcell).trans hroom,hcell,trivial,
      trivial,(Nat.add_le_add_left hread accumulated).trans hacc,trivial⟩
  obtain ⟨hr,hb⟩ := atoms_runs hbound (selectionAtoms selection destination) hv
  refine ⟨applyAtoms (selectionAtoms selection destination) S,hr,hb,?_⟩
  simp [applyAtoms,selectionAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,
    Function.update_apply,hindex,hselection,hget,hrow,hmatrix,hdest,
    hd₁,hd₂,hd₃,Ne.symm hd₁,Ne.symm hd₂,Ne.symm hd₃,
    IndexedRefinement.read,col,List.getElem?_eq_getElem hindexlt]


private def prefixCount {n : ℕ} (R : Finset (Fin n×Fin n)) (selected : List (Fin n))
    (row : Fin n) (i : ℕ) : ℕ :=
  IndexedRefinement.selectedCount n (matrixWord R) ((selected.take i).map Fin.val) row.val

private theorem prefixCount_le {n : ℕ} (R : Finset (Fin n×Fin n))
    (selected : List (Fin n)) (row : Fin n) (i : ℕ) : prefixCount R selected row i ≤ i := by
  rw [prefixCount,IndexedRefinement.selectedCount_correct]
  exact (Multiset.countP_le_card _ _).trans (by simp [Multiset.coe_card,List.length_take])

private theorem prefixCount_succ {n : ℕ} (R : Finset (Fin n×Fin n))
    (selected : List (Fin n)) (row : Fin n) (i : ℕ) (hi : i<selected.length) :
    prefixCount R selected row (i+1)=prefixCount R selected row i+
      IndexedRefinement.read (matrixWord R) ((selected[i]).val+n*row.val) := by
  unfold prefixCount IndexedRefinement.selectedCount
  rw [List.take_succ_eq_append_getElem hi]
  simp only [List.map_append,List.map_cons,List.map_nil,List.sum_append,List.sum_cons,
    List.sum_nil,Nat.add_zero]

private structure ScanInvariant {n : ℕ} (R : Finset (Fin n×Fin n))
    (selected : List (Fin n)) (row : Fin n) (selection : Arr) (destination : Reg)
    (m i : ℕ) (S : Store Reg Arr) : Prop where
  bounded : S.Bounded m
  index_eq : S.scalar .selectionIndex=i
  remaining_eq : S.scalar .selectionTodo=selected.length-i
  one_eq : S.scalar .one=1
  rowBase_eq : S.scalar .rowBase=n*row.val
  destination_eq : S.scalar destination=prefixCount R selected row i
  matrix_eq : S.array .matrix=matrixWord R
  selection_eq : S.array selection=selected.map Fin.val

theorem selectionLoop_runs (selection : Arr) (destination : Reg)
    (hdestination : destination=.leftCount ∨ destination=.rightCount)
    (S : Store Reg Arr) (n m : ℕ) (row : Fin n)
    (R : Finset (Fin n×Fin n)) (selected : List (Fin n))
    (hbound : S.Bounded m) (hmatrix : S.array .matrix=matrixWord R)
    (hselection : S.array selection=selected.map Fin.val)
    (hsize : S.scalar .selectionSize=selected.length)
    (hone : S.scalar .one=1) (hrow : S.scalar .rowBase=n*row.val)
    (hdest : S.scalar destination=0) (hroom : n*n≤m) (hlen : selected.length≤m) :
    ∃ t≤7*selected.length+3,∃ T,
      Runs (storageBound Reg Arr m)
        (loop .selectionIndex .selectionTodo .selectionSize (selectionBody selection destination)) S t T ∧
      T.Bounded m ∧ T.scalar destination=
        IndexedRefinement.selectedCount n (matrixWord R) (selected.map Fin.val) row.val := by
  have hdi : destination≠Reg.selectionIndex := by rcases hdestination with rfl|rfl <;> decide
  have hdr : destination≠Reg.selectionTodo := by rcases hdestination with rfl|rfl <;> decide
  let I := ScanInvariant R selected row selection destination m
  have hcopy : (S.setScalar .selectionTodo (S.scalar .selectionSize)).Bounded m :=
    hbound.setScalar _ (by simpa [hsize] using hlen)
  have hstart : I 0 ((S.setScalar .selectionTodo (S.scalar .selectionSize)).setScalar .selectionIndex 0) := by
    refine ⟨hcopy.setScalar _ (Nat.zero_le _),?_,?_,?_,?_,?_,?_,?_⟩
    · simp
    · simp [hsize]
    · simp [hone]
    · simp [hrow]
    · simpa [prefixCount,IndexedRefinement.selectedCount,hdi,hdr] using hdest
    · simpa using hmatrix
    · simpa using hselection
  have hcontrol : ∀ i≤selected.length,∀ T,I i T →
      T.scalar .selectionIndex=i ∧ T.scalar .selectionTodo=selected.length-i ∧
      T.scalar .one=1 ∧ T.size≤storageBound Reg Arr m := by
    intro i _ T hT
    exact ⟨hT.index_eq,hT.remaining_eq,hT.one_eq,Store.size_le_of_bounded hT.bounded⟩
  have hstep : ∀ i<selected.length,∀ T,I i T →
      ∃ t≤4,∃ U,Runs (storageBound Reg Arr m) (selectionBody selection destination) T t U ∧
        U.scalar .selectionIndex=i ∧ U.scalar .selectionTodo=selected.length-i ∧ U.scalar .one=1 ∧
        (U.setScalar .selectionIndex (i+1)).size≤storageBound Reg Arr m ∧
        I (i+1) (advance .selectionIndex .selectionTodo U) := by
    intro i hi T hT
    have hacc : prefixCount R selected row i+1≤m := by
      have := prefixCount_le R selected row i
      omega
    obtain ⟨U,run,hU,heq⟩ := selectionBody_runs selection destination hdestination T n m row.val i
      (prefixCount R selected row i) R selected hT.bounded hT.matrix_eq hT.selection_eq
      hT.index_eq hT.rowBase_eq hT.destination_eq row.isLt hi hroom hacc
    have scalarFrame (r : Reg) (hr : r≠destination) (h₁ : r≠.selected)
        (h₂ : r≠.matrixIndex) (h₃ : r≠.temp) : U.scalar r=T.scalar r := by
      apply run.scalar_eq_of_not_mem
      simp [selectionBody,atoms,selectionAtoms,NatArrayLanguage.sequence,Program.scalarWrites,Atom.scalarWrites,
        hr,h₁,h₂,h₃]
    have hiU : U.scalar .selectionIndex=i := by
      rw [scalarFrame .selectionIndex (Ne.symm hdi) (by decide) (by decide) (by decide)]
      exact hT.index_eq
    have hrU : U.scalar .selectionTodo=selected.length-i := by
      rw [scalarFrame .selectionTodo (Ne.symm hdr) (by decide) (by decide) (by decide)]
      exact hT.remaining_eq
    have h1U : U.scalar .one=1 := by
      rw [scalarFrame .one (by rcases hdestination with rfl|rfl <;> decide)
        (by decide) (by decide) (by decide)]
      exact hT.one_eq
    have hbU : U.scalar .rowBase=n*row.val := by
      rw [scalarFrame .rowBase (by rcases hdestination with rfl|rfl <;> decide)
        (by decide) (by decide) (by decide)]
      exact hT.rowBase_eq
    have arrayFrame (a : Arr) : U.array a=T.array a := by
      apply run.array_eq_of_not_mem
      simp [selectionBody,atoms,selectionAtoms,NatArrayLanguage.sequence,Program.arrayWrites,Atom.arrayWrites]
    have hmid := hU.setScalar Reg.selectionIndex (show i+1≤m by omega)
    refine ⟨4,le_rfl,U,run,hiU,hrU,h1U,Store.size_le_of_bounded hmid,?_⟩
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [advance,hiU] using hmid.setScalar Reg.selectionTodo
        (show U.scalar .selectionTodo-1≤m by rw [hrU]; omega)
    · simp [advance,hiU]
    · simp [advance,hrU]; omega
    · simpa [advance] using h1U
    · simpa [advance] using hbU
    · rw [prefixCount_succ R selected row i hi]
      simpa [advance,hdi,hdr] using heq
    · simpa [advance,arrayFrame] using hT.matrix_eq
    · simpa [advance,arrayFrame] using hT.selection_eq
  obtain ⟨t,ht,T,run,hT⟩ := countedLoop_runs (storageBound Reg Arr m)
    .selectionIndex .selectionTodo .selectionSize .one (selectionBody selection destination)
    selected.length 4 I S (Store.size_le_of_bounded hbound) (Store.size_le_of_bounded hcopy)
    hstart hcontrol (by decide) (by decide) hstep
  refine ⟨t,by omega,T,run,hT.bounded,?_⟩
  simpa [prefixCount] using hT.destination_eq


private def selectionPrelude (selection : Arr) (destination : Reg) : List (Atom Reg Arr) := [
  .const destination 0, .arrayLength .selectionSize selection,
  .binary .mul .rowBase .n .row]

theorem selectedCount_runs (selection : Arr) (destination : Reg)
    (hdestination : destination=.leftCount ∨ destination=.rightCount)
    (S : Store Reg Arr) (n m : ℕ) (row : Fin n)
    (R : Finset (Fin n×Fin n)) (selected : List (Fin n))
    (hbound : S.Bounded m) (hmatrix : S.array .matrix=matrixWord R)
    (hselection : S.array selection=selected.map Fin.val)
    (hn : S.scalar .n=n) (hrow : S.scalar .row=row.val)
    (hone : S.scalar .one=1) (hroom : n*n≤m) (hlen : selected.length≤m) :
    ∃ t≤7*selected.length+6,∃ T,
      Runs (storageBound Reg Arr m) (selectedCount selection destination) S t T ∧
      T.Bounded m ∧ T.scalar destination=
        IndexedRefinement.selectedCount n (matrixWord R) (selected.map Fin.val) row.val := by
  have hdst (r : Reg) (hr : r=.n ∨ r=.row ∨ r=.one ∨ r=.selectionSize ∨ r=.rowBase) :
      r≠destination := by
    rcases hdestination with rfl|rfl <;> rcases hr with rfl|rfl|rfl|rfl|rfl <;> decide
  have hmul : n*row.val≤m := (Nat.mul_le_mul_left n (Nat.le_of_lt row.isLt)).trans hroom
  have hvalid : ValidAtoms m (selectionPrelude selection destination) S := by
    simp [selectionPrelude,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,hn,hrow,hselection,hdst .n (by simp),hdst .row (by simp),hmul]
  obtain ⟨pre,hpre⟩ := atoms_runs hbound (selectionPrelude selection destination) hvalid
  let S₁ := applyAtoms (selectionPrelude selection destination) S
  have hmatrix₁ : S₁.array .matrix=matrixWord R := by
    simpa [S₁,applyAtoms,selectionPrelude,Atom.apply] using hmatrix
  have hselection₁ : S₁.array selection=selected.map Fin.val := by
    simpa [S₁,applyAtoms,selectionPrelude,Atom.apply] using hselection
  have hsize₁ : S₁.scalar .selectionSize=selected.length := by
    simp [S₁,applyAtoms,selectionPrelude,Atom.apply,Store.setScalar,hselection]
  have hone₁ : S₁.scalar .one=1 := by
    simp [S₁,applyAtoms,selectionPrelude,Atom.apply,Store.setScalar,hdst .one (by simp),hone]
  have hrow₁ : S₁.scalar .rowBase=n*row.val := by
    simp [S₁,applyAtoms,selectionPrelude,Atom.apply,Store.setScalar,BinaryOp.eval,
      hdst .n (by simp),hdst .row (by simp),hn,hrow]
  have hdest₁ : S₁.scalar destination=0 := by
    simp [S₁,applyAtoms,selectionPrelude,Atom.apply,Store.setScalar,
      Ne.symm (hdst .rowBase (by simp)),Ne.symm (hdst .selectionSize (by simp))]
  obtain ⟨t,ht,T,run,hT,heq⟩ := selectionLoop_runs selection destination hdestination S₁ n m row
    R selected hpre hmatrix₁ hselection₁ hsize₁ hone₁ hrow₁ hdest₁ hroom hlen
  have rest : Runs (storageBound Reg Arr m)
      (NatArrayLanguage.sequence [loop .selectionIndex .selectionTodo .selectionSize
        (selectionBody selection destination)]) S₁ (t+0) T :=
    .seq run (.skip run.end_bound)
  have full := sequence_append_runs ((selectionPrelude selection destination).map .atom)
    [loop .selectionIndex .selectionTodo .selectionSize (selectionBody selection destination)] pre rest
  refine ⟨3+t,by omega,T,?_,hT,heq⟩
  simpa only [selectionPrelude,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
    List.length_cons,List.length_nil,Nat.add_zero,selectionBody,selectionAtoms,atoms]
    using full



def histogramBody : Code := NatArrayLanguage.sequence [
  selectedCount .leftSelection .leftCount, selectedCount .rightSelection .rightCount,
  atom (.binary .eq .flag .leftCount .rightCount),
  atom (.binary .mul .result .result .flag)]

private def comparisonAtoms : List (Atom Reg Arr) := [
  .binary .eq .flag .leftCount .rightCount,
  .binary .mul .result .result .flag]

theorem histogramBody_runs (S : Store Reg Arr) (n m : ℕ) (row : Fin n)
    (R : Finset (Fin n×Fin n)) (left right : List (Fin n))
    (hbound : S.Bounded m) (hmatrix : S.array .matrix=matrixWord R)
    (hleft : S.array .leftSelection=left.map Fin.val)
    (hright : S.array .rightSelection=right.map Fin.val)
    (hn : S.scalar .n=n) (hrow : S.scalar .row=row.val) (hone : S.scalar .one=1)
    (hresult : S.scalar .result≤1) (hroom : n*n≤m) (hm : 1≤m)
    (hlenL : left.length≤m) (hlenR : right.length≤m) :
    ∃ t≤7*(left.length+right.length)+14,∃ T,
      Runs (storageBound Reg Arr m) histogramBody S t T ∧ T.Bounded m ∧
      T.scalar .result = S.scalar .result *
        boolNat (Decidable.decide (
          IndexedRefinement.selectedCount n (matrixWord R) (left.map Fin.val) row.val =
          IndexedRefinement.selectedCount n (matrixWord R) (right.map Fin.val) row.val)) := by
  obtain ⟨tL,htL,U,runL,hU,eqL⟩ := selectedCount_runs .leftSelection .leftCount (Or.inl rfl)
    S n m row R left hbound hmatrix hleft hn hrow hone hroom hlenL
  have frameL (r : Reg) (h : r∉(selectedCount .leftSelection .leftCount).scalarWrites) :
      U.scalar r=S.scalar r := runL.scalar_eq_of_not_mem r h
  have arraysL (a : Arr) : U.array a=S.array a := runL.array_eq_of_not_mem a (by
    simp [selectedCount,loop,atom,NatArrayLanguage.sequence,Program.arrayWrites,Atom.arrayWrites])
  obtain ⟨tR,htR,V,runR,hV,eqR⟩ := selectedCount_runs .rightSelection .rightCount (Or.inr rfl)
    U n m row R right hU (by simpa [arraysL] using hmatrix) (by simpa [arraysL] using hright)
    (by rw [frameL .n (by decide)]; exact hn)
    (by rw [frameL .row (by decide)]; exact hrow)
    (by rw [frameL .one (by decide)]; exact hone) hroom hlenR
  have frameR (r : Reg) (h : r∉(selectedCount .rightSelection .rightCount).scalarWrites) :
      V.scalar r=U.scalar r := runR.scalar_eq_of_not_mem r h
  have hleftV : V.scalar .leftCount=
      IndexedRefinement.selectedCount n (matrixWord R) (left.map Fin.val) row.val := by
    rw [frameR .leftCount (by decide),eqL]
  have hresultV : V.scalar .result=S.scalar .result := by
    rw [frameR .result (by decide),frameL .result (by decide)]
  have hbool : (if V.scalar .leftCount=V.scalar .rightCount then 1 else 0)≤1 := by split <;> omega
  have hproduct : V.scalar .result*(if V.scalar .leftCount=V.scalar .rightCount then 1 else 0)≤m := by
    rw [hresultV]
    exact (Nat.mul_le_mul hresult hbool).trans (by simpa using hm)
  have hvalid : ValidAtoms m comparisonAtoms V := by
    simp [comparisonAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,Store.setScalar,
      BinaryOp.eval,hproduct,hbool.trans hm]
    simpa only [mul_ite,mul_one,mul_zero] using hproduct
  obtain ⟨finish,hfinish⟩ := atoms_runs hV comparisonAtoms hvalid
  let T := applyAtoms comparisonAtoms V
  have both : Runs (storageBound Reg Arr m)
      (NatArrayLanguage.sequence [selectedCount .leftSelection .leftCount,
        selectedCount .rightSelection .rightCount]) S (tL+(tR+0)) V :=
    .seq runL (.seq runR (.skip runR.end_bound))
  have full := sequence_append_runs
    [selectedCount .leftSelection .leftCount,selectedCount .rightSelection .rightCount]
    (comparisonAtoms.map .atom) both finish
  refine ⟨tL+tR+2,by omega,T,?_,hfinish,?_⟩
  · simpa only [histogramBody,comparisonAtoms,List.map_cons,List.map_nil,List.cons_append,
      List.nil_append,List.length_cons,List.length_nil,Nat.add_zero] using full
  · simp [T,applyAtoms,comparisonAtoms,Atom.apply,Store.setScalar,BinaryOp.eval,
      hresultV,hleftV,eqR,boolNat]



private def histogramPrefix {n : ℕ} (R : Finset (Fin n×Fin n))
    (left right : List (Fin n)) (i : ℕ) : ℕ :=
  boolNat ((List.range i).all (fun row =>
    IndexedRefinement.selectedCount n (matrixWord R) (left.map Fin.val) row ==
    IndexedRefinement.selectedCount n (matrixWord R) (right.map Fin.val) row))

private theorem histogramPrefix_le {n : ℕ} (R : Finset (Fin n×Fin n))
    (left right : List (Fin n)) (i : ℕ) : histogramPrefix R left right i≤1 := by
  unfold histogramPrefix boolNat
  split <;> omega

private theorem histogramPrefix_succ {n : ℕ} (R : Finset (Fin n×Fin n))
    (left right : List (Fin n)) (i : ℕ) :
    histogramPrefix R left right (i+1) = histogramPrefix R left right i *
      boolNat (Decidable.decide (
        IndexedRefinement.selectedCount n (matrixWord R) (left.map Fin.val) i =
        IndexedRefinement.selectedCount n (matrixWord R) (right.map Fin.val) i)) := by
  unfold histogramPrefix
  rw [List.range_succ]
  simp only [List.all_append,List.all_cons,List.all_nil,Bool.and_true]
  generalize (List.range i).all _ = flag
  by_cases h : IndexedRefinement.selectedCount n (matrixWord R) (left.map Fin.val) i =
      IndexedRefinement.selectedCount n (matrixWord R) (right.map Fin.val) i
  · simp [h,boolNat]
  · simp [h,boolNat]

private structure HistogramInvariant {n : ℕ} (R : Finset (Fin n×Fin n))
    (left right : List (Fin n)) (m i : ℕ) (S : Store Reg Arr) : Prop where
  bounded : S.Bounded m
  index_eq : S.scalar .row=i
  remaining_eq : S.scalar .rowTodo=n-i
  one_eq : S.scalar .one=1
  n_eq : S.scalar .n=n
  result_eq : S.scalar .result=histogramPrefix R left right i
  matrix_eq : S.array .matrix=matrixWord R
  left_eq : S.array .leftSelection=left.map Fin.val
  right_eq : S.array .rightSelection=right.map Fin.val

/-- Exact operational correctness of the final class-histogram test. -/
theorem histogram_runs (S : Store Reg Arr) (n m : ℕ)
    (R : Finset (Fin n×Fin n)) (left right : List (Fin n))
    (hbound : S.Bounded m) (hmatrix : S.array .matrix=matrixWord R)
    (hleft : S.array .leftSelection=left.map Fin.val)
    (hright : S.array .rightSelection=right.map Fin.val)
    (hn : S.scalar .n=n) (hone : S.scalar .one=1)
    (hroom : n*n≤m) (hm : 1≤m) (hlenL : left.length≤m) (hlenR : right.length≤m) :
    ∃ t≤n*(7*(left.length+right.length)+17)+4,∃ T,
      Runs (storageBound Reg Arr m) histogram S t T ∧ T.Bounded m ∧
      T.scalar .result = boolNat (IndexedRefinement.sameHistogram n (matrixWord R)
        (left.map Fin.val) (right.map Fin.val)) := by
  have hnsmall : n≤m := (Nat.le_mul_self n).trans hroom
  let S₀ := S.setScalar .result 1
  have hs₀ : S₀.Bounded m := hbound.setScalar .result hm
  have init : Runs (storageBound Reg Arr m) (atom (.const .result 1)) S 1 S₀ :=
    atom_runs hbound _ trivial hm
  let I := HistogramInvariant R left right m
  have hcopy : (S₀.setScalar .rowTodo (S₀.scalar .n)).Bounded m :=
    hs₀.setScalar _ (by simpa [S₀,hn] using hnsmall)
  have hstart : I 0 ((S₀.setScalar .rowTodo (S₀.scalar .n)).setScalar .row 0) := by
    refine ⟨hcopy.setScalar _ (Nat.zero_le _),?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simp
    · simp [S₀,hn]
    · simp [S₀,hone]
    · simp [S₀,hn]
    · simp [S₀,histogramPrefix,boolNat]
    · simpa [S₀] using hmatrix
    · simpa [S₀] using hleft
    · simpa [S₀] using hright
  have hcontrol : ∀ i≤n,∀ T,I i T →
      T.scalar .row=i ∧ T.scalar .rowTodo=n-i ∧ T.scalar .one=1 ∧
      T.size≤storageBound Reg Arr m := by
    intro i hi T hT
    exact ⟨hT.index_eq,hT.remaining_eq,hT.one_eq,Store.size_le_of_bounded hT.bounded⟩
  have hstep : ∀ i<n,∀ T,I i T →
      ∃ t≤7*(left.length+right.length)+14,∃ U,
        Runs (storageBound Reg Arr m) histogramBody T t U ∧
        U.scalar .row=i ∧ U.scalar .rowTodo=n-i ∧ U.scalar .one=1 ∧
        (U.setScalar .row (i+1)).size≤storageBound Reg Arr m ∧
        I (i+1) (advance .row .rowTodo U) := by
    intro i hi T hT
    obtain ⟨t,ht,U,run,hU,heq⟩ := histogramBody_runs T n m ⟨i,hi⟩ R left right
      hT.bounded hT.matrix_eq hT.left_eq hT.right_eq hT.n_eq hT.index_eq hT.one_eq
      (by rw [hT.result_eq]; exact histogramPrefix_le R left right i) hroom hm hlenL hlenR
    have scalarFrame (r : Reg) (h : r∉histogramBody.scalarWrites) :
        U.scalar r=T.scalar r := run.scalar_eq_of_not_mem r h
    have hiU : U.scalar .row=i := by rw [scalarFrame .row (by decide),hT.index_eq]
    have hrU : U.scalar .rowTodo=n-i := by rw [scalarFrame .rowTodo (by decide),hT.remaining_eq]
    have h1U : U.scalar .one=1 := by rw [scalarFrame .one (by decide),hT.one_eq]
    have hnU : U.scalar .n=n := by rw [scalarFrame .n (by decide),hT.n_eq]
    have arrays (a : Arr) : U.array a=T.array a := run.array_eq_of_not_mem a (by
      simp [histogramBody,selectedCount,loop,atom,NatArrayLanguage.sequence,
        Program.arrayWrites,Atom.arrayWrites])
    have hmid := hU.setScalar Reg.row (show i+1≤m by omega)
    refine ⟨t,ht,U,run,hiU,hrU,h1U,Store.size_le_of_bounded hmid,?_⟩
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [advance,hiU] using hmid.setScalar Reg.rowTodo
        (show U.scalar .rowTodo-1≤m by rw [hrU]; omega)
    · simp [advance,hiU]
    · simp [advance,hrU]; omega
    · simpa [advance] using h1U
    · simpa [advance] using hnU
    · rw [histogramPrefix_succ]
      simpa [advance,hT.result_eq] using heq
    · simpa [advance,arrays] using hT.matrix_eq
    · simpa [advance,arrays] using hT.left_eq
    · simpa [advance,arrays] using hT.right_eq
  obtain ⟨t,ht,T,run,hT⟩ := countedLoop_runs (storageBound Reg Arr m)
    .row .rowTodo .n .one histogramBody n (7*(left.length+right.length)+14) I S₀
    (Store.size_le_of_bounded hs₀) (Store.size_le_of_bounded hcopy)
    hstart hcontrol (by decide) (by decide) hstep
  refine ⟨1+t,by nlinarith,T,?_,hT.bounded,?_⟩
  · change Runs _ (NatArrayLanguage.sequence [atom (.const .result 1),
      loop .row .rowTodo .n histogramBody]) S (1+t) T
    simpa using Runs.seq init (Runs.seq run (Runs.skip run.end_bound))
  · exact hT.result_eq


end GroupWL.MachinePrograms.IndexedWL

