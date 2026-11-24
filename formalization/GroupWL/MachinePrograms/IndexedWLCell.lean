import GroupWL.MachinePrograms.IndexedWLCount
import GroupWL.MachinePrograms.IndexedWLDecode

/-! Bounded execution of the pairwise relation entries. -/
namespace GroupWL.MachinePrograms.IndexedWL
open NatArrayLanguage GroupWL.IndexedRefinement
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

structure Room (n k b m : ℕ) : Prop where
  matrix : n*n≤m
  target : (n*b)*k≤m
  pair : n*b≤m
  arity : k≤m
  width : b≤m
  one : 1≤m
  vectors : n^k≤m

structure Context {n k b : ℕ} (D : Data n k b) (R : Finset (Fin n×Fin n))
    (m : ℕ) (S : Store Reg Arr) : Prop where
  bounded : S.Bounded m
  n_eq : S.scalar .n=n
  arity_eq : S.scalar .arity=k
  width_eq : S.scalar .width=b
  one_eq : S.scalar .one=1
  matrix_eq : S.array .matrix=matrixWord R
  fanouts_eq : S.array .fanouts=D.fanoutWord
  targets_eq : S.array .targets=D.targetWord
  vector_length : (S.array .vector).length=k

def PreservesContext (p : Code) : Prop :=
  Reg.n∉p.scalarWrites ∧ Reg.arity∉p.scalarWrites ∧ Reg.width∉p.scalarWrites ∧
  Reg.one∉p.scalarWrites ∧ Arr.matrix∉p.arrayWrites ∧
  Arr.fanouts∉p.arrayWrites ∧ Arr.targets∉p.arrayWrites

instance (p : Code) : Decidable (PreservesContext p) := by
  unfold PreservesContext
  infer_instance

theorem Context.of_run {n k b m : ℕ} {D : Data n k b} {R : Finset (Fin n×Fin n)}
    {S T : Store Reg Arr} {p : Code} {time : ℕ} (ctx : Context D R m S)
    (run : Runs (storageBound Reg Arr m) p S time T) (hbound : T.Bounded m)
    (hlen : (T.array .vector).length=k) (hp : PreservesContext p) : Context D R m T := by
  refine ⟨hbound,?_,?_,?_,?_,?_,?_,?_,hlen⟩
  · rw [run.scalar_eq_of_not_mem .n hp.1]; exact ctx.n_eq
  · rw [run.scalar_eq_of_not_mem .arity hp.2.1]; exact ctx.arity_eq
  · rw [run.scalar_eq_of_not_mem .width hp.2.2.1]; exact ctx.width_eq
  · rw [run.scalar_eq_of_not_mem .one hp.2.2.2.1]; exact ctx.one_eq
  · rw [run.array_eq_of_not_mem .matrix hp.2.2.2.2.1]; exact ctx.matrix_eq
  · rw [run.array_eq_of_not_mem .fanouts hp.2.2.2.2.2.1]; exact ctx.fanouts_eq
  · rw [run.array_eq_of_not_mem .targets hp.2.2.2.2.2.2]; exact ctx.targets_eq

def valueBody : Code := NatArrayLanguage.sequence [
  decodeVector, countAt .row .leftCount, countAt .column .rightCount,
  atom (.binary .eq .flag .leftCount .rightCount),
  atom (.binary .mul .entry .entry .flag)]

private def valueComparison : List (Atom Reg Arr) := [
  .binary .eq .flag .leftCount .rightCount, .binary .mul .entry .entry .flag]

theorem valueBody_runs {n k b m : ℕ} (D : Data n k b) (R : Finset (Fin n×Fin n))
    (a c : Fin n) (v : Fin (n^k)) (S : Store Reg Arr) (room : Room n k b m)
    (ctx : Context D R m S) (hrow : S.scalar .row=a.val) (hcolumn : S.scalar .column=c.val)
    (hvalue : S.scalar .value=v.val) (hentry : S.scalar .entry≤1) :
    ∃ t≤2*b*(10*k+10)+6*k+20,∃ T,
      Runs (storageBound Reg Arr m) valueBody S t T ∧ Context D R m T ∧
      T.scalar .entry=S.scalar .entry*boolNat (Decidable.decide (
        vectorCount D (matrixWord R) a.val v.val=vectorCount D (matrixWord R) c.val v.val)) := by
  obtain ⟨td,htd,U,rd,hU,vecU⟩ := decodeVector_runs S m n k v.val ctx.bounded
    ctx.n_eq D.positive ctx.arity_eq hvalue ctx.one_eq ctx.vector_length
  have ctxU : Context D R m U := ctx.of_run rd hU (by simp [vecU]) (by decide)
  have rowU : U.scalar .row=a.val := by rw [rd.scalar_eq_of_not_mem .row (by decide),hrow]
  have columnU : U.scalar .column=c.val := by rw [rd.scalar_eq_of_not_mem .column (by decide),hcolumn]
  obtain ⟨tl,htl,V,rl,hV,leftV⟩ := countAt_runs D R a v .row .leftCount (Or.inl rfl) (Or.inl rfl)
    U m hU ctxU.matrix_eq ctxU.fanouts_eq ctxU.targets_eq vecU ctxU.n_eq ctxU.arity_eq ctxU.width_eq
    ctxU.one_eq rowU room.matrix room.target room.pair room.arity room.width room.one
  have vecV : V.array .vector=vectorWord n k v.val := by
    rw [rl.array_eq_of_not_mem .vector (by decide),vecU]
  have ctxV : Context D R m V := ctxU.of_run rl hV (by simp [vecV]) (by decide)
  have columnV : V.scalar .column=c.val := by rw [rl.scalar_eq_of_not_mem .column (by decide),columnU]
  obtain ⟨tr,htr,W,rr,hW,rightW⟩ := countAt_runs D R c v .column .rightCount (Or.inr rfl) (Or.inr rfl)
    V m hV ctxV.matrix_eq ctxV.fanouts_eq ctxV.targets_eq vecV ctxV.n_eq ctxV.arity_eq ctxV.width_eq
    ctxV.one_eq columnV room.matrix room.target room.pair room.arity room.width room.one
  have leftW : W.scalar .leftCount=vectorCount D (matrixWord R) a.val v.val := by
    rw [rr.scalar_eq_of_not_mem .leftCount (by decide),leftV]
  have entryW : W.scalar .entry=S.scalar .entry := by
    rw [rr.scalar_eq_of_not_mem .entry (by decide),rl.scalar_eq_of_not_mem .entry (by decide),
      rd.scalar_eq_of_not_mem .entry (by decide)]
  have hbool : (if W.scalar .leftCount=W.scalar .rightCount then 1 else 0)≤1 := by split <;> omega
  have hproduct : W.scalar .entry*(if W.scalar .leftCount=W.scalar .rightCount then 1 else 0)≤m := by
    rw [entryW]
    exact (Nat.mul_le_mul hentry hbool).trans (by simpa using room.one)
  have valid : ValidAtoms m valueComparison W := by
    simp [valueComparison,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,Store.setScalar,
      BinaryOp.eval,hbool.trans room.one]
    simpa only [mul_ite,mul_one,mul_zero] using hproduct
  obtain ⟨finish,hfinish⟩ := atoms_runs hW valueComparison valid
  let T := applyAtoms valueComparison W
  have prefixRun : Runs (storageBound Reg Arr m)
      (NatArrayLanguage.sequence [decodeVector,countAt .row .leftCount,countAt .column .rightCount])
      S (td+(tl+(tr+0))) W := .seq rd (.seq rl (.seq rr (.skip rr.end_bound)))
  have full := sequence_append_runs [decodeVector,countAt .row .leftCount,countAt .column .rightCount]
    (valueComparison.map .atom) prefixRun finish
  have full' : Runs (storageBound Reg Arr m) valueBody S (td+tl+tr+2) T := by
    convert full using 1 <;> simp [valueBody,valueComparison,atom] <;> omega
  have vecT : T.array .vector=vectorWord n k v.val := by
    rw [finish.array_eq_of_not_mem .vector (by decide),rr.array_eq_of_not_mem .vector (by decide),vecV]
  refine ⟨td+tl+tr+2,by nlinarith,T,full',ctx.of_run full' hfinish (by simp [vecT]) (by decide),?_⟩
  simp [T,applyAtoms,valueComparison,Atom.apply,Store.setScalar,BinaryOp.eval,
    entryW,leftW,rightW,boolNat]


theorem Context.scalarUpdate {n k b m : ℕ} {D : Data n k b} {R : Finset (Fin n×Fin n)}
    {S : Store Reg Arr} (ctx : Context D R m S) (r : Reg) (v : ℕ) (hv : v≤m)
    (hr : r≠.n ∧ r≠.arity ∧ r≠.width ∧ r≠.one) : Context D R m (S.setScalar r v) := by
  refine ⟨ctx.bounded.setScalar r hv,?_,?_,?_,?_,ctx.matrix_eq,ctx.fanouts_eq,ctx.targets_eq,ctx.vector_length⟩
  · simpa [Ne.symm hr.1] using ctx.n_eq
  · simpa [Ne.symm hr.2.1] using ctx.arity_eq
  · simpa [Ne.symm hr.2.2.1] using ctx.width_eq
  · simpa [Ne.symm hr.2.2.2] using ctx.one_eq

def valueBranch : Code := .branch .entry valueBody .skip

theorem valueBranch_runs {n k b m : ℕ} (D : Data n k b) (R : Finset (Fin n×Fin n))
    (a c : Fin n) (v : Fin (n^k)) (S : Store Reg Arr) (room : Room n k b m)
    (ctx : Context D R m S) (hrow : S.scalar .row=a.val) (hcolumn : S.scalar .column=c.val)
    (hvalue : S.scalar .value=v.val) (hentry : S.scalar .entry≤1) :
    ∃ t≤2*b*(10*k+10)+6*k+21,∃ T,
      Runs (storageBound Reg Arr m) valueBranch S t T ∧ Context D R m T ∧
      T.scalar .entry=S.scalar .entry*boolNat (Decidable.decide (
        vectorCount D (matrixWord R) a.val v.val=vectorCount D (matrixWord R) c.val v.val)) := by
  by_cases hz : S.scalar .entry=0
  · exact ⟨1,by omega,S,.branch_zero hz (.skip (Store.size_le_of_bounded ctx.bounded)),ctx,by simp [hz]⟩
  · obtain ⟨t,ht,T,run,hT,heq⟩ := valueBody_runs D R a c v S room ctx hrow hcolumn hvalue hentry
    exact ⟨t+1,by omega,T,.branch_nonzero hz run,hT,heq⟩

private def entryPrefix {n k b : ℕ} (D : Data n k b) (R : Finset (Fin n×Fin n))
    (a c : Fin n) (i : ℕ) : ℕ :=
  boolNat (Decidable.decide ((a,c)∈R) &&
    (List.range i).all (fun v => vectorCount D (matrixWord R) a.val v==vectorCount D (matrixWord R) c.val v))

private theorem entryPrefix_le {n k b : ℕ} (D : Data n k b) (R : Finset (Fin n×Fin n))
    (a c : Fin n) (i : ℕ) : entryPrefix D R a c i ≤ 1 := by
  unfold entryPrefix boolNat; split <;> omega

private theorem entryPrefix_zero {n k b : ℕ} (D : Data n k b) (R : Finset (Fin n×Fin n))
    (a c : Fin n) : entryPrefix D R a c 0=boolNat (Decidable.decide ((a,c)∈R)) := by
  simp [entryPrefix]

private theorem entryPrefix_succ {n k b : ℕ} (D : Data n k b) (R : Finset (Fin n×Fin n))
    (a c : Fin n) (i : ℕ) :
    entryPrefix D R a c (i+1)=entryPrefix D R a c i*boolNat (Decidable.decide (
      vectorCount D (matrixWord R) a.val i=vectorCount D (matrixWord R) c.val i)) := by
  unfold entryPrefix
  rw [List.range_succ]
  simp only [List.all_append,List.all_cons,List.all_nil,Bool.and_true]
  generalize Decidable.decide ((a,c)∈R)=initial
  generalize (List.range i).all _=previous
  by_cases h : vectorCount D (matrixWord R) a.val i=vectorCount D (matrixWord R) c.val i
  · simp [h,boolNat]
  · simp [h,boolNat]

private theorem entryPrefix_full {n k b : ℕ} (D : Data n k b) (R : Finset (Fin n×Fin n))
    (a c : Fin n) : entryPrefix D R a c (n^k)=nextEntry D (matrixWord R) a.val c.val := by
  rw [nextEntry,matrixWord_read]
  simp [entryPrefix,boolNat,List.all_eq_true,List.mem_range]

private structure ValueInvariant {n k b : ℕ} (D : Data n k b)
    (R : Finset (Fin n×Fin n)) (a c : Fin n) (m i : ℕ) (S : Store Reg Arr) : Prop where
  context : Context D R m S
  row_eq : S.scalar .row=a.val
  column_eq : S.scalar .column=c.val
  index_eq : S.scalar .value=i
  remaining_eq : S.scalar .valueTodo=n^k-i
  entry_eq : S.scalar .entry=entryPrefix D R a c i

theorem valueLoop_runs {n k b m : ℕ} (D : Data n k b) (R : Finset (Fin n×Fin n))
    (a c : Fin n) (S : Store Reg Arr) (room : Room n k b m) (ctx : Context D R m S)
    (hrow : S.scalar .row=a.val) (hcolumn : S.scalar .column=c.val)
    (hlimit : S.scalar .vectorLimit=n^k)
    (hentry : S.scalar .entry=boolNat (Decidable.decide ((a,c)∈R))) :
    ∃ t≤n^k*(2*b*(10*k+10)+6*k+24)+3,∃ T,
      Runs (storageBound Reg Arr m) (loop .value .valueTodo .vectorLimit valueBranch) S t T ∧
      Context D R m T ∧ T.scalar .entry=nextEntry D (matrixWord R) a.val c.val := by
  let I := ValueInvariant D R a c m
  have ctxCopy : Context D R m (S.setScalar .valueTodo (S.scalar .vectorLimit)) :=
    ctx.scalarUpdate _ _ (by simpa [hlimit] using room.vectors) (by decide)
  have ctxStart := ctxCopy.scalarUpdate Reg.value 0 (Nat.zero_le _) (by decide)
  have start : I 0 ((S.setScalar .valueTodo (S.scalar .vectorLimit)).setScalar .value 0) := by
    refine ⟨ctxStart,?_,?_,?_,?_,?_⟩
    · simp [hrow]
    · simp [hcolumn]
    · simp
    · simp [hlimit]
    · simpa [entryPrefix_zero] using hentry
  have control : ∀ i≤n^k,∀ T,I i T →
      T.scalar .value=i ∧ T.scalar .valueTodo=n^k-i ∧ T.scalar .one=1 ∧
      T.size≤storageBound Reg Arr m := by
    intro i hi T hT
    exact ⟨hT.index_eq,hT.remaining_eq,hT.context.one_eq,Store.size_le_of_bounded hT.context.bounded⟩
  have step : ∀ i<n^k,∀ T,I i T →
      ∃ t≤2*b*(10*k+10)+6*k+21,∃ U,
        Runs (storageBound Reg Arr m) valueBranch T t U ∧
        U.scalar .value=i ∧ U.scalar .valueTodo=n^k-i ∧ U.scalar .one=1 ∧
        (U.setScalar .value (i+1)).size≤storageBound Reg Arr m ∧
        I (i+1) (advance .value .valueTodo U) := by
    intro i hi T hT
    obtain ⟨t,ht,U,run,ctxU,heq⟩ := valueBranch_runs D R a c ⟨i,hi⟩ T room hT.context
      hT.row_eq hT.column_eq hT.index_eq (by rw [hT.entry_eq]; exact entryPrefix_le D R a c i)
    have hiU : U.scalar .value=i := by rw [run.scalar_eq_of_not_mem .value (by decide),hT.index_eq]
    have hrU : U.scalar .valueTodo=n^k-i := by rw [run.scalar_eq_of_not_mem .valueTodo (by decide),hT.remaining_eq]
    have rowU : U.scalar .row=a.val := by rw [run.scalar_eq_of_not_mem .row (by decide),hT.row_eq]
    have colU : U.scalar .column=c.val := by rw [run.scalar_eq_of_not_mem .column (by decide),hT.column_eq]
    have ctxMid := ctxU.scalarUpdate Reg.value (i+1) (show i+1≤m by have := room.vectors; omega) (by decide)
    have ctxNext := ctxMid.scalarUpdate Reg.valueTodo (U.scalar .valueTodo-1)
      (show U.scalar .valueTodo-1≤m by rw [hrU]; have := room.vectors; omega) (by decide)
    refine ⟨t,ht,U,run,hiU,hrU,ctxU.one_eq,Store.size_le_of_bounded ctxMid.bounded,?_⟩
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · simpa [advance,hiU] using ctxNext
    · simpa [advance] using rowU
    · simpa [advance] using colU
    · simp [advance,hiU]
    · simp [advance,hrU]; omega
    · rw [entryPrefix_succ]
      simpa [advance,hT.entry_eq] using heq
  obtain ⟨t,ht,T,run,hT⟩ := countedLoop_runs (storageBound Reg Arr m) .value .valueTodo .vectorLimit .one
    valueBranch (n^k) (2*b*(10*k+10)+6*k+21) I S (Store.size_le_of_bounded ctx.bounded)
    (Store.size_le_of_bounded ctxCopy.bounded) start control (by decide) (by decide) step
  exact ⟨t,by nlinarith,T,run,hT.context,(hT.entry_eq.trans (entryPrefix_full D R a c))⟩



private def cellPrelude : List (Atom Reg Arr) := [
  .binary .mul .cellIndex .n .row,
  .binary .add .cellIndex .column .cellIndex,
  .read .entry .matrix .cellIndex]

/-- Compute and store one entry of the next materialized relation matrix. -/
theorem nextCell_runs {n k b m : ℕ} (D : Data n k b) (R : Finset (Fin n×Fin n))
    (a c : Fin n) (S : Store Reg Arr) (room : Room n k b m) (ctx : Context D R m S)
    (hrow : S.scalar .row=a.val) (hcolumn : S.scalar .column=c.val)
    (hlimit : S.scalar .vectorLimit=n^k) (hnext : (S.array .nextMatrix).length=n*n) :
    ∃ t≤n^k*(2*b*(10*k+10)+6*k+24)+7,∃ T,
      Runs (storageBound Reg Arr m) nextCell S t T ∧ Context D R m T ∧
      T.array .nextMatrix=(S.array .nextMatrix).set (c.val+n*a.val)
        (nextEntry D (matrixWord R) a.val c.val) := by
  have hcell : c.val+n*a.val<n*n := (finProdFinEquiv (a,c)).isLt
  have hmul : n*a.val≤m := (Nat.mul_le_mul_left n (Nat.le_of_lt a.isLt)).trans room.matrix
  have hvalid : ValidAtoms m cellPrelude S := by
    simp [cellPrelude,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,ctx.n_eq,hrow,hcolumn,ctx.matrix_eq,hmul,hcell,(Nat.le_of_lt hcell).trans room.matrix]
  obtain ⟨pre,hpre⟩ := atoms_runs ctx.bounded cellPrelude hvalid
  let U := applyAtoms cellPrelude S
  have vecU : (U.array .vector).length=k := by
    rw [pre.array_eq_of_not_mem .vector (by decide)]; exact ctx.vector_length
  have ctxU : Context D R m U := ctx.of_run pre hpre vecU (by decide)
  have rowU : U.scalar .row=a.val := by rw [pre.scalar_eq_of_not_mem .row (by decide),hrow]
  have colU : U.scalar .column=c.val := by rw [pre.scalar_eq_of_not_mem .column (by decide),hcolumn]
  have limitU : U.scalar .vectorLimit=n^k := by rw [pre.scalar_eq_of_not_mem .vectorLimit (by decide),hlimit]
  have cellU : U.scalar .cellIndex=c.val+n*a.val := by
    simp [U,applyAtoms,cellPrelude,Atom.apply,BinaryOp.eval,Store.setScalar,ctx.n_eq,hrow,hcolumn]
  have entryU : U.scalar .entry=boolNat (Decidable.decide ((a,c)∈R)) := by
    simp only [U,applyAtoms,cellPrelude,List.foldl_cons,List.foldl_nil,Atom.apply,
      BinaryOp.eval,Store.setScalar,Function.update_apply,reduceCtorEq,if_false,if_true,
      ctx.n_eq,hrow,hcolumn,ctx.matrix_eq]
    exact matrixWord_read R a c
  obtain ⟨t,ht,V,run,ctxV,entryV⟩ := valueLoop_runs D R a c U room ctxU rowU colU limitU entryU
  have cellV : V.scalar .cellIndex=c.val+n*a.val := by
    rw [run.scalar_eq_of_not_mem .cellIndex (by decide),cellU]
  have nextV : V.array .nextMatrix=S.array .nextMatrix := by
    rw [run.array_eq_of_not_mem .nextMatrix (by decide),pre.array_eq_of_not_mem .nextMatrix (by decide)]
  have validLast : (Atom.write Arr.nextMatrix Reg.cellIndex Reg.entry).Valid V := by
    change V.scalar .cellIndex<(V.array .nextMatrix).length
    simpa [cellV,nextV,hnext] using hcell
  have last := atom_runs ctxV.bounded (.write .nextMatrix .cellIndex .entry) validLast trivial
  have boundLast := Atom.apply_bounded ctxV.bounded (.write .nextMatrix .cellIndex .entry) trivial
  let T := (Atom.write Arr.nextMatrix Reg.cellIndex Reg.entry).apply V
  have rest : Runs (storageBound Reg Arr m) (NatArrayLanguage.sequence [
      loop .value .valueTodo .vectorLimit valueBranch,
      atom (.write .nextMatrix .cellIndex .entry)]) U (t+(1+0)) T :=
    .seq run (.seq last (.skip last.end_bound))
  have full := sequence_append_runs (cellPrelude.map .atom)
    [loop .value .valueTodo .vectorLimit valueBranch,atom (.write .nextMatrix .cellIndex .entry)] pre rest
  have full' : Runs (storageBound Reg Arr m) nextCell S (3+t+1) T := by
    convert full using 1 <;> simp [nextCell,cellPrelude,valueBranch,valueBody,atom] <;> omega
  refine ⟨3+t+1,by omega,T,full',?_,?_⟩
  · exact ctxV.of_run last boundLast (by
      rw [last.array_eq_of_not_mem .vector (by decide)]; exact ctxV.vector_length) (by decide)
  · simp [T,Atom.apply,cellV,nextV,entryV]


end GroupWL.MachinePrograms.IndexedWL

