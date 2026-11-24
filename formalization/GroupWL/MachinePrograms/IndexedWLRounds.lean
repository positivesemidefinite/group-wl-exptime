import GroupWL.MachinePrograms.IndexedWLCell

/-! Actual materialized matrix rounds, preserving the old matrix during all
pair computations and copying the next matrix only after it is complete. -/
namespace GroupWL.MachinePrograms.IndexedWL
open NatArrayLanguage GroupWL.IndexedRefinement
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

private def Filled (expected : List ℕ) (i : ℕ) (actual : List ℕ) : Prop :=
  actual.length=expected.length ∧ ∀ j < i,IndexedRefinement.read actual j=IndexedRefinement.read expected j

private theorem Filled.set_next {expected actual : List ℕ} {i value : ℕ}
    (h : Filled expected i actual) (hi : i<actual.length)
    (hv : value=IndexedRefinement.read expected i) :
    Filled expected (i+1) (actual.set i value) := by
  refine ⟨by simpa using h.1,?_⟩
  intro j hj
  by_cases he : i=j
  · subst j
    simp [IndexedRefinement.read,List.getElem?_set_self hi,hv]
  · simp only [IndexedRefinement.read,List.getElem?_set_ne he]
    exact h.2 j (by omega)

private theorem Filled.complete {expected actual : List ℕ} (h : Filled expected expected.length actual) :
    actual=expected := by
  apply List.ext_getElem h.1
  intro i hi hj
  have hh := h.2 i hj
  simpa only [IndexedRefinement.read,List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hj,Option.getD_some] using hh

private structure ColumnInvariant {n k b : ℕ} (D : Data n k b)
    (R : Finset (Fin n×Fin n)) (a : Fin n) (m i : ℕ) (S : Store Reg Arr) : Prop where
  context : Context D R m S
  row_eq : S.scalar .row=a.val
  index_eq : S.scalar .column=i
  remaining_eq : S.scalar .columnTodo=n-i
  limit_eq : S.scalar .vectorLimit=n^k
  filled : Filled (matrixWord (CompressedRefinement.step D.edges R)) (n*a.val+i) (S.array .nextMatrix)

theorem columnLoop_runs {n k b m : ℕ} (D : Data n k b) (R : Finset (Fin n×Fin n))
    (a : Fin n) (S : Store Reg Arr) (room : Room n k b m) (ctx : Context D R m S)
    (hrow : S.scalar .row=a.val) (hlimit : S.scalar .vectorLimit=n^k)
    (hfilled : Filled (matrixWord (CompressedRefinement.step D.edges R)) (n*a.val) (S.array .nextMatrix)) :
    ∃ t≤n*(n^k*(2*b*(10*k+10)+6*k+24)+10)+3,∃ T,
      Runs (storageBound Reg Arr m) (loop .column .columnTodo .n nextCell) S t T ∧
      Context D R m T ∧
      Filled (matrixWord (CompressedRefinement.step D.edges R)) (n*a.val+n) (T.array .nextMatrix) := by
  have hnsmall : n≤m := (Nat.le_mul_self n).trans room.matrix
  let I := ColumnInvariant D R a m
  have ctxCopy := ctx.scalarUpdate Reg.columnTodo (S.scalar .n) (by simpa [ctx.n_eq] using hnsmall) (by decide)
  have ctxStart := ctxCopy.scalarUpdate Reg.column 0 (Nat.zero_le _) (by decide)
  have start : I 0 ((S.setScalar .columnTodo (S.scalar .n)).setScalar .column 0) := by
    refine ⟨ctxStart,?_,?_,?_,?_,?_⟩
    · simp [hrow]
    · simp
    · simp [ctx.n_eq]
    · simp [hlimit]
    · simpa using hfilled
  have control : ∀i≤n,∀T,I i T →
      T.scalar .column=i ∧ T.scalar .columnTodo=n-i ∧ T.scalar .one=1 ∧
      T.size≤storageBound Reg Arr m := by
    intro i hi T hT
    exact ⟨hT.index_eq,hT.remaining_eq,hT.context.one_eq,Store.size_le_of_bounded hT.context.bounded⟩
  have step : ∀i<n,∀T,I i T →
      ∃t≤n^k*(2*b*(10*k+10)+6*k+24)+7,∃U,
        Runs (storageBound Reg Arr m) nextCell T t U ∧
        U.scalar .column=i ∧ U.scalar .columnTodo=n-i ∧ U.scalar .one=1 ∧
        (U.setScalar .column (i+1)).size≤storageBound Reg Arr m ∧
        I (i+1) (advance .column .columnTodo U) := by
    intro i hi T hT
    let c : Fin n := ⟨i,hi⟩
    have hlen : (T.array .nextMatrix).length=n*n := by simpa using hT.filled.1
    obtain ⟨t,ht,U,run,ctxU,heq⟩ := nextCell_runs D R a c T room hT.context hT.row_eq hT.index_eq hT.limit_eq hlen
    have hiU : U.scalar .column=i := by rw [run.scalar_eq_of_not_mem .column (by decide),hT.index_eq]
    have hrU : U.scalar .columnTodo=n-i := by rw [run.scalar_eq_of_not_mem .columnTodo (by decide),hT.remaining_eq]
    have rowU : U.scalar .row=a.val := by rw [run.scalar_eq_of_not_mem .row (by decide),hT.row_eq]
    have limitU : U.scalar .vectorLimit=n^k := by rw [run.scalar_eq_of_not_mem .vectorLimit (by decide),hT.limit_eq]
    have cell : i+n*a.val<(T.array .nextMatrix).length := by
      rw [hlen]
      exact (finProdFinEquiv (a,c)).isLt
    have hvalue : nextEntry D (matrixWord R) a.val c.val =
        IndexedRefinement.read (matrixWord (CompressedRefinement.step D.edges R)) (i+n*a.val) := by
      rw [nextEntry_correct]
      exact (matrixWord_read _ a c).symm
    have hfilledU : Filled (matrixWord (CompressedRefinement.step D.edges R)) (n*a.val+(i+1))
        (U.array .nextMatrix) := by
      rw [heq]
      have hold : Filled (matrixWord (CompressedRefinement.step D.edges R)) (i+n*a.val) (T.array .nextMatrix) := by
        simpa [Nat.add_comm] using hT.filled
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hold.set_next cell hvalue
    have ctxMid := ctxU.scalarUpdate Reg.column (i+1) (by omega) (by decide)
    have ctxNext := ctxMid.scalarUpdate Reg.columnTodo (U.scalar .columnTodo-1)
      (by rw [hrU]; omega) (by decide)
    refine ⟨t,ht,U,run,hiU,hrU,ctxU.one_eq,Store.size_le_of_bounded ctxMid.bounded,?_⟩
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · simpa [advance,hiU] using ctxNext
    · simpa [advance] using rowU
    · simp [advance,hiU]
    · simp [advance,hrU]; omega
    · simpa [advance] using limitU
    · simpa [advance] using hfilledU
  obtain ⟨t,ht,T,run,hT⟩ := countedLoop_runs (storageBound Reg Arr m) .column .columnTodo .n .one nextCell n
    (n^k*(2*b*(10*k+10)+6*k+24)+7) I S (Store.size_le_of_bounded ctx.bounded)
    (Store.size_le_of_bounded ctxCopy.bounded) start control (by decide) (by decide) step
  exact ⟨t,by nlinarith,T,run,hT.context,hT.filled⟩


private structure RowInvariant {n k b : ℕ} (D : Data n k b)
    (R : Finset (Fin n×Fin n)) (m i : ℕ) (S : Store Reg Arr) : Prop where
  context : Context D R m S
  index_eq : S.scalar .row=i
  remaining_eq : S.scalar .rowTodo=n-i
  limit_eq : S.scalar .vectorLimit=n^k
  filled : Filled (matrixWord (CompressedRefinement.step D.edges R)) (n*i) (S.array .nextMatrix)

theorem rowLoop_runs {n k b m : ℕ} (D : Data n k b) (R : Finset (Fin n×Fin n))
    (S : Store Reg Arr) (room : Room n k b m) (ctx : Context D R m S)
    (hlimit : S.scalar .vectorLimit=n^k) (hnext : (S.array .nextMatrix).length=n*n) :
    ∃ t≤n*(n*(n^k*(2*b*(10*k+10)+6*k+24)+10)+6)+3,∃ T,
      Runs (storageBound Reg Arr m) (loop .row .rowTodo .n (loop .column .columnTodo .n nextCell)) S t T ∧
      Context D R m T ∧ T.array .nextMatrix=matrixWord (CompressedRefinement.step D.edges R) := by
  have hnsmall : n≤m := (Nat.le_mul_self n).trans room.matrix
  let I := RowInvariant D R m
  have ctxCopy := ctx.scalarUpdate Reg.rowTodo (S.scalar .n) (by simpa [ctx.n_eq] using hnsmall) (by decide)
  have ctxStart := ctxCopy.scalarUpdate Reg.row 0 (Nat.zero_le _) (by decide)
  have start : I 0 ((S.setScalar .rowTodo (S.scalar .n)).setScalar .row 0) := by
    refine ⟨ctxStart,?_,?_,?_,?_⟩
    · simp
    · simp [ctx.n_eq]
    · simp [hlimit]
    · exact ⟨by simpa using hnext,by simp⟩
  have control : ∀i≤n,∀T,I i T →
      T.scalar .row=i ∧ T.scalar .rowTodo=n-i ∧ T.scalar .one=1 ∧
      T.size≤storageBound Reg Arr m := by
    intro i hi T hT
    exact ⟨hT.index_eq,hT.remaining_eq,hT.context.one_eq,Store.size_le_of_bounded hT.context.bounded⟩
  have step : ∀i<n,∀T,I i T →
      ∃t≤n*(n^k*(2*b*(10*k+10)+6*k+24)+10)+3,∃U,
        Runs (storageBound Reg Arr m) (loop .column .columnTodo .n nextCell) T t U ∧
        U.scalar .row=i ∧ U.scalar .rowTodo=n-i ∧ U.scalar .one=1 ∧
        (U.setScalar .row (i+1)).size≤storageBound Reg Arr m ∧
        I (i+1) (advance .row .rowTodo U) := by
    intro i hi T hT
    obtain ⟨t,ht,U,run,ctxU,heq⟩ := columnLoop_runs D R ⟨i,hi⟩ T room hT.context hT.index_eq
      hT.limit_eq hT.filled
    have hiU : U.scalar .row=i := by rw [run.scalar_eq_of_not_mem .row (by decide),hT.index_eq]
    have hrU : U.scalar .rowTodo=n-i := by rw [run.scalar_eq_of_not_mem .rowTodo (by decide),hT.remaining_eq]
    have limitU : U.scalar .vectorLimit=n^k := by rw [run.scalar_eq_of_not_mem .vectorLimit (by decide),hT.limit_eq]
    have ctxMid := ctxU.scalarUpdate Reg.row (i+1) (by omega) (by decide)
    have ctxNext := ctxMid.scalarUpdate Reg.rowTodo (U.scalar .rowTodo-1)
      (by rw [hrU]; omega) (by decide)
    refine ⟨t,ht,U,run,hiU,hrU,ctxU.one_eq,Store.size_le_of_bounded ctxMid.bounded,?_⟩
    refine ⟨?_,?_,?_,?_,?_⟩
    · simpa [advance,hiU] using ctxNext
    · simp [advance,hiU]
    · simp [advance,hrU]; omega
    · simpa [advance] using limitU
    · simpa [advance,Nat.mul_add] using heq
  obtain ⟨t,ht,T,run,hT⟩ := countedLoop_runs (storageBound Reg Arr m) .row .rowTodo .n .one
    (loop .column .columnTodo .n nextCell) n (n*(n^k*(2*b*(10*k+10)+6*k+24)+10)+3)
    I S (Store.size_le_of_bounded ctx.bounded) (Store.size_le_of_bounded ctxCopy.bounded)
    start control (by decide) (by decide) step
  refine ⟨t,by nlinarith,T,run,hT.context,?_⟩
  apply Filled.complete
  simpa only [matrixWord_length] using hT.filled

def roundCost (n k b : ℕ) : ℕ := n*(n*(n^k*(2*b*(10*k+10)+6*k+24)+10)+6)+4

/-- One entire materialized relation round is executed with the old matrix
fixed, then the stored next matrix becomes the input to the following round. -/
theorem round_runs {n k b m : ℕ} (D : Data n k b) (R : Finset (Fin n×Fin n))
    (S : Store Reg Arr) (room : Room n k b m) (ctx : Context D R m S)
    (hlimit : S.scalar .vectorLimit=n^k) (hnext : (S.array .nextMatrix).length=n*n) :
    ∃ t≤roundCost n k b,∃ T,
      Runs (storageBound Reg Arr m) round S t T ∧
      Context D (CompressedRefinement.step D.edges R) m T ∧
      (T.array .nextMatrix).length=n*n := by
  obtain ⟨t,ht,U,run,ctxU,heq⟩ := rowLoop_runs D R S room ctx hlimit hnext
  have copy := atom_runs ctxU.bounded (.copyArray .matrix .nextMatrix) trivial trivial
  have boundCopy := Atom.apply_bounded ctxU.bounded (.copyArray .matrix .nextMatrix) trivial
  let T := (Atom.copyArray Arr.matrix Arr.nextMatrix).apply U
  refine ⟨t+1,by unfold roundCost; omega,T,?_,?_,?_⟩
  · simpa using Runs.seq run (Runs.seq copy (Runs.skip copy.end_bound))
  · refine ⟨boundCopy,ctxU.n_eq,ctxU.arity_eq,ctxU.width_eq,ctxU.one_eq,?_,?_,?_,?_⟩
    · simpa [T,Atom.apply] using heq
    · simpa [T,Atom.apply] using ctxU.fanouts_eq
    · simpa [T,Atom.apply] using ctxU.targets_eq
    · simpa [T,Atom.apply] using ctxU.vector_length
  · simp [T,Atom.apply,heq]



private structure RefinementInvariant {n k b : ℕ} (D : Data n k b)
    (initialEq : Fin n → Fin n → Bool) (m i : ℕ) (S : Store Reg Arr) : Prop where
  context : Context D (CompressedRefinement.table D.edges initialEq i) m S
  index_eq : S.scalar .round=i
  remaining_eq : S.scalar .roundTodo=n*n-i
  limit_eq : S.scalar .vectorLimit=n^k
  next_length : (S.array .nextMatrix).length=n*n

/-- The fixed source loop executes the entire n^2-round refinement bound. -/
theorem refinementLoop_runs {n k b m : ℕ} (D : Data n k b)
    (initialEq : Fin n → Fin n → Bool) (S : Store Reg Arr) (room : Room n k b m)
    (ctx : Context D (CompressedRefinement.table D.edges initialEq 0) m S)
    (hlimit : S.scalar .vectorLimit=n^k) (hsquare : S.scalar .square=n*n)
    (hnext : (S.array .nextMatrix).length=n*n) :
    ∃ t≤(n*n)*(roundCost n k b+3)+3,∃ T,
      Runs (storageBound Reg Arr m) (loop .round .roundTodo .square round) S t T ∧
      Context D (CompressedRefinement.table D.edges initialEq (n*n)) m T := by
  let I := RefinementInvariant D initialEq m
  have ctxCopy := ctx.scalarUpdate Reg.roundTodo (S.scalar .square) (by simpa [hsquare] using room.matrix) (by decide)
  have ctxStart := ctxCopy.scalarUpdate Reg.round 0 (Nat.zero_le _) (by decide)
  have start : I 0 ((S.setScalar .roundTodo (S.scalar .square)).setScalar .round 0) := by
    refine ⟨ctxStart,?_,?_,?_,?_⟩
    · simp
    · simp [hsquare]
    · simp [hlimit]
    · simpa using hnext
  have control : ∀i≤n*n,∀T,I i T →
      T.scalar .round=i ∧ T.scalar .roundTodo=n*n-i ∧ T.scalar .one=1 ∧
      T.size≤storageBound Reg Arr m := by
    intro i hi T hT
    exact ⟨hT.index_eq,hT.remaining_eq,hT.context.one_eq,Store.size_le_of_bounded hT.context.bounded⟩
  have step : ∀i<n*n,∀T,I i T →
      ∃t≤roundCost n k b,∃U,Runs (storageBound Reg Arr m) round T t U ∧
        U.scalar .round=i ∧ U.scalar .roundTodo=n*n-i ∧ U.scalar .one=1 ∧
        (U.setScalar .round (i+1)).size≤storageBound Reg Arr m ∧
        I (i+1) (advance .round .roundTodo U) := by
    intro i hi T hT
    obtain ⟨t,ht,U,run,ctxU,hnextU⟩ := round_runs D _ T room hT.context hT.limit_eq hT.next_length
    have hiU : U.scalar .round=i := by rw [run.scalar_eq_of_not_mem .round (by decide),hT.index_eq]
    have hrU : U.scalar .roundTodo=n*n-i := by rw [run.scalar_eq_of_not_mem .roundTodo (by decide),hT.remaining_eq]
    have limitU : U.scalar .vectorLimit=n^k := by rw [run.scalar_eq_of_not_mem .vectorLimit (by decide),hT.limit_eq]
    have ctxMid := ctxU.scalarUpdate Reg.round (i+1) (by have := room.matrix; omega) (by decide)
    have ctxNext := ctxMid.scalarUpdate Reg.roundTodo (U.scalar .roundTodo-1)
      (by rw [hrU]; have := room.matrix; omega) (by decide)
    refine ⟨t,ht,U,run,hiU,hrU,ctxU.one_eq,Store.size_le_of_bounded ctxMid.bounded,?_⟩
    refine ⟨?_,?_,?_,?_,?_⟩
    · simpa only [advance,hiU,CompressedRefinement.table] using ctxNext
    · simp [advance,hiU]
    · simp [advance,hrU]; omega
    · simpa [advance] using limitU
    · simpa [advance] using hnextU
  obtain ⟨t,ht,T,run,hT⟩ := countedLoop_runs (storageBound Reg Arr m) .round .roundTodo .square .one
    round (n*n) (roundCost n k b) I S (Store.size_le_of_bounded ctx.bounded)
    (Store.size_le_of_bounded ctxCopy.bounded) start control (by decide) (by decide) step
  exact ⟨t,ht,T,run,hT.context⟩


end GroupWL.MachinePrograms.IndexedWL

