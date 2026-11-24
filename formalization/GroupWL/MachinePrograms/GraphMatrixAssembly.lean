import GroupWL.MachinePrograms.GraphMatrixPrograms
import GroupWL.MachinePrograms.NatArrayCountedLoops

/-! Matrix assembly from the concrete tuple comparator. -/
namespace GroupWL.MachinePrograms.GraphMatrixPrograms
open NatArrayLanguage GroupWL.IndexedRefinement
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

def initialEq {n m k : ℕ} (mul : Fin n → Fin n → Bool) (mul' : Fin m → Fin m → Bool)
    (a c : Fin (n^k+m^k)) : Bool := decide (pointSignature mul mul' a=pointSignature mul mul' c)

def initialRelation {n m k : ℕ} (mul : Fin n → Fin n → Bool) (mul' : Fin m → Fin m → Bool) :
    Finset (Fin (n^k+m^k)×Fin (n^k+m^k)) :=
  Finset.univ.filter (fun ac => initialEq mul mul' ac.1 ac.2=true)

theorem initialMatrix_read {n m k : ℕ} (mul : Fin n → Fin n → Bool)
    (mul' : Fin m → Fin m → Bool) (a c : Fin (n^k+m^k)) :
    IndexedRefinement.read (matrixWord (initialRelation (k:=k) mul mul')) (c.val+(n^k+m^k)*a.val)=
      boolNat (initialEq mul mul' a c) := by
  rw [matrixWord_read]
  simp [initialRelation]

structure Room (n m k B : ℕ) : Prop where
  left_positive : 0<n
  right_positive : 0<m
  left_table : n*n≤B
  right_table : m*m≤B
  cube : k^3≤B
  one : 1≤B
  matrix : (n^k+m^k)*(n^k+m^k)≤B

structure Context {n m k : ℕ} (mul : Fin n → Fin n → Bool) (mul' : Fin m → Fin m → Bool)
    (B : ℕ) (S : Store Reg Arr) : Prop where
  bounded : S.Bounded B
  left_eq : S.scalar (.inr .leftCount)=n
  right_eq : S.scalar (.inr .rightCount)=m
  arity_eq : S.scalar (.inr .arity)=k
  cutoff_eq : S.scalar (.inr .vectorLimit)=n^k
  total_eq : S.scalar (.inr .square)=n^k+m^k
  one_eq : S.scalar (.inr .one)=1
  vector_length : (S.array (.inr .vector)).length=k
  matrix_length : (S.array (.inr .matrix)).length=(n^k+m^k)*(n^k+m^k)
  left_table : S.array (.inr .fanouts)=GraphInitial.tableWord mul
  right_table : S.array (.inr .targets)=GraphInitial.tableWord mul'

theorem Context.scalarUpdate {n m k B : ℕ} {mul : Fin n → Fin n → Bool}
    {mul' : Fin m → Fin m → Bool} {S : Store Reg Arr} (ctx : Context (k:=k) mul mul' B S)
    (r : Reg) (v : ℕ) (hv : v≤B)
    (hr : r∉({.inr .leftCount,.inr .rightCount,.inr .arity,.inr .vectorLimit,.inr .square,.inr .one} : Finset Reg)) :
    Context (k:=k) mul mul' B (S.setScalar r v) := by
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hr
  refine ⟨ctx.bounded.setScalar r hv,?_,?_,?_,?_,?_,?_,ctx.vector_length,ctx.matrix_length,ctx.left_table,ctx.right_table⟩
  all_goals first
    | simpa [Ne.symm hr.1] using ctx.left_eq
    | simpa [Ne.symm hr.2.1] using ctx.right_eq
    | simpa [Ne.symm hr.2.2.1] using ctx.arity_eq
    | simpa [Ne.symm hr.2.2.2.1] using ctx.cutoff_eq
    | simpa [Ne.symm hr.2.2.2.2.1] using ctx.total_eq
    | simpa [Ne.symm hr.2.2.2.2.2] using ctx.one_eq

def storeAtoms : List (Atom Reg Arr) := [
  .binary .mul (.inr .cellIndex) (.inr .square) (.inr .row),
  .binary .add (.inr .cellIndex) (.inr .column) (.inr .cellIndex),
  .write (.inr .matrix) (.inr .cellIndex) (.inl .result)]

def cell : Code := .seq comparePair (atoms storeAtoms)

theorem cell_runs {n m k B : ℕ} (mul : Fin n → Fin n → Bool) (mul' : Fin m → Fin m → Bool)
    (a c : Fin (n^k+m^k)) (S : Store Reg Arr) (room : Room n m k B) (ctx : Context (k:=k) mul mul' B S)
    (hrow : S.scalar (.inr .row)=a.val) (hcol : S.scalar (.inr .column)=c.val) :
    ∃t≤26*k^3+12*k+33,∃T,Runs (storageBound Reg Arr B) cell S t T ∧ Context (k:=k) mul mul' B T ∧
      T.array (.inr .matrix)=(S.array (.inr .matrix)).set (c.val+(n^k+m^k)*a.val)
        (IndexedRefinement.read (matrixWord (initialRelation (k:=k) mul mul')) (c.val+(n^k+m^k)*a.val)) := by
  obtain ⟨tc,htc,U,run,hU,hresult,heq,lenU⟩ := comparePair_runs mul mul' a c S ctx.bounded
    ctx.left_eq ctx.right_eq ctx.cutoff_eq hrow hcol ctx.arity_eq ctx.one_eq ctx.vector_length
    room.left_positive room.right_positive room.left_table room.right_table room.cube room.one
    ctx.left_table ctx.right_table
  have scalarFrame (r : Reg) (hr : r∉comparePair.scalarWrites) : U.scalar r=S.scalar r :=
    run.scalar_eq_of_not_mem r hr
  have arrayFrame (a : Arr) (ha : a∉comparePair.arrayWrites) : U.array a=S.array a :=
    run.array_eq_of_not_mem a ha
  have rowU : U.scalar (.inr .row)=a.val := by rw [scalarFrame _ (by decide),hrow]
  have colU : U.scalar (.inr .column)=c.val := by rw [scalarFrame _ (by decide),hcol]
  have totalU : U.scalar (.inr .square)=n^k+m^k := by rw [scalarFrame _ (by decide),ctx.total_eq]
  have matrixU : U.array (.inr .matrix)=S.array (.inr .matrix) := arrayFrame _ (by decide)
  have hindex : c.val+(n^k+m^k)*a.val<(n^k+m^k)*(n^k+m^k) := (finProdFinEquiv (a,c)).isLt
  have hmul : (n^k+m^k)*a.val≤B :=
    (Nat.mul_le_mul_left _ (Nat.le_of_lt a.isLt)).trans room.matrix
  have valid : ValidAtoms B storeAtoms U := by
    simp only [storeAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,Function.update_apply,Sum.inr.injEq,Sum.inl.injEq,reduceCtorEq,if_false,if_true]
    simp only [rowU,colU,totalU,matrixU,ctx.matrix_length]
    exact ⟨trivial,hmul,trivial,(Nat.le_of_lt hindex).trans room.matrix,hindex,trivial,trivial⟩
  obtain ⟨finish,hfinish⟩ := atoms_runs hU storeAtoms valid
  let T := applyAtoms storeAtoms U
  have full : Runs (storageBound Reg Arr B) cell S (tc+3) T := .seq run finish
  have resultEq : U.scalar (.inl .result)=boolNat (initialEq mul mul' a c) := by
    by_cases h : pointSignature mul mul' a=pointSignature mul mul' c
    · have hh := heq.mpr h
      simp [initialEq,h,boolNat,hh]
    · have hh : U.scalar (.inl .result)≠1 := fun hx => h (heq.mp hx)
      have hz : U.scalar (.inl .result)=0 := by omega
      simp [initialEq,h,boolNat,hz]
  have matrixT : T.array (.inr .matrix)=(S.array (.inr .matrix)).set (c.val+(n^k+m^k)*a.val)
      (IndexedRefinement.read (matrixWord (initialRelation (k:=k) mul mul')) (c.val+(n^k+m^k)*a.val)) := by
    simp only [T,applyAtoms,storeAtoms,List.foldl_cons,List.foldl_nil,Atom.apply,BinaryOp.eval,
      Store.setScalar,Function.update_apply,Store.setArray_same,Sum.inr.injEq,Sum.inl.injEq,
      reduceCtorEq,if_false,if_true,rowU,colU,totalU,matrixU,resultEq,initialMatrix_read]
  refine ⟨tc+3,by omega,T,full,?_,matrixT⟩
  refine ⟨hfinish,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [full.scalar_eq_of_not_mem _ (by decide)]; exact ctx.left_eq
  · rw [full.scalar_eq_of_not_mem _ (by decide)]; exact ctx.right_eq
  · rw [full.scalar_eq_of_not_mem _ (by decide)]; exact ctx.arity_eq
  · rw [full.scalar_eq_of_not_mem _ (by decide)]; exact ctx.cutoff_eq
  · rw [full.scalar_eq_of_not_mem _ (by decide)]; exact ctx.total_eq
  · rw [full.scalar_eq_of_not_mem _ (by decide)]; exact ctx.one_eq
  · rw [finish.array_eq_of_not_mem _ (by decide)]; exact lenU
  · simpa [matrixT] using ctx.matrix_length
  · rw [full.array_eq_of_not_mem _ (by decide)]; exact ctx.left_table
  · rw [full.array_eq_of_not_mem _ (by decide)]; exact ctx.right_table


private def Filled (expected : List ℕ) (i : ℕ) (actual : List ℕ) : Prop :=
  actual.length=expected.length ∧ ∀ j < i,IndexedRefinement.read actual j=IndexedRefinement.read expected j

private theorem Filled.set_next {expected actual : List ℕ} {i : ℕ}
    (h : Filled expected i actual) (hi : i<actual.length) :
    Filled expected (i+1) (actual.set i (IndexedRefinement.read expected i)) := by
  refine ⟨by simpa using h.1,?_⟩
  intro j hj
  by_cases he : i=j
  · subst j
    simp [IndexedRefinement.read,List.getElem?_set_self hi]
  · simp only [IndexedRefinement.read,List.getElem?_set_ne he]
    exact h.2 j (by omega)

private theorem Filled.complete {expected actual : List ℕ} (h : Filled expected expected.length actual) :
    actual=expected := by
  apply List.ext_getElem h.1
  intro i hi hj
  have hh := h.2 i hj
  simpa only [IndexedRefinement.read,List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hj,Option.getD_some] using hh

def columns : Code := countedLoop (.inr .column) (.inr .columnTodo) (.inr .square) (.inr .one) cell
def rows : Code := countedLoop (.inr .row) (.inr .rowTodo) (.inr .square) (.inr .one) columns

private structure ColumnInvariant {n m k : ℕ} (mul : Fin n → Fin n → Bool)
    (mul' : Fin m → Fin m → Bool) (a : Fin (n^k+m^k)) (B i : ℕ) (S : Store Reg Arr) : Prop where
  context : Context (k:=k) mul mul' B S
  row_eq : S.scalar (.inr .row)=a.val
  index_eq : S.scalar (.inr .column)=i
  remaining_eq : S.scalar (.inr .columnTodo)=n^k+m^k-i
  filled : Filled (matrixWord (initialRelation (k:=k) mul mul')) ((n^k+m^k)*a.val+i) (S.array (.inr .matrix))

theorem columns_runs {n m k B : ℕ} (mul : Fin n → Fin n → Bool) (mul' : Fin m → Fin m → Bool)
    (a : Fin (n^k+m^k)) (S : Store Reg Arr) (room : Room n m k B) (ctx : Context (k:=k) mul mul' B S)
    (hrow : S.scalar (.inr .row)=a.val)
    (hfilled : Filled (matrixWord (initialRelation (k:=k) mul mul')) ((n^k+m^k)*a.val) (S.array (.inr .matrix))) :
    ∃t≤(n^k+m^k)*(26*k^3+12*k+36)+3,∃T,Runs (storageBound Reg Arr B) columns S t T ∧
      Context (k:=k) mul mul' B T ∧
      Filled (matrixWord (initialRelation (k:=k) mul mul')) ((n^k+m^k)*a.val+(n^k+m^k)) (T.array (.inr .matrix)) := by
  let N := n^k+m^k
  have hN : N≤B := (Nat.le_mul_self N).trans room.matrix
  let I := ColumnInvariant mul mul' a B
  have ctxCopy := ctx.scalarUpdate (.inr .columnTodo) (S.scalar (.inr .square))
    (by simpa [ctx.total_eq] using hN) (by decide)
  have ctxStart := ctxCopy.scalarUpdate (.inr .column) 0 (Nat.zero_le _) (by decide)
  have start : I 0 ((S.setScalar (.inr .columnTodo) (S.scalar (.inr .square))).setScalar (.inr .column) 0) := by
    refine ⟨ctxStart,?_,?_,?_,?_⟩
    · simp [hrow]
    · simp
    · simp [ctx.total_eq]
    · simpa using hfilled
  have control : ∀ i≤N,∀T,I i T →
      T.scalar (.inr .column)=i ∧ T.scalar (.inr .columnTodo)=N-i ∧
      T.scalar (.inr .one)=1 ∧ T.size≤storageBound Reg Arr B := by
    intro i hi T hT
    exact ⟨hT.index_eq,hT.remaining_eq,hT.context.one_eq,Store.size_le_of_bounded hT.context.bounded⟩
  have step : ∀ i<N,∀T,I i T →
      ∃t≤26*k^3+12*k+33,∃U,Runs (storageBound Reg Arr B) cell T t U ∧
        U.scalar (.inr .column)=i ∧ U.scalar (.inr .columnTodo)=N-i ∧ U.scalar (.inr .one)=1 ∧
        (U.setScalar (.inr .column) (i+1)).size≤storageBound Reg Arr B ∧
        I (i+1) (advance (.inr .column) (.inr .columnTodo) U) := by
    intro i hi T hT
    let c : Fin (n^k+m^k) := ⟨i,hi⟩
    obtain ⟨t,ht,U,run,ctxU,heq⟩ := cell_runs mul mul' a c T room hT.context hT.row_eq hT.index_eq
    have hiU : U.scalar (.inr .column)=i := by rw [run.scalar_eq_of_not_mem _ (by decide),hT.index_eq]
    have hrU : U.scalar (.inr .columnTodo)=N-i := by rw [run.scalar_eq_of_not_mem _ (by decide),hT.remaining_eq]
    have rowU : U.scalar (.inr .row)=a.val := by rw [run.scalar_eq_of_not_mem _ (by decide),hT.row_eq]
    have hcell : i+N*a.val<(T.array (.inr .matrix)).length := by
      rw [hT.context.matrix_length]
      exact (finProdFinEquiv (a,c)).isLt
    have filledU : Filled (matrixWord (initialRelation (k:=k) mul mul')) (N*a.val+(i+1)) (U.array (.inr .matrix)) := by
      rw [heq]
      have old : Filled (matrixWord (initialRelation (k:=k) mul mul')) (i+N*a.val) (T.array (.inr .matrix)) := by
        simpa [Nat.add_comm] using hT.filled
      simpa [N,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using old.set_next hcell
    have ctxMid := ctxU.scalarUpdate (.inr .column) (i+1) (by omega) (by decide)
    have ctxNext := ctxMid.scalarUpdate (.inr .columnTodo) (U.scalar (.inr .columnTodo)-1)
      (by rw [hrU]; omega) (by decide)
    refine ⟨t,ht,U,run,hiU,hrU,ctxU.one_eq,Store.size_le_of_bounded ctxMid.bounded,?_⟩
    refine ⟨?_,?_,?_,?_,?_⟩
    · simpa [advance,hiU] using ctxNext
    · simpa [advance] using rowU
    · simp [advance,hiU]
    · simp [advance,hrU]; omega
    · simpa [advance] using filledU
  obtain ⟨t,ht,T,run,hT⟩ := countedLoop_runs (storageBound Reg Arr B) (.inr .column) (.inr .columnTodo)
    (.inr .square) (.inr .one) cell N (26*k^3+12*k+33) I S
    (Store.size_le_of_bounded ctx.bounded) (Store.size_le_of_bounded ctxCopy.bounded)
    start control (by decide) (by decide) step
  exact ⟨t,by dsimp [N] at ht; nlinarith,T,run,hT.context,hT.filled⟩

private structure RowInvariant {n m k : ℕ} (mul : Fin n → Fin n → Bool)
    (mul' : Fin m → Fin m → Bool) (B i : ℕ) (S : Store Reg Arr) : Prop where
  context : Context (k:=k) mul mul' B S
  index_eq : S.scalar (.inr .row)=i
  remaining_eq : S.scalar (.inr .rowTodo)=n^k+m^k-i
  filled : Filled (matrixWord (initialRelation (k:=k) mul mul')) ((n^k+m^k)*i) (S.array (.inr .matrix))

theorem rows_runs {n m k B : ℕ} (mul : Fin n → Fin n → Bool) (mul' : Fin m → Fin m → Bool)
    (S : Store Reg Arr) (room : Room n m k B) (ctx : Context (k:=k) mul mul' B S) :
    ∃t≤(n^k+m^k)*((n^k+m^k)*(26*k^3+12*k+36)+6)+3,∃T,
      Runs (storageBound Reg Arr B) rows S t T ∧ Context (k:=k) mul mul' B T ∧
      T.array (.inr .matrix)=matrixWord (initialRelation (k:=k) mul mul') := by
  let N := n^k+m^k
  have hN : N≤B := (Nat.le_mul_self N).trans room.matrix
  let I := RowInvariant (k:=k) mul mul' B
  have ctxCopy := ctx.scalarUpdate (.inr .rowTodo) (S.scalar (.inr .square))
    (by simpa [ctx.total_eq] using hN) (by decide)
  have ctxStart := ctxCopy.scalarUpdate (.inr .row) 0 (Nat.zero_le _) (by decide)
  have start : I 0 ((S.setScalar (.inr .rowTodo) (S.scalar (.inr .square))).setScalar (.inr .row) 0) := by
    refine ⟨ctxStart,?_,?_,?_⟩
    · simp
    · simp [ctx.total_eq]
    · exact ⟨by simpa using ctx.matrix_length,by simp⟩
  have control : ∀ i≤N,∀T,I i T →
      T.scalar (.inr .row)=i ∧ T.scalar (.inr .rowTodo)=N-i ∧ T.scalar (.inr .one)=1 ∧
      T.size≤storageBound Reg Arr B := by
    intro i hi T hT
    exact ⟨hT.index_eq,hT.remaining_eq,hT.context.one_eq,Store.size_le_of_bounded hT.context.bounded⟩
  have step : ∀ i<N,∀T,I i T →
      ∃t≤N*(26*k^3+12*k+36)+3,∃U,Runs (storageBound Reg Arr B) columns T t U ∧
        U.scalar (.inr .row)=i ∧ U.scalar (.inr .rowTodo)=N-i ∧ U.scalar (.inr .one)=1 ∧
        (U.setScalar (.inr .row) (i+1)).size≤storageBound Reg Arr B ∧
        I (i+1) (advance (.inr .row) (.inr .rowTodo) U) := by
    intro i hi T hT
    obtain ⟨t,ht,U,run,ctxU,heq⟩ := columns_runs mul mul' ⟨i,hi⟩ T room hT.context hT.index_eq hT.filled
    have hiU : U.scalar (.inr .row)=i := by rw [run.scalar_eq_of_not_mem _ (by decide),hT.index_eq]
    have hrU : U.scalar (.inr .rowTodo)=N-i := by rw [run.scalar_eq_of_not_mem _ (by decide),hT.remaining_eq]
    have ctxMid := ctxU.scalarUpdate (.inr .row) (i+1) (by omega) (by decide)
    have ctxNext := ctxMid.scalarUpdate (.inr .rowTodo) (U.scalar (.inr .rowTodo)-1)
      (by rw [hrU]; omega) (by decide)
    refine ⟨t,ht,U,run,hiU,hrU,ctxU.one_eq,Store.size_le_of_bounded ctxMid.bounded,?_⟩
    refine ⟨?_,?_,?_,?_⟩
    · simpa [advance,hiU] using ctxNext
    · simp [advance,hiU]
    · simp [advance,hrU]; omega
    · simpa [advance,N,Nat.mul_add] using heq
  obtain ⟨t,ht,T,run,hT⟩ := countedLoop_runs (storageBound Reg Arr B) (.inr .row) (.inr .rowTodo)
    (.inr .square) (.inr .one) columns N (N*(26*k^3+12*k+36)+3) I S
    (Store.size_le_of_bounded ctx.bounded) (Store.size_le_of_bounded ctxCopy.bounded)
    start control (by decide) (by decide) step
  refine ⟨t,by dsimp [N] at ht; nlinarith,T,run,hT.context,?_⟩
  apply Filled.complete
  simpa only [matrixWord_length] using hT.filled



structure Input {n m k : ℕ} (mul : Fin n → Fin n → Bool) (mul' : Fin m → Fin m → Bool)
    (B : ℕ) (S : Store Reg Arr) : Prop where
  bounded : S.Bounded B
  left_eq : S.scalar (.inr .leftCount)=n
  right_eq : S.scalar (.inr .rightCount)=m
  arity_eq : S.scalar (.inr .arity)=k
  cutoff_eq : S.scalar (.inr .vectorLimit)=n^k
  total_eq : S.scalar (.inr .square)=n^k+m^k
  left_table : S.array (.inr .fanouts)=GraphInitial.tableWord mul
  right_table : S.array (.inr .targets)=GraphInitial.tableWord mul'

def prepareAtoms : List (Atom Reg Arr) := [
  .const (.inr .zero) 0,.const (.inr .one) 1,
  .binary .mul (.inr .targetIndex) (.inr .square) (.inr .square),
  .allocate (.inr .matrix) (.inr .targetIndex) (.inr .zero),
  .allocate (.inr .vector) (.inr .arity) (.inr .zero)]

def build : Code := .seq (atoms prepareAtoms) rows

theorem build_runs {n m k B : ℕ} (mul : Fin n → Fin n → Bool) (mul' : Fin m → Fin m → Bool)
    (S : Store Reg Arr) (room : Room n m k B) (input : Input (k:=k) mul mul' B S) :
    ∃t≤(n^k+m^k)*((n^k+m^k)*(26*k^3+12*k+36)+6)+8,∃T,
      Runs (storageBound Reg Arr B) build S t T ∧ Context (k:=k) mul mul' B T ∧
      T.array (.inr .matrix)=matrixWord (initialRelation (k:=k) mul mul') := by
  have valid : ValidAtoms B prepareAtoms S := by
    simp [prepareAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,input.total_eq,room.one,room.matrix]
  obtain ⟨prepare,hprepare⟩ := atoms_runs input.bounded prepareAtoms valid
  let U := applyAtoms prepareAtoms S
  have scalarFrame (r : Reg) (hr : r∉(atoms prepareAtoms).scalarWrites) : U.scalar r=S.scalar r :=
    prepare.scalar_eq_of_not_mem r hr
  have arrayFrame (a : Arr) (ha : a∉(atoms prepareAtoms).arrayWrites) : U.array a=S.array a :=
    prepare.array_eq_of_not_mem a ha
  have ctxU : Context (k:=k) mul mul' B U := by
    refine ⟨hprepare,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · rw [scalarFrame _ (by decide)]; exact input.left_eq
    · rw [scalarFrame _ (by decide)]; exact input.right_eq
    · rw [scalarFrame _ (by decide)]; exact input.arity_eq
    · rw [scalarFrame _ (by decide)]; exact input.cutoff_eq
    · rw [scalarFrame _ (by decide)]; exact input.total_eq
    · simp [U,applyAtoms,prepareAtoms,Atom.apply,Store.setScalar]
    · simp [U,applyAtoms,prepareAtoms,Atom.apply,Store.setScalar,Store.setArray,input.arity_eq]
    · simp [U,applyAtoms,prepareAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,input.total_eq]
    · rw [arrayFrame _ (by decide)]; exact input.left_table
    · rw [arrayFrame _ (by decide)]; exact input.right_table
  obtain ⟨t,ht,T,run,ctxT,heq⟩ := rows_runs mul mul' U room ctxU
  exact ⟨5+t,by omega,T,.seq prepare run,ctxT,heq⟩



theorem build_cost_le {n m k B : ℕ} (room : Room n m k B) :
    (n^k+m^k)*((n^k+m^k)*(26*k^3+12*k+36)+6)+8≤100*(B+1)^2 := by
  let N := n^k+m^k
  have hN : N≤B := (Nat.le_mul_self N).trans room.matrix
  have hk : k≤B := (Nat.le_self_pow (by decide : 3≠0) k).trans room.cube
  have hc : 26*k^3+12*k+36≤38*B+36 := by have := room.cube; omega
  have hprod := Nat.mul_le_mul room.matrix hc
  change N*N*(26*k^3+12*k+36)≤B*(38*B+36) at hprod
  change N*(N*(26*k^3+12*k+36)+6)+8≤100*(B+1)^2
  nlinarith

theorem build_runs_polynomial {n m k B : ℕ} (mul : Fin n → Fin n → Bool)
    (mul' : Fin m → Fin m → Bool) (S : Store Reg Arr) (room : Room n m k B)
    (input : Input (k:=k) mul mul' B S) :
    ∃t≤100*(B+1)^2,∃T,Runs (200*(B+1)^2) build S t T ∧
      Context (k:=k) mul mul' B T ∧
      T.array (.inr .matrix)=matrixWord (initialRelation (k:=k) mul mul') := by
  obtain ⟨t,ht,T,run,hT,heq⟩ := build_runs mul mul' S room input
  have hb : storageBound Reg Arr B≤200*(B+1)^2 :=
    Nat.mul_le_mul_right _ (by decide : Fintype.card Reg+3*Fintype.card Arr≤200)
  exact ⟨t,ht.trans (build_cost_le room),T,run.mono hb,hT,heq⟩


end GroupWL.MachinePrograms.GraphMatrixPrograms

