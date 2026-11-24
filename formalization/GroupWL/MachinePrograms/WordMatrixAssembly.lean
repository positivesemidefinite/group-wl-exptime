import GroupWL.MachinePrograms.WordMatrixDefinitions

namespace GroupWL.MachinePrograms.WordMatrixPrograms
open NatArrayLanguage WordMatrixSemantics
open IndexedRefinement (boolNat matrixWord)
set_option maxRecDepth 8192
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
private theorem compareLoaded_scalar_frame (r : IndexedWL.Reg) : wl r∉compareLoaded.scalarWrites := by
  change wl r∉(atoms transfer).scalarWrites∪((WordTypeComparator.program.map Sum.inr Sum.inr).scalarWrites∪{base .result})
  rw [Program.scalarWrites_map]
  simp only [Finset.mem_union,not_or]
  refine ⟨?_,?_,?_⟩
  · simp [transfer,atoms,NatArrayLanguage.sequence,Program.scalarWrites,Atom.scalarWrites,wl,word,base]
  · simp [wl,Finset.mem_image]
  · simp [wl,base]

private theorem compareLoaded_array_frame (a : IndexedWL.Arr) : array a∉compareLoaded.arrayWrites := by
  change array a∉(atoms transfer).arrayWrites∪((WordTypeComparator.program.map Sum.inr Sum.inr).arrayWrites∪∅)
  rw [Program.arrayWrites_map]
  simp only [Finset.union_empty,Finset.mem_union,not_or]
  refine ⟨?_,?_⟩
  · simp [transfer,atoms,NatArrayLanguage.sequence,Program.arrayWrites,Atom.arrayWrites,array,data]
  · simp [array,Finset.mem_image]

private theorem point_scalar_frame (r : IndexedWL.Reg)
    (hr : r∈({.leftCount,.rightCount,.arity,.vectorLimit,.square,.zero,.cellIndex,.rowTodo,.one} : Finset IndexedWL.Reg)) :
    wl r∉point.scalarWrites := by
  have hload : (.inr r : InitialMatrixPrograms.Reg)∉InitialMatrixPrograms.loadPair.scalarWrites :=
    (by decide +kernel : ∀r∈({.leftCount,.rightCount,.arity,.vectorLimit,.square,.zero,.cellIndex,.rowTodo,.one} : Finset IndexedWL.Reg),
      (.inr r : InitialMatrixPrograms.Reg)∉InitialMatrixPrograms.loadPair.scalarWrites) r hr
  have hrow : r≠IndexedWL.Reg.row ∧ r≠IndexedWL.Reg.column := by
    exact (by decide : ∀r∈({.leftCount,.rightCount,.arity,.vectorLimit,.square,.zero,.cellIndex,.rowTodo,.one} : Finset IndexedWL.Reg), r≠IndexedWL.Reg.row ∧ r≠IndexedWL.Reg.column) r hr
  change wl r∉{wl .row,wl .column}∪((InitialMatrixPrograms.loadPair.map Sum.inl Sum.inl).scalarWrites∪compareLoaded.scalarWrites)
  rw [Program.scalarWrites_map]
  simp only [Finset.mem_union,not_or]
  refine ⟨by simpa [wl] using hrow,?_,compareLoaded_scalar_frame r⟩
  simpa [wl,Finset.mem_image] using hload

private theorem point_array_frame (a : IndexedWL.Arr)
    (ha : a∈({.matrix,.fanouts,.targets} : Finset IndexedWL.Arr)) : array a∉point.arrayWrites := by
  have hload : (.inr a : InitialMatrixPrograms.Arr)∉InitialMatrixPrograms.loadPair.arrayWrites :=
    (by decide +kernel : ∀a∈({.matrix,.fanouts,.targets} : Finset IndexedWL.Arr),
      (.inr a : InitialMatrixPrograms.Arr)∉InitialMatrixPrograms.loadPair.arrayWrites) a ha
  change array a∉∅∪((InitialMatrixPrograms.loadPair.map Sum.inl Sum.inl).arrayWrites∪compareLoaded.arrayWrites)
  rw [Program.arrayWrites_map]
  simp only [Finset.empty_union,Finset.mem_union,not_or]
  exact ⟨by simpa [array,Finset.mem_image] using hload,compareLoaded_array_frame a⟩


private theorem bitValue (value : ℕ) (flag : Bool) (hv : value≤1) (he : value=1 ↔ flag=true) : value=boolNat flag := by
  cases flag <;> simp_all [boolNat] <;> omega

variable {G H : Type} [Group G] [Group H] [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H]
variable {n m k : ℕ}
theorem point_runs (e : G≃Fin n) (e' : H≃Fin m)
    (f : Fin n→Fin n→Fin n) (g : Fin m→Fin m→Fin m)
    (hf : ∀x y,e.symm (f x y)=e.symm x*e.symm y)
    (hg : ∀x y,e'.symm (g x y)=e'.symm x*e'.symm y)
    (leftZero : (e 1).val=0) (rightZero : (e' 1).val=0)
    (i : Fin ((n^k+m^k)*(n^k+m^k))) (S : State) (B : ℕ) (bounded : S.Bounded B)
    (ctx : Context (k:=k) f g S) (index : S.scalar (wl .cellIndex)=i.val)
    (one : S.scalar (wl .one)=1) (room : (max n m)^4≤B) :
    ∃t≤201*(B+1)^3,∃T,Runs (storageBound Reg Arr B) point S t T ∧ T.Bounded B ∧
      Context (k:=k) f g T ∧ T.scalar (base .result)=
        boolNat (initialEq e e' (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2) := by
  have hn : 0<n := by have := (e 1).isLt;omega
  have hN : 0<n^k+m^k := Nat.add_pos_left (pow_pos hn _) _
  let divide : Atom Reg Arr := .divmod (wl .row) (wl .column) (wl .cellIndex) (wl .square)
  let U := divide.apply S
  have valid : divide.Valid S := ⟨by decide,by change 0<S.scalar (wl .square);rw [ctx.total_eq];exact hN⟩
  have first := atom_runs bounded divide valid trivial
  have hU := divide.apply_bounded bounded trivial
  have ctxU : Context (k:=k) f g U := by
    change Context (k:=k) f g ((S.setScalar (wl .row) _).setScalar (wl .column) _)
    exact (ctx.scalarUpdate _ _ (by decide)).scalarUpdate _ _ (by decide)
  have row : U.scalar (wl .row)=(finProdFinEquiv.symm i).1.val := by
    simp [U,divide,Atom.apply,Store.setScalar,wl,index,ctx.total_eq]
    change S.scalar (wl .cellIndex) / S.scalar (wl .square) = i.val / (n^k+m^k)
    rw [index,ctx.total_eq]
  have column : U.scalar (wl .column)=(finProdFinEquiv.symm i).2.val := by
    simp [U,divide,Atom.apply,Store.setScalar,wl,index,ctx.total_eq]
    change S.scalar (wl .cellIndex) % S.scalar (wl .square) = i.val % (n^k+m^k)
    rw [index,ctx.total_eq]
  have uone : U.scalar (wl .one)=1 := by simpa [U,divide,Atom.apply,Store.setScalar,wl] using one
  obtain ⟨t,ht,T,last,hT,tvalid,result,vector⟩ := comparePair_runs e e' f g hf hg leftZero rightZero
    (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2 U B hU ctxU.left_eq ctxU.right_eq ctxU.cutoff_eq
    row column ctxU.arity_eq uone ctxU.vector_length ctxU.left_table ctxU.right_table room
  have scalarFrame (r : Reg) (hr : r∈({wl .leftCount,wl .rightCount,wl .arity,wl .vectorLimit,wl .square,wl .zero} : Finset Reg)) :
      T.scalar r=S.scalar r := by
    exact (Runs.seq first last).scalar_eq_of_not_mem r
      (by
        simp only [Finset.mem_insert,Finset.mem_singleton] at hr
        rcases hr with rfl|rfl|rfl|rfl|rfl|rfl <;> exact point_scalar_frame _ (by decide))
  have context : Context (k:=k) f g T := ⟨
    (scalarFrame _ (by decide)).trans ctx.left_eq,(scalarFrame _ (by decide)).trans ctx.right_eq,
    (scalarFrame _ (by decide)).trans ctx.arity_eq,(scalarFrame _ (by decide)).trans ctx.cutoff_eq,
    (scalarFrame _ (by decide)).trans ctx.total_eq,(scalarFrame _ (by decide)).trans ctx.zero_eq,vector,
    ((Runs.seq first last).array_eq_of_not_mem _ (point_array_frame _ (by decide))).trans ctx.left_table,
    ((Runs.seq first last).array_eq_of_not_mem _ (point_array_frame _ (by decide))).trans ctx.right_table⟩
  refine ⟨1+t,by have h1 : 1≤(B+1)^3 := one_le_pow₀ (by omega);omega,T,.seq first last,hT,context,?_⟩
  exact bitValue _ _ tvalid result

theorem build_runs (e : G≃Fin n) (e' : H≃Fin m)
    (f : Fin n→Fin n→Fin n) (g : Fin m→Fin m→Fin m)
    (hf : ∀x y,e.symm (f x y)=e.symm x*e.symm y)
    (hg : ∀x y,e'.symm (g x y)=e'.symm x*e'.symm y)
    (leftZero : (e 1).val=0) (rightZero : (e' 1).val=0)
    (S : State) (B : ℕ) (bounded : S.Bounded B)
    (hn : S.scalar (wl .leftCount)=n) (hm : S.scalar (wl .rightCount)=m)
    (hk : S.scalar (wl .arity)=k) (hcut : S.scalar (wl .vectorLimit)=n^k)
    (htotal : S.scalar (wl .square)=n^k+m^k)
    (leftTable : S.array (array .fanouts)=GroupInitial.tableWord f)
    (rightTable : S.array (array .targets)=GroupInitial.tableWord g)
    (room : (max n m)^4≤B) (matrixRoom : (n^k+m^k)*(n^k+m^k)≤B) :
    ∃t≤210*(B+1)^4,∃T,Runs (storageBound Reg Arr B) build S t T ∧ T.Bounded B ∧
      Context (k:=k) f g T ∧ T.array (array .matrix)=matrixWord (initialRelation (k:=k) e e') := by
  have hp : 0<n := by have := (e 1).isLt;omega
  have h1 : 1≤B := (one_le_pow₀ (by omega : 1≤max n m)).trans room
  have valid : ValidAtoms B prepare S := by
    simp [prepare,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar,wl,htotal] at *
    exact ⟨h1,matrixRoom⟩
  obtain ⟨pre,hU⟩ := atoms_runs bounded prepare valid
  let U := applyAtoms prepare S
  have hn' := hn
  have hm' := hm
  have hk' := hk
  have hcut' := hcut
  have htotal' := htotal
  have leftTable' := leftTable
  have rightTable' := rightTable
  simp only [wl,array] at hn' hm' hk' hcut' htotal' leftTable' rightTable'
  have context : Context (k:=k) f g U := by
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
      simp [U,applyAtoms,prepare,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,wl,array,
        hn',hm',hk',hcut',htotal',leftTable',rightTable']
  have one : U.scalar (wl .one)=1 := by simp [U,applyAtoms,prepare,Atom.apply,Store.setScalar,Store.setArray,wl]
  have total : U.scalar (wl .roundTodo)=(n^k+m^k)*(n^k+m^k) := by
    simp [U,applyAtoms,prepare,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,wl,htotal']
  let value : Fin ((n^k+m^k)*(n^k+m^k))→ℕ := fun i=>boolNat (initialEq e e' (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)
  have pointSpec : ∀i : Fin ((n^k+m^k)*(n^k+m^k)),∀V,Context (k:=k) f g V → V.Bounded B →
      V.scalar (wl .cellIndex)=i.val → V.scalar (wl .rowTodo)=(n^k+m^k)*(n^k+m^k)-i.val →
      V.scalar (wl .one)=1 → ∃t≤201*(B+1)^3,∃W,Runs (storageBound Reg Arr B) point V t W ∧
        W.Bounded B ∧ Context (k:=k) f g W ∧ W.scalar (wl .cellIndex)=i.val ∧
        W.scalar (wl .rowTodo)=(n^k+m^k)*(n^k+m^k)-i.val ∧ W.scalar (wl .one)=1 ∧
        W.scalar (base .result)=value i ∧ W.array (array .matrix)=V.array (array .matrix) := by
    intro i V ctx hV ix todo one
    obtain ⟨t,ht,W,run,hW,hctx,hvalue⟩ := point_runs e e' f g hf hg leftZero rightZero i V B hV ctx ix one room
    exact ⟨t,ht,W,run,hW,hctx,(run.scalar_eq_of_not_mem _ (point_scalar_frame _ (by decide))).trans ix,
      (run.scalar_eq_of_not_mem _ (point_scalar_frame _ (by decide))).trans todo,
      (run.scalar_eq_of_not_mem _ (point_scalar_frame _ (by decide))).trans one,hvalue,
      run.array_eq_of_not_mem _ (point_array_frame _ (by decide))⟩
  obtain ⟨t,ht,T,run,hT,ctxT,output⟩ := ArrayTabulate.tabulate_runs (wl .cellIndex) (wl .rowTodo) (wl .roundTodo)
    (wl .one) (wl .zero) (base .result) (array .matrix) point value (Context (k:=k) f g) B (201*(B+1)^3)
    (fun _ _ h=>h.scalarUpdate _ _ (by decide)) (fun _ _ h=>h.scalarUpdate _ _ (by decide))
    (fun _ _ h=>h.matrixUpdate _) (by decide) (by decide) (by decide) pointSpec U hU context total one context.zero_eq
  have budget : (n^k+m^k)*(n^k+m^k)*(201*(B+1)^3+4)+8≤210*(B+1)^4 := by
    have hh := Nat.mul_le_mul_right (201*(B+1)^3+4) matrixRoom
    nlinarith [sq_nonneg (B*B)]
  refine ⟨4+t,by omega,T,.seq pre run,hT,ctxT,?_⟩
  rw [initialRelation_word]
  exact output

end GroupWL.MachinePrograms.WordMatrixPrograms
