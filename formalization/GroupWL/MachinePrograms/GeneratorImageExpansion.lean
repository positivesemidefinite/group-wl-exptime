import GroupWL.MachinePrograms.GeneratorImages

namespace GroupWL.MachinePrograms.GeneratorImages
open NatArrayLanguage ArrayTabulation
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

theorem rowCode_scalarFrame {B S T t} (h : Runs B rowCode S t T) (r : Control) :
    T.scalar (.inr r)=S.scalar (.inr r) :=
  h.scalar_eq_of_not_mem _ ((by decide : ∀ r : Control,Sum.inr r∉rowCode.scalarWrites) r)

theorem rowCode_inputFrame {B S T t} (h : Runs B rowCode S t T) :
    T.array (.inl .input)=S.array (.inl .input) := h.array_eq_of_not_mem _ (by decide)

private structure ImageState (S : State) (M rows cols identity i : ℕ) (T : State) : Prop where
  bounded : T.Bounded M
  cols_eq : T.scalar (.inr .cols)=cols
  identity_eq : T.scalar (.inr .identity)=identity
  one_eq : T.scalar (.inr .one)=1
  row_eq : T.scalar (.inr .row)=i
  todo_eq : T.scalar (.inr .todo)=rows-i
  input_eq : T.array (.inl .input)=S.array (.inl .input)
  output_prefix : Prefix (rowImage (S.array (.inl .input)) cols identity) rows i (T.array (.inr .images))

theorem expansionLoop_runs (S : State) (M rows cols identity : ℕ)
    (hb : S.Bounded M) (hrows : S.scalar (.inr .rows)=rows) (hc : S.scalar (.inr .cols)=cols)
    (he : S.scalar (.inr .identity)=identity) (hone : S.scalar (.inr .one)=1)
    (helt : identity<cols) (hlen : (S.array (.inl .input)).length=rows*cols)
    (hout : (S.array (.inr .images)).length=rows) (hroom : rows*cols≤M) :
    ∃ t≤rows*(9*cols+13)+3,∃ T,
      Runs (storageBound Reg Arr M) (countedLoop (.inr .row) (.inr .todo) (.inr .rows) (.inr .one) rowCode) S t T ∧
      T.Bounded M ∧ T.array (.inr .images)=List.ofFn (fun i : Fin rows => rowImage (S.array (.inl .input)) cols identity i.val) := by
  have hrowsM : rows≤M := by simpa [hrows] using hb.1 (.inr .rows)
  let I := ImageState S M rows cols identity
  have hcopy := hb.setScalar (Sum.inr Control.todo) (show S.scalar (.inr .rows)≤M from hb.1 _)
  have hstart : I 0 ((S.setScalar (.inr .todo) (S.scalar (.inr .rows))).setScalar (.inr .row) 0) := by
    refine ⟨hcopy.setScalar _ (by omega),?_,?_,?_,?_,?_,?_,?_⟩
    · simp [hc]
    · simp [he]
    · simp [hone]
    · simp
    · simp [hrows]
    · rfl
    · exact ⟨hout,by omega⟩
  have hcontrol : ∀ i≤rows,∀ T,I i T →
      T.scalar (.inr .row)=i ∧ T.scalar (.inr .todo)=rows-i ∧ T.scalar (.inr .one)=1 ∧
        T.size≤storageBound Reg Arr M := by
    intro i hi T hT
    exact ⟨hT.row_eq,hT.todo_eq,hT.one_eq,Store.size_le_of_bounded hT.bounded⟩
  have hstep : ∀ i<rows,∀ T,I i T →
      ∃ t≤9*cols+10,∃ U,Runs (storageBound Reg Arr M) rowCode T t U ∧
        U.scalar (.inr .row)=i ∧ U.scalar (.inr .todo)=rows-i ∧ U.scalar (.inr .one)=1 ∧
        (U.setScalar (.inr .row) (i+1)).size≤storageBound Reg Arr M ∧
        I (i+1) (advance (.inr .row) (.inr .todo) U) := by
    intro i hi T hT
    obtain ⟨t,ht,U,run,hU,ho⟩ := rowCode_runs T M rows cols identity i hT.bounded hT.cols_eq
      hT.identity_eq hT.row_eq hi helt (by simpa [hT.input_eq] using hlen) hT.output_prefix.1 hroom
    have hrow := (rowCode_scalarFrame run .row).trans hT.row_eq
    have htodo := (rowCode_scalarFrame run .todo).trans hT.todo_eq
    have h1 := (rowCode_scalarFrame run .one).trans hT.one_eq
    have hmid := hU.setScalar (Sum.inr Control.row) (show i+1≤M by omega)
    refine ⟨t,ht,U,run,hrow,htodo,h1,Store.size_le_of_bounded hmid,?_⟩
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [advance,hrow] using hmid.setScalar (Sum.inr Control.todo)
        (show U.scalar (.inr .todo)-1≤M by rw [htodo]; omega)
    · simpa [advance] using (rowCode_scalarFrame run .cols).trans hT.cols_eq
    · simpa [advance] using (rowCode_scalarFrame run .identity).trans hT.identity_eq
    · simpa [advance] using h1
    · simp [advance,hrow]
    · simp [advance,htodo]; omega
    · exact (rowCode_inputFrame run).trans hT.input_eq
    · change Prefix _ rows (i+1) (U.array (.inr .images))
      rw [ho,hT.input_eq]
      exact hT.output_prefix.write hi
  obtain ⟨t,ht,T,run,hT⟩ := countedLoop_runs (storageBound Reg Arr M)
    (.inr .row) (.inr .todo) (.inr .rows) (.inr .one) rowCode rows (9*cols+10) I S
    (Store.size_le_of_bounded hb) (Store.size_le_of_bounded hcopy) hstart hcontrol
    (by decide) (by decide) hstep
  exact ⟨t,ht,T,run,hT.bounded,hT.output_prefix.complete⟩

theorem expand_runs (S : State) (M rows cols identity : ℕ)
    (hb : S.Bounded M) (hrows : S.scalar (.inr .rows)=rows) (hc : S.scalar (.inr .cols)=cols)
    (he : S.scalar (.inr .identity)=identity) (helt : identity<cols)
    (hlen : (S.array (.inl .input)).length=rows*cols) (hroom : rows*cols≤M) (hM : 1≤M) :
    ∃ t≤rows*(9*cols+13)+5,∃ T,Runs (storageBound Reg Arr M) expand S t T ∧
      T.Bounded M ∧ T.array (.inr .images)=List.ofFn (fun i : Fin rows => rowImage (S.array (.inl .input)) cols identity i.val) := by
  let U := S.setScalar (.inr .one) 1
  have hU : U.Bounded M := hb.setScalar _ hM
  have pre₁ : Runs (storageBound Reg Arr M) (.atom (.const (.inr .one) 1)) S 1 U := atom_runs hb _ trivial hM
  let V := (Atom.allocate (Sum.inr Output.images) (Sum.inr Control.rows) (Sum.inr Control.identity)).apply U
  have hV : V.Bounded M := Atom.apply_bounded hU _ trivial
  have pre₂ := atom_runs hU (.allocate (.inr .images) (.inr .rows) (.inr .identity)) trivial trivial
  obtain ⟨t,ht,T,run,hT,ho⟩ := expansionLoop_runs V M rows cols identity hV
    (by simp [V,U,Atom.apply,hrows]) (by simp [V,U,Atom.apply,hc])
    (by simp [V,U,Atom.apply,he]) (by simp [V,U,Atom.apply]) helt
    (by simpa [V,Atom.apply,Store.setArray,U] using hlen)
    (by simp [V,Atom.apply,Store.setArray,U,hrows]) hroom
  refine ⟨1+(1+(t+0)),by omega,T,.seq pre₁ (.seq pre₂ (.seq run (.skip run.end_bound))),hT,?_⟩
  simpa [V,Atom.apply,Store.setArray,U] using ho

end GroupWL.MachinePrograms.GeneratorImages
