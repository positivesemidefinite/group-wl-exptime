import GroupWL.MachinePrograms.GroupSaturationLoops

/-! Complete, bounded multiplication-only saturation of an initial mask. -/
namespace GroupWL.MachinePrograms.GroupSaturation

open NatArrayLanguage FiniteSetArrays
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def closureSet {n : ℕ} (op : Fin n → Fin n → Fin n) (C : Finset (Fin n)) : ℕ → Finset (Fin n)
  | 0 => C
  | i+1 => closureSet op C i ∪ (closureSet op C i).biUnion (fun a => (closureSet op C i).image (op a))

private def outerControls : Finset Reg := {.order,.one,.total,.round,.roundTodo}

theorem step_scalarFrame {B S T t} (h : Runs B step S t T)
    (r : Reg) (hr : r∈outerControls) : T.scalar r=S.scalar r :=
  h.scalar_eq_of_not_mem r ((by decide : ∀ r∈outerControls,r∉step.scalarWrites) r hr)

theorem step_tableFrame {B S T t} (h : Runs B step S t T) : T.array .table=S.array .table :=
  h.array_eq_of_not_mem .table (by decide)

private structure SaturationState (S : State) (n M : ℕ) (C : Finset (Fin n))
    (op : Fin n → Fin n → Fin n) (i : ℕ) (T : State) : Prop where
  bounded : T.Bounded M
  order_eq : T.scalar .order=n
  one_eq : T.scalar .one=1
  total_eq : T.scalar .total=n*n
  round_eq : T.scalar .round=i
  todo_eq : T.scalar .roundTodo=n-i
  table_eq : T.array .table=S.array .table
  current_eq : T.array .current=word (closureSet op C i)

theorem saturationLoop_runs (S : State) (n M : ℕ) (C : Finset (Fin n))
    (op : Fin n → Fin n → Fin n)
    (hb : S.Bounded M) (hn : S.scalar .order=n) (h1 : S.scalar .one=1)
    (htotal : S.scalar .total=n*n) (hcurrent : S.array .current=word C)
    (hlen : (S.array .table).length=n*n)
    (hread : ∀ i : Fin (n*n),(S.array .table)[i.val]?.getD 0=
      (op (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2).val)
    (hpos : 0<n) (hroom : n*n≤M) :
    ∃ t≤n*(10*(n*n)+8)+3,∃ T,
      Runs (storageBound Reg Arr M) (countedLoop .round .roundTodo .order .one step) S t T ∧
      T.Bounded M ∧ T.array .current=word (closureSet op C n) := by
  have hnM : n≤M := by nlinarith
  let I := SaturationState S n M C op
  have hcopy : (S.setScalar .roundTodo (S.scalar .order)).Bounded M :=
    hb.setScalar _ (by simpa [hn] using hnM)
  have hstart : I 0 ((S.setScalar .roundTodo (S.scalar .order)).setScalar .round 0) := by
    refine ⟨hcopy.setScalar _ (by omega),?_,?_,?_,?_,?_,?_,?_⟩
    · simp [hn]
    · simp [h1]
    · simp [htotal]
    · simp
    · simp [hn]
    · rfl
    · exact hcurrent
  have hcontrol : ∀ i≤n,∀ T,I i T →
      T.scalar .round=i ∧ T.scalar .roundTodo=n-i ∧ T.scalar .one=1 ∧
        T.size≤storageBound Reg Arr M := by
    intro i hi T hT
    exact ⟨hT.round_eq,hT.todo_eq,hT.one_eq,Store.size_le_of_bounded hT.bounded⟩
  have hstep : ∀ i<n,∀ T,I i T →
      ∃ t≤10*(n*n)+5,∃ U,Runs (storageBound Reg Arr M) step T t U ∧
        U.scalar .round=i ∧ U.scalar .roundTodo=n-i ∧ U.scalar .one=1 ∧
        (U.setScalar .round (i+1)).size≤storageBound Reg Arr M ∧
        I (i+1) (advance .round .roundTodo U) := by
    intro i hi T hT
    obtain ⟨t,ht,U,run,hU,ho⟩ := step_runs T n M (closureSet op C i) op
      hT.bounded hT.order_eq hT.one_eq hT.total_eq hT.current_eq
      (by simpa [hT.table_eq] using hlen) (by simpa [hT.table_eq] using hread) hroom
    have frame (r : Reg) (hr : r∈outerControls) := step_scalarFrame run r hr
    have hp : U.scalar .round=i := (frame _ (by decide)).trans hT.round_eq
    have hr : U.scalar .roundTodo=n-i := (frame _ (by decide)).trans hT.todo_eq
    have hone : U.scalar .one=1 := (frame _ (by decide)).trans hT.one_eq
    have hmid := hU.setScalar Reg.round (show i+1≤M by omega)
    refine ⟨t,ht,U,run,hp,hr,hone,Store.size_le_of_bounded hmid,?_⟩
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [advance,hp] using hmid.setScalar Reg.roundTodo
        (show U.scalar .roundTodo-1≤M by rw [hr]; omega)
    · simpa [advance] using (frame .order (by decide)).trans hT.order_eq
    · simpa [advance] using hone
    · simpa [advance] using (frame .total (by decide)).trans hT.total_eq
    · simp [advance,hp]
    · simp [advance,hr]; omega
    · exact (step_tableFrame run).trans hT.table_eq
    · exact ho
  obtain ⟨t,ht,T,run,hT⟩ := countedLoop_runs (storageBound Reg Arr M)
    .round .roundTodo .order .one step n (10*(n*n)+5) I S
    (Store.size_le_of_bounded hb) (Store.size_le_of_bounded hcopy) hstart hcontrol
    (by decide) (by decide) hstep
  exact ⟨t,ht,T,run,hT.bounded,hT.current_eq⟩

theorem saturate_runs (S : State) (n M : ℕ) (C : Finset (Fin n))
    (op : Fin n → Fin n → Fin n)
    (hb : S.Bounded M) (hn : S.scalar .order=n) (hcurrent : S.array .current=word C)
    (hlen : (S.array .table).length=n*n)
    (hread : ∀ i : Fin (n*n),(S.array .table)[i.val]?.getD 0=
      (op (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2).val)
    (hpos : 0<n) (hroom : n*n≤M) :
    ∃ t≤10*n^3+8*n+5,∃ T,Runs (storageBound Reg Arr M) saturate S t T ∧
      T.Bounded M ∧ T.array .current=word (closureSet op C n) := by
  have hM : 1≤M := by nlinarith
  let U := S.setScalar .one 1
  let V := U.setScalar .total (n*n)
  have hU : U.Bounded M := hb.setScalar _ hM
  have hV : V.Bounded M := hU.setScalar _ hroom
  have pre₁ : Runs (storageBound Reg Arr M) (.atom (.const .one 1)) S 1 U := atom_runs hb _ trivial hM
  have pre₂ : Runs (storageBound Reg Arr M) (.atom (.binary .mul .total .order .order)) U 1 V := by
    have he : (Atom.binary BinaryOp.mul Reg.total Reg.order Reg.order).apply U=V := by
      simp [Atom.apply,BinaryOp.eval,U,V,hn]
    rw [←he]
    exact atom_runs hU _ trivial (by simpa [Atom.SmallResult,BinaryOp.eval,U,hn] using hroom)
  obtain ⟨t,ht,T,run,hT,ho⟩ := saturationLoop_runs V n M C op hV
    (by simp [V,U,hn]) (by simp [V,U]) (by simp [V]) hcurrent hlen hread hpos hroom
  refine ⟨1+(1+(t+0)),by nlinarith,T,.seq pre₁ (.seq pre₂ (.seq run (.skip run.end_bound))),hT,ho⟩

end GroupWL.MachinePrograms.GroupSaturation
