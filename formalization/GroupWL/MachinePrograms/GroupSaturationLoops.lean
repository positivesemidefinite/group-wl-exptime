import GroupWL.MachinePrograms.GroupSaturation

/-! Quadratic pair scans and cubic finite saturation loops. -/
namespace GroupWL.MachinePrograms.GroupSaturation

open NatArrayLanguage FiniteSetArrays
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

private def controls : Finset Reg := {.order,.one,.total,.position,.todo,.round,.roundTodo}

theorem stepPair_scalarFrame {B S T t} (h : Runs B stepPair S t T)
    (r : Reg) (hr : r∈controls) : T.scalar r=S.scalar r := by
  exact h.scalar_eq_of_not_mem r ((by decide : ∀ r∈controls,r∉stepPair.scalarWrites) r hr)

theorem stepPair_arrayFrame {B S T t} (h : Runs B stepPair S t T)
    (a : Arr) (ha : a≠.next) : T.array a=S.array a := by
  apply h.array_eq_of_not_mem
  cases a <;> simp_all [stepPair,atoms,pairAtoms,NatArrayLanguage.sequence,Program.arrayWrites,Atom.arrayWrites]

private structure PairState (S : State) (n M : ℕ) (C : Finset (Fin n))
    (op : Fin n → Fin n → Fin n) (i : ℕ) (T : State) : Prop where
  bounded : T.Bounded M
  order_eq : T.scalar .order=n
  one_eq : T.scalar .one=1
  position_eq : T.scalar .position=i
  todo_eq : T.scalar .todo=n*n-i
  table_eq : T.array .table=S.array .table
  current_eq : T.array .current=word C
  next_eq : T.array .next=word (scanPrefix C op i)

theorem pairLoop_runs (S : State) (n M : ℕ) (C : Finset (Fin n))
    (op : Fin n → Fin n → Fin n)
    (hb : S.Bounded M) (hn : S.scalar .order=n) (h1 : S.scalar .one=1)
    (htotal : S.scalar .total=n*n) (hcurrent : S.array .current=word C)
    (hnext : S.array .next=word C) (hlen : (S.array .table).length=n*n)
    (hread : ∀ i : Fin (n*n),(S.array .table)[i.val]?.getD 0=
      (op (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2).val)
    (hroom : n*n≤M) :
    ∃ t≤10*(n*n)+3,∃ T,
      Runs (storageBound Reg Arr M) (countedLoop .position .todo .total .one stepPair) S t T ∧
      T.Bounded M ∧ T.array .next=word (C ∪ C.biUnion (fun a => C.image (op a))) := by
  let I := PairState S n M C op
  have hcopy : (S.setScalar .todo (S.scalar .total)).Bounded M :=
    hb.setScalar _ (by simpa [htotal] using hroom)
  have hstart : I 0 ((S.setScalar .todo (S.scalar .total)).setScalar .position 0) := by
    refine ⟨hcopy.setScalar _ (by omega),?_,?_,?_,?_,?_,?_,?_⟩
    · simp [hn]
    · simp [h1]
    · simp
    · simp [htotal]
    · rfl
    · exact hcurrent
    · simpa using hnext
  have hcontrol : ∀ i≤n*n,∀ T,I i T →
      T.scalar .position=i ∧ T.scalar .todo=n*n-i ∧ T.scalar .one=1 ∧
        T.size≤storageBound Reg Arr M := by
    intro i hi T hT
    exact ⟨hT.position_eq,hT.todo_eq,hT.one_eq,Store.size_le_of_bounded hT.bounded⟩
  have hstep : ∀ i<n*n,∀ T,I i T →
      ∃ t≤7,∃ U,Runs (storageBound Reg Arr M) stepPair T t U ∧
        U.scalar .position=i ∧ U.scalar .todo=n*n-i ∧ U.scalar .one=1 ∧
        (U.setScalar .position (i+1)).size≤storageBound Reg Arr M ∧
        I (i+1) (advance .position .todo U) := by
    intro i hi T hT
    obtain ⟨t,ht,U,run,hU,ho⟩ := stepPair_runs T n M C (scanPrefix C op i) op ⟨i,hi⟩
      hT.bounded hT.order_eq hT.one_eq hT.position_eq hT.current_eq hT.next_eq
      (by simpa [hT.table_eq] using hlen) (by simpa [hT.table_eq] using hread ⟨i,hi⟩) hroom
    have frame (r : Reg) (hr : r∈controls) := stepPair_scalarFrame run r hr
    have hp : U.scalar .position=i := (frame _ (by decide)).trans hT.position_eq
    have hr : U.scalar .todo=n*n-i := (frame _ (by decide)).trans hT.todo_eq
    have hone : U.scalar .one=1 := (frame _ (by decide)).trans hT.one_eq
    have hmid := hU.setScalar Reg.position (show i+1≤M by omega)
    refine ⟨t,ht,U,run,hp,hr,hone,Store.size_le_of_bounded hmid,?_⟩
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [advance,hp] using hmid.setScalar Reg.todo
        (show U.scalar .todo-1≤M by rw [hr]; omega)
    · simpa [advance] using (frame .order (by decide)).trans hT.order_eq
    · simpa [advance] using hone
    · simp [advance,hp]
    · simp [advance,hr]; omega
    · exact (stepPair_arrayFrame run .table (by decide)).trans hT.table_eq
    · exact (stepPair_arrayFrame run .current (by decide)).trans hT.current_eq
    · simpa only [prefix_succ C op i hi] using ho
  obtain ⟨t,ht,T,run,hT⟩ := countedLoop_runs (storageBound Reg Arr M)
    .position .todo .total .one stepPair (n*n) 7 I S
    (Store.size_le_of_bounded hb) (Store.size_le_of_bounded hcopy) hstart hcontrol
    (by decide) (by decide) hstep
  exact ⟨t,by omega,T,run,hT.bounded,by simpa only [prefix_complete] using hT.next_eq⟩

theorem step_runs (S : State) (n M : ℕ) (C : Finset (Fin n))
    (op : Fin n → Fin n → Fin n)
    (hb : S.Bounded M) (hn : S.scalar .order=n) (h1 : S.scalar .one=1)
    (htotal : S.scalar .total=n*n) (hcurrent : S.array .current=word C)
    (hlen : (S.array .table).length=n*n)
    (hread : ∀ i : Fin (n*n),(S.array .table)[i.val]?.getD 0=
      (op (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2).val)
    (hroom : n*n≤M) :
    ∃ t≤10*(n*n)+5,∃ T,Runs (storageBound Reg Arr M) step S t T ∧
      T.Bounded M ∧ T.array .current=word (C ∪ C.biUnion (fun a => C.image (op a))) := by
  let U := (Atom.copyArray Arr.next Arr.current).apply S
  have hU : U.Bounded M := Atom.apply_bounded hb _ trivial
  have pre := atom_runs hb (.copyArray .next .current) trivial trivial
  obtain ⟨t,ht,T,run,hT,ho⟩ := pairLoop_runs U n M C op hU hn h1 htotal hcurrent
    (by simpa [U,Atom.apply,Store.setArray] using hcurrent)
    (by simpa [U,Atom.apply,Store.setArray] using hlen)
    (by simpa [U,Atom.apply,Store.setArray] using hread) hroom
  let V := (Atom.copyArray Arr.current Arr.next).apply T
  have hV : V.Bounded M := Atom.apply_bounded hT _ trivial
  have post := atom_runs hT (.copyArray .current .next) trivial trivial
  refine ⟨1+(t+(1+0)),by omega,V,.seq pre (.seq run (.seq post (.skip (Store.size_le_of_bounded hV)))),hV,?_⟩
  simpa [V,Atom.apply,Store.setArray] using ho

end GroupWL.MachinePrograms.GroupSaturation
