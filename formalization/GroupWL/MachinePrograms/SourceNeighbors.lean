import GroupWL.MachinePrograms.NatArrayCountedLoops
import GroupWL.MachinePrograms.NatArrayProofs
import GroupWL.MachinePrograms.NatArrayFrames

/-! Ordered incidence lists are built by scanning a column of the full scope
table. Zero-coefficient incidences are retained because the scope bit is used. -/
namespace GroupWL.MachinePrograms.SourceNeighbors

open NatArrayLanguage
set_option maxHeartbeats 1200000

inductive Reg where
  | length | stride | offset | index | remaining | one | zero | count | address | flag
  deriving DecidableEq, Fintype
inductive Arr where | input | output deriving DecidableEq, Fintype
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def selected (xs : List ℕ) (stride offset n : ℕ) : List ℕ :=
  (List.range n).filter (fun i => (xs[i*stride+offset]?.getD 0) != 0)

@[simp] theorem selected_zero (xs : List ℕ) (stride offset : ℕ) : selected xs stride offset 0 = [] := rfl

theorem selected_succ (xs : List ℕ) (stride offset n : ℕ) :
    selected xs stride offset (n+1) = selected xs stride offset n++
      if xs[n*stride+offset]?.getD 0 = 0 then [] else [n] := by
  simp [selected,List.range_succ,List.filter_append]
  split_ifs <;> simp_all

theorem selected_length_le (xs : List ℕ) (stride offset n : ℕ) :
    (selected xs stride offset n).length ≤ n := by
  simpa [selected] using List.length_filter_le (fun i => (xs[i*stride+offset]?.getD 0) != 0) (List.range n)

def readAtoms : List (Atom Reg Arr) := [
  .binary .mul .address .index .stride,.binary .add .address .address .offset,
  .read .flag .input .address]

def saveAtoms : List (Atom Reg Arr) := [.write .output .count .index,.binary .add .count .count .one]

def body : Code := .seq (atoms readAtoms) (.branch .flag (atoms saveAtoms) .skip)

def program : Code := .seq
  (atoms [.const .one 1,.const .zero 0,.const .count 0,.allocate .output .length .zero])
  (countedLoop .index .remaining .length .one body)

def afterRead (S : State) : State := applyAtoms readAtoms S

def afterBody (S : State) : State :=
  if (S.array .input)[S.scalar .index*S.scalar .stride+S.scalar .offset]?.getD 0 = 0 then afterRead S
  else applyAtoms saveAtoms (afterRead S)

theorem body_runs (S : State) (M : ℕ) (bounded : S.Bounded M)
    (hone : S.scalar .one=1)
    (hread : S.scalar .index*S.scalar .stride+S.scalar .offset < (S.array .input).length)
    (hwrite : S.scalar .count < (S.array .output).length) (hcount : S.scalar .count+1≤M) :
    ∃ t ≤ 6, Runs (storageBound Reg Arr M) body S t (afterBody S) ∧ (afterBody S).Bounded M := by
  have hl := bounded.2.1 Arr.input
  have hmul : S.scalar .index*S.scalar .stride ≤ M := by omega
  have hadd : S.scalar .index*S.scalar .stride+S.scalar .offset ≤ M := by omega
  have hvalid : ValidAtoms M readAtoms S := by
    simp [readAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,hmul,hadd,hread]
  obtain ⟨first,hAB⟩ := atoms_runs bounded readAtoms hvalid
  have hflag : (afterRead S).scalar .flag =
      (S.array .input)[S.scalar .index*S.scalar .stride+S.scalar .offset]?.getD 0 := by
    simp [afterRead,readAtoms,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar]
  by_cases hz : (S.array .input)[S.scalar .index*S.scalar .stride+S.scalar .offset]?.getD 0 = 0
  · refine ⟨4,by omega,?_,?_⟩
    · simpa [body,afterBody,hz,readAtoms] using
        first.seq (Runs.branch_zero (hflag.trans hz) (Runs.skip (Store.size_le_of_bounded hAB)))
    · simpa [afterBody,hz] using hAB
  · have hsave : ValidAtoms M saveAtoms (afterRead S) := by
      simp [saveAtoms,afterRead,readAtoms,applyAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,
        Atom.apply,BinaryOp.eval,Store.setScalar,hwrite,hone,hcount]
    obtain ⟨last,hLB⟩ := atoms_runs hAB saveAtoms hsave
    refine ⟨6,by omega,?_,?_⟩
    · simpa [body,afterBody,hz,readAtoms,saveAtoms] using first.seq
        (Runs.branch_nonzero (by change (afterRead S).scalar .flag ≠ 0; rw [hflag]; exact hz) last)
    · simpa [afterBody,hz] using hLB

theorem take_set_append (xs : List ℕ) (n v : ℕ) (hn : n<xs.length) :
    (xs.set n v).take (n+1) = xs.take n++[v] := by
  rw [List.take_add_one,List.take_set_of_le (show n ≤ n from le_rfl),List.getElem?_set_self hn]
  rfl

theorem program_runs (S : State) (xs : List ℕ) (n stride offset M : ℕ)
    (bounded : S.Bounded M) (hM : 1≤M)
    (hinput : S.array .input=xs) (hlen : S.scalar .length=n)
    (hstride : S.scalar .stride=stride) (hoffset : S.scalar .offset=offset)
    (hread : ∀ i<n, i*stride+offset < xs.length) :
    ∃ t ≤ n*9+7, ∃ T, Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧
      T.array .input=xs ∧ T.scalar .count=(selected xs stride offset n).length ∧
      (T.array .output).length=n ∧
      (T.array .output).take (T.scalar .count)=selected xs stride offset n := by
  have hnM : n≤M := hlen ▸ bounded.1 Reg.length
  let init : List (Atom Reg Arr) := [.const .one 1,.const .zero 0,.const .count 0,.allocate .output .length .zero]
  have hvalid : ValidAtoms M init S := by simp [init,ValidAtoms,Atom.Valid,Atom.SmallResult,hM]
  obtain ⟨first,hUB⟩ := atoms_runs bounded init hvalid
  let U := applyAtoms init S
  have hU : U = (((S.setScalar .one 1).setScalar .zero 0).setScalar .count 0).setArray .output (List.replicate n 0) := by
    simp [U,init,applyAtoms,Atom.apply,Store.setScalar,hlen]
  let I (i : ℕ) (V : State) : Prop := V.Bounded M ∧ V.array .input=xs ∧
    V.scalar .length=n ∧ V.scalar .stride=stride ∧ V.scalar .offset=offset ∧
    V.scalar .index=i ∧ V.scalar .remaining=n-i ∧ V.scalar .one=1 ∧
    V.scalar .count=(selected xs stride offset i).length ∧ (V.array .output).length=n ∧
    (V.array .output).take (V.scalar .count)=selected xs stride offset i
  have hcopy : (U.setScalar .remaining (U.scalar .length)).Bounded M := hUB.setScalar _ (hUB.1 _)
  have start : I 0 ((U.setScalar .remaining (U.scalar .length)).setScalar .index 0) := by
    refine ⟨hcopy.setScalar _ (Nat.zero_le M),?_⟩
    rw [hU]
    simp [Store.setScalar,Store.setArray,hinput,hlen,hstride,hoffset]
  have control : ∀ i≤n, ∀ V, I i V → V.scalar .index=i ∧ V.scalar .remaining=n-i ∧
      V.scalar .one=1 ∧ V.size≤storageBound Reg Arr M := by
    intro i hi V hv
    exact ⟨hv.2.2.2.2.2.1,hv.2.2.2.2.2.2.1,hv.2.2.2.2.2.2.2.1,Store.size_le_of_bounded hv.1⟩
  have step : ∀ i<n, ∀ V, I i V → ∃ t≤6, ∃ W, Runs (storageBound Reg Arr M) body V t W ∧
      W.scalar .index=i ∧ W.scalar .remaining=n-i ∧ W.scalar .one=1 ∧
      (W.setScalar .index (i+1)).size≤storageBound Reg Arr M ∧ I (i+1) (advance .index .remaining W) := by
    intro i hi V hv
    rcases hv with ⟨hVB,hVi,hVn,hVs,hVo,hVidx,hVrem,hVone,hVc,hVlen,hVtake⟩
    have hc : V.scalar .count ≤ i := by rw [hVc]; exact selected_length_le _ _ _ _
    obtain ⟨t,ht,run,hWB⟩ := body_runs V M hVB hVone
      (by rw [hVi,hVidx,hVs,hVo]; exact hread i hi)
      (by rw [hVlen]; omega) (by omega)
    let W := afterBody V
    have hidx : W.scalar .index=i := by
      exact (run.scalar_eq_of_not_mem .index (by decide)).trans hVidx
    have hrem : W.scalar .remaining=n-i := by
      exact (run.scalar_eq_of_not_mem .remaining (by decide)).trans hVrem
    have hone : W.scalar .one=1 := by
      exact (run.scalar_eq_of_not_mem .one (by decide)).trans hVone
    have hnextB : (advance .index .remaining W).Bounded M :=
      (hWB.setScalar _ (by rw [hidx]; omega)).setScalar _ ((Nat.sub_le _ _).trans (hWB.1 _))
    refine ⟨t,ht,W,run,hidx,hrem,hone,Store.size_le_of_bounded (hWB.setScalar _ (by omega)),hnextB,?_⟩
    have hiw : V.scalar .count < (V.array .output).length := by rw [hVlen]; omega
    have hVtake' : (V.array .output).take (selected xs stride offset i).length = selected xs stride offset i := by
      simpa only [hVc] using hVtake
    by_cases hz : xs[i*stride+offset]?.getD 0=0
    · simp [W,afterBody,afterRead,readAtoms,applyAtoms,Atom.apply,BinaryOp.eval,
        Store.setScalar,advance,hVidx,hVrem,hVone,hVi,hVn,hVs,hVo,hVc,hVlen,hVtake',
        selected_succ,hz]
      omega
    · simp [W,afterBody,afterRead,readAtoms,saveAtoms,applyAtoms,Atom.apply,BinaryOp.eval,
        Store.setScalar,Store.setArray,advance,hVidx,hVrem,hVone,hVi,hVn,hVs,hVo,hVc,hVlen,
        selected_succ,hz]
      refine ⟨by omega,?_⟩
      simpa [hVc] using (take_set_append (V.array .output) (V.scalar .count) i hiw).trans
        (congrArg (fun a => a++[i]) hVtake)
  obtain ⟨t,ht,T,last,hT⟩ := countedLoop_runs (storageBound Reg Arr M) .index .remaining .length .one body n 6 I U
    (Store.size_le_of_bounded hUB) (Store.size_le_of_bounded hcopy) start control (by decide) (by decide) step
  refine ⟨4+t,by omega,T,first.seq last,hT.1,hT.2.1,hT.2.2.2.2.2.2.2.2.1,hT.2.2.2.2.2.2.2.2.2.1,
    hT.2.2.2.2.2.2.2.2.2.2⟩

end GroupWL.MachinePrograms.SourceNeighbors
