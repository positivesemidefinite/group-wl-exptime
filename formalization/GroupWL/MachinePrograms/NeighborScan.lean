import GroupWL.MachinePrograms.ArrayTabulate
import GroupWL.MachinePrograms.NatArrayFrames

/-! Count a row's marked neighbors and select its requested neighbor by a bounded scan. -/
namespace GroupWL.MachinePrograms.NeighborScan
open NatArrayLanguage
abbrev Reg := Fin 12
abbrev Arr := Unit
abbrev Code := Program Reg Arr
set_option maxRecDepth 4096

def neighbors (xs : List ℕ) (n row stop : ℕ) : List ℕ :=
  (List.range stop).filter (fun j => IndexedRefinement.read xs (j+n*row)==1)

theorem neighbors_succ (xs : List ℕ) (n row stop : ℕ) :
    neighbors xs n row (stop+1)=if IndexedRefinement.read xs (stop+n*row)=1 then
      neighbors xs n row stop++[stop] else neighbors xs n row stop := by
  simp [neighbors,List.range_succ,List.filter_append]
  split_ifs <;> simp_all

theorem read_append_singleton (xs : List ℕ) (x i : ℕ) :
    IndexedRefinement.read (xs++[x]) i=if i=xs.length then x else IndexedRefinement.read xs i := by
  by_cases hi : i<xs.length
  · simp [IndexedRefinement.read,List.getElem?_append,hi,show i≠xs.length by omega]
  · by_cases he : i=xs.length
    · simp [IndexedRefinement.read,List.getElem?_append,he]
    · have hx : xs[i]?=none := List.getElem?_eq_none (by omega)
      have hdiff : i-xs.length≠0 := by omega
      simp [IndexedRefinement.read,List.getElem?_append,hi,he,hx,hdiff]

def active : Code := .seq (.atom (.binary .eq 10 6 2))
  (.seq (.branch 10 (.atom (.copy 7 3)) .skip) (.atom (.binary .add 6 6 5)))

theorem active_runs (S : Store Reg Arr) (B count slot i z : ℕ) (hS : S.Bounded B)
    (hc : S.scalar 6=count) (hs : S.scalar 2=slot) (hi : S.scalar 3=i)
    (hz : S.scalar 7=z) (hone : S.scalar 5=1) (hnext : count+1≤B) :
    ∃ t≤4,∃ T,Runs (storageBound Reg Arr B) active S t T ∧ T.Bounded B ∧
      T.scalar 6=count+1 ∧ T.scalar 7=if count=slot then i else z := by
  have hflag : (Atom.binary .eq 10 6 2).SmallResult B S := by
    change (if S.scalar 6=S.scalar 2 then 1 else 0)≤B
    split_ifs <;>omega
  have first := atom_runs hS (.binary .eq 10 6 2) trivial hflag
  let U := (Atom.binary .eq 10 6 2).apply S
  have hU : U.Bounded B := Atom.apply_bounded hS _ hflag
  by_cases he : count=slot
  · have copy := atom_runs hU (.copy 7 3) trivial trivial
    let V := (Atom.copy 7 3).apply U
    have hV : V.Bounded B := Atom.apply_bounded hU _ trivial
    have small : (Atom.binary .add 6 6 5).SmallResult B V := by
      simpa [Atom.SmallResult,V,U,Atom.apply,BinaryOp.eval,Store.setScalar,hc,hone] using hnext
    have last := atom_runs hV (.binary .add 6 6 5) trivial small
    refine ⟨4,le_rfl,_,Runs.seq first (Runs.seq (Runs.branch_nonzero ?_ copy) last),
      Atom.apply_bounded hV _ small,?_,?_⟩
    · change U.scalar 10≠0;simp [U,Atom.apply,BinaryOp.eval,Store.setScalar,hc,hs,he]
    · simp [V,U,Atom.apply,BinaryOp.eval,Store.setScalar,hc,hone]
    · simp [V,U,Atom.apply,BinaryOp.eval,Store.setScalar,hi,he]
  · have small : (Atom.binary .add 6 6 5).SmallResult B U := by
      simpa [Atom.SmallResult,U,Atom.apply,BinaryOp.eval,Store.setScalar,hc,hone] using hnext
    have last := atom_runs hU (.binary .add 6 6 5) trivial small
    refine ⟨3,by omega,_,Runs.seq first (Runs.seq (Runs.branch_zero ?_ (Runs.skip
      (Store.size_le_of_bounded hU))) last),Atom.apply_bounded hU _ small,?_,?_⟩
    · change U.scalar 10=0;simp [U,Atom.apply,BinaryOp.eval,Store.setScalar,hc,hs,he]
    · simp [U,Atom.apply,BinaryOp.eval,Store.setScalar,hc,hone]
    · simp [U,Atom.apply,BinaryOp.eval,Store.setScalar,hz,he]

def prepare : List (Atom Reg Arr) := [.binary .mul 8 0 1,.binary .add 8 3 8,.read 9 () 8,.binary .eq 9 9 5]
def body : Code := .seq (atoms prepare) (.branch 9 active .skip)

theorem body_runs (xs ys : List ℕ) (n row slot i B : ℕ) (S : Store Reg Arr)
    (hS : S.Bounded B) (hn : S.scalar 0=n) (hr : S.scalar 1=row) (hs : S.scalar 2=slot)
    (hi : S.scalar 3=i) (hone : S.scalar 5=1) (hc : S.scalar 6=ys.length)
    (hp : S.scalar 7=IndexedRefinement.read ys slot) (ha : S.array ()=xs)
    (hlen : xs.length=n*n) (hrow : row<n) (hcol : i<n) (hy : ys.length≤ i) (hroom : n*n≤B) :
    ∃ t≤9,∃ T,Runs (storageBound Reg Arr B) body S t T ∧ T.Bounded B ∧
      T.scalar 6=(if IndexedRefinement.read xs (i+n*row)=1 then ys++[i] else ys).length ∧
      T.scalar 7=IndexedRefinement.read (if IndexedRefinement.read xs (i+n*row)=1 then ys++[i] else ys) slot := by
  have hindex : i+n*row<n*n := by nlinarith
  have hnB : n≤B := by
    have hnpos : 0<n := by omega
    nlinarith
  have hm : n*row≤B := by nlinarith
  have h1 : 1≤B := by omega
  have valid : ValidAtoms B prepare S := by
    simp [prepare,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar,
      hn,hr,hi,ha,hlen,hindex,hm,show i+n*row≤B by omega]
    split_ifs <;>omega
  obtain ⟨first,hU⟩ := atoms_runs hS prepare valid
  let U := applyAtoms prepare S
  have us (j : Reg) (hj : j≠8 ∧ j≠9) : U.scalar j=S.scalar j := by
    simp [U,applyAtoms,prepare,Atom.apply,Store.setScalar,hj.1,hj.2]
  have uf : U.scalar 9=if IndexedRefinement.read xs (i+n*row)=1 then 1 else 0 := by
    simp [U,applyAtoms,prepare,Atom.apply,BinaryOp.eval,Store.setScalar,hn,hr,hi,ha,hone,IndexedRefinement.read]
  by_cases he : IndexedRefinement.read xs (i+n*row)=1
  · obtain ⟨t,ht,T,last,hT,hcount,hpicked⟩ := active_runs U B ys.length slot i (IndexedRefinement.read ys slot) hU
      ((us _ (by decide)).trans hc) ((us _ (by decide)).trans hs) ((us _ (by decide)).trans hi)
      ((us _ (by decide)).trans hp) ((us _ (by decide)).trans hone) (by omega)
    refine ⟨4+(t+1),by omega,T,Runs.seq first (Runs.branch_nonzero (by change U.scalar 9≠0;simp [uf,he]) last),hT,?_,?_⟩
    · simpa [he] using hcount
    · simpa [he,read_append_singleton,eq_comm] using hpicked
  · refine ⟨5,by omega,U,Runs.seq first (Runs.branch_zero (by change U.scalar 9=0;simp [uf,he])
      (Runs.skip (Store.size_le_of_bounded hU))),hU,?_,?_⟩
    · simpa [he] using (us 6 (by decide)).trans hc
    · simpa [he] using (us 7 (by decide)).trans hp

private structure Invariant (xs : List ℕ) (n row slot B i : ℕ) (S : Store Reg Arr) : Prop where
  bounded : S.Bounded B
  n_eq : S.scalar 0=n
  row_eq : S.scalar 1=row
  slot_eq : S.scalar 2=slot
  index_eq : S.scalar 3=i
  todo_eq : S.scalar 4=n-i
  one_eq : S.scalar 5=1
  count_eq : S.scalar 6=(neighbors xs n row i).length
  picked_eq : S.scalar 7=IndexedRefinement.read (neighbors xs n row i) slot
  array_eq : S.array ()=xs

def scanLoop : Code := countedLoop 3 4 0 5 body

theorem scanLoop_runs (xs : List ℕ) (n row slot B : ℕ) (S : Store Reg Arr)
    (hS : S.Bounded B) (hn : S.scalar 0=n) (hr : S.scalar 1=row) (hs : S.scalar 2=slot)
    (hone : S.scalar 5=1) (hc : S.scalar 6=0) (hp : S.scalar 7=0) (ha : S.array ()=xs)
    (hlen : xs.length=n*n) (hrow : row<n) (hroom : n*n≤B) :
    ∃ t≤12*n+3,∃ T,Runs (storageBound Reg Arr B) scanLoop S t T ∧ T.Bounded B ∧
      T.scalar 6=(neighbors xs n row n).length ∧ T.scalar 7=IndexedRefinement.read (neighbors xs n row n) slot := by
  have hnB : n≤B := by simpa [hn] using hS.1 0
  let I := Invariant xs n row slot B
  have hcopy := hS.setScalar 4 (hS.1 0)
  have start : I 0 ((S.setScalar 4 (S.scalar 0)).setScalar 3 0) := by
    refine ⟨hcopy.setScalar _ (Nat.zero_le _),?_,?_,?_,?_,?_,?_,?_,?_,ha⟩
    all_goals simp [hn,hr,hs,hone,hc,hp,neighbors,IndexedRefinement.read]
  have control : ∀ i≤n,∀ U,I i U → U.scalar 3=i ∧ U.scalar 4=n-i ∧ U.scalar 5=1 ∧ U.size≤storageBound Reg Arr B := by
    intro i hi U hU
    exact ⟨hU.index_eq,hU.todo_eq,hU.one_eq,Store.size_le_of_bounded hU.bounded⟩
  have step : ∀ i<n,∀ U,I i U → ∃ t≤9,∃ V,Runs (storageBound Reg Arr B) body U t V ∧
      V.scalar 3=i ∧ V.scalar 4=n-i ∧ V.scalar 5=1 ∧ (V.setScalar 3 (i+1)).size≤storageBound Reg Arr B ∧
      I (i+1) (advance 3 4 V) := by
    intro i hi U hU
    have hy : (neighbors xs n row i).length≤ i := by simpa [neighbors] using List.length_filter_le (fun j=>IndexedRefinement.read xs (j+n*row)==1) (List.range i)
    obtain ⟨t,ht,V,run,hV,hcount,hpicked⟩ := body_runs xs (neighbors xs n row i) n row slot i B U hU.bounded
      hU.n_eq hU.row_eq hU.slot_eq hU.index_eq hU.one_eq hU.count_eq hU.picked_eq hU.array_eq hlen hrow hi hy hroom
    have frames (j : Reg) (hj : j.val<6) : V.scalar j=U.scalar j := by
      apply run.scalar_eq_of_not_mem
      simp [body,active,atoms,prepare,NatArrayLanguage.sequence,Program.scalarWrites,Atom.scalarWrites]
      repeat' constructor
      all_goals apply Fin.ne_of_val_ne;omega
    have arrays : V.array ()=U.array () := run.array_eq_of_not_mem () (by
      simp [body,active,atoms,prepare,NatArrayLanguage.sequence,Program.arrayWrites,Atom.arrayWrites])
    have hvi := (frames 3 (by decide)).trans hU.index_eq
    have hvt := (frames 4 (by decide)).trans hU.todo_eq
    have hvo := (frames 5 (by decide)).trans hU.one_eq
    have mid := hV.setScalar 3 (show i+1≤B by omega)
    refine ⟨t,ht,V,run,hvi,hvt,hvo,Store.size_le_of_bounded mid,?_⟩
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [advance,hvi] using mid.setScalar 4 (show V.scalar 4-1≤B by rw [hvt];omega)
    · simpa [advance] using (frames 0 (by decide)).trans hU.n_eq
    · simpa [advance] using (frames 1 (by decide)).trans hU.row_eq
    · simpa [advance] using (frames 2 (by decide)).trans hU.slot_eq
    · simp [advance,hvi]
    · simp [advance,hvt];omega
    · simpa [advance] using hvo
    · simpa [advance,neighbors_succ] using hcount
    · simpa [advance,neighbors_succ] using hpicked
    · simpa [advance,arrays] using hU.array_eq
  obtain ⟨t,ht,T,run,hT⟩ := countedLoop_runs (storageBound Reg Arr B) 3 4 0 5 body n 9 I S
    (Store.size_le_of_bounded hS) (Store.size_le_of_bounded hcopy) start control (by decide) (by decide) step
  exact ⟨t,by omega,T,run,hT.bounded,hT.count_eq,hT.picked_eq⟩

def prelude : List (Atom Reg Arr) := [.const 5 1,.const 6 0,.const 7 0]
def scan : Code := .seq (atoms prelude) scanLoop

theorem scan_runs (xs : List ℕ) (n row slot B : ℕ) (S : Store Reg Arr)
    (hS : S.Bounded B) (hn : S.scalar 0=n) (hr : S.scalar 1=row) (hs : S.scalar 2=slot)
    (ha : S.array ()=xs) (hlen : xs.length=n*n) (hrow : row<n) (hroom : n*n≤B) :
    ∃ t≤12*n+6,∃ T,Runs (storageBound Reg Arr B) scan S t T ∧ T.Bounded B ∧
      T.scalar 6=(neighbors xs n row n).length ∧ T.scalar 7=IndexedRefinement.read (neighbors xs n row n) slot := by
  have h1 : 1≤B := by
    have hnpos : 0<n := by omega
    nlinarith
  have valid : ValidAtoms B prelude S := by simp [prelude,ValidAtoms,Atom.Valid,Atom.SmallResult,h1]
  obtain ⟨first,hU⟩ := atoms_runs hS prelude valid
  let U := applyAtoms prelude S
  obtain ⟨t,ht,T,last,hT,hc,hp⟩ := scanLoop_runs xs n row slot B U hU
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar,hn])
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar,hr])
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar,hs])
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar])
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar])
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar]) ha hlen hrow hroom
  exact ⟨3+t,by omega,T,Runs.seq first last,hT,hc,hp⟩
end GroupWL.MachinePrograms.NeighborScan
