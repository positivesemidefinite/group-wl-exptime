import GroupWL.IndexedRefinement
import GroupWL.MachinePrograms.NatArrayComponents
import GroupWL.MachinePrograms.NatArrayCountedLoops
import GroupWL.MachinePrograms.NatArrayFrames
import GroupWL.FiniteWordTypes

/-! Check the two kernels of a materialized paired-subgroup mask. -/
namespace GroupWL.MachinePrograms.PairedKernelScan
open NatArrayLanguage
abbrev Reg := Fin 14
abbrev Arr := Unit
abbrev Code := Program Reg Arr
set_option maxRecDepth 4096

def testAt (xs : List ℕ) (m l r i : ℕ) : Bool :=
  if IndexedRefinement.read xs i=1 then decide (i/m=l ↔ i%m=r) else true

def prefixTest (xs : List ℕ) (m l r i : ℕ) : ℕ :=
  IndexedRefinement.boolNat ((List.range i).all (testAt xs m l r))

theorem prefix_le (xs : List ℕ) (m l r i : ℕ) : prefixTest xs m l r i≤1 :=
  IndexedRefinement.boolNat_le_one _

theorem prefix_succ (xs : List ℕ) (m l r i : ℕ) :
    prefixTest xs m l r (i+1)=prefixTest xs m l r i*IndexedRefinement.boolNat (testAt xs m l r i) := by
  simp only [prefixTest,List.range_succ,List.all_append,List.all_cons,List.all_nil,Bool.and_true]
  cases (List.range i).all (testAt xs m l r) <;> cases testAt xs m l r i <;> rfl

def checkAtoms : List (Atom Reg Arr) := [
  .divmod 9 10 4 1,.binary .eq 11 9 2,.binary .eq 12 10 3,
  .binary .eq 13 11 12,.binary .mul 7 7 13]
def readAtoms : List (Atom Reg Arr) := [.read 8 () 4,.binary .eq 8 8 6]
def body : Code := .seq (atoms readAtoms) (.branch 8 (atoms checkAtoms) .skip)

theorem check_runs (S : Store Reg Arr) (B m l r i z : ℕ) (hS : S.Bounded B)
    (hm : S.scalar 1=m) (hl : S.scalar 2=l) (hr : S.scalar 3=r)
    (hi : S.scalar 4=i) (hz : S.scalar 7=z) (hpos : 0<m) (hz1 : z≤1) (h1 : 1≤B) :
    ∃ T,Runs (storageBound Reg Arr B) (atoms checkAtoms) S 5 T ∧ T.Bounded B ∧
      T.scalar 7=z*IndexedRefinement.boolNat (decide (i/m=l ↔ i%m=r)) := by
  have hmul : z*(if (if i/m=l then 1 else 0)=(if i%m=r then 1 else 0) then 1 else 0)≤B := by
    split_ifs <;> omega
  have valid : ValidAtoms B checkAtoms S := by
    simp [checkAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,hm,hl,hr,hi,hz,hpos,h1,hmul]
    split_ifs <;> omega
  obtain ⟨run,hT⟩ := atoms_runs hS checkAtoms valid
  refine ⟨_,run,hT,?_⟩
  simp only [applyAtoms,checkAtoms,List.foldl_cons,List.foldl_nil,Atom.apply,BinaryOp.eval,
    Store.setScalar,Function.update_apply]
  simp [hm,hl,hr,hi,hz,IndexedRefinement.boolNat]
  split_ifs <;> simp_all

theorem body_runs (S : Store Reg Arr) (B m l r i z : ℕ) (xs : List ℕ) (hS : S.Bounded B)
    (hm : S.scalar 1=m) (hl : S.scalar 2=l) (hr : S.scalar 3=r) (hi : S.scalar 4=i)
    (hone : S.scalar 6=1) (hz : S.scalar 7=z) (ha : S.array ()=xs)
    (hil : i<xs.length) (hpos : 0<m) (hz1 : z≤1) (h1 : 1≤B) :
    ∃ t≤8,∃ T,Runs (storageBound Reg Arr B) body S t T ∧ T.Bounded B ∧
      T.scalar 7=z*IndexedRefinement.boolNat (testAt xs m l r i) := by
  have valid : ValidAtoms B readAtoms S := by
    simp [readAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,hi,ha,hil,h1]
    split_ifs <;> omega
  obtain ⟨init,hU⟩ := atoms_runs hS readAtoms valid
  let U := applyAtoms readAtoms S
  have us (j : Reg) (hj : j≠8) : U.scalar j=S.scalar j := by
    simp [U,applyAtoms,readAtoms,Atom.apply,Store.setScalar,hj]
  have uf : U.scalar 8=if IndexedRefinement.read xs i=1 then 1 else 0 := by
    simp [U,applyAtoms,readAtoms,Atom.apply,Store.setScalar,BinaryOp.eval,ha,hi,hone,IndexedRefinement.read]
  by_cases hmask : IndexedRefinement.read xs i=1
  · obtain ⟨T,last,hT,hresult⟩ := check_runs U B m l r i z hU
      ((us _ (by decide)).trans hm) ((us _ (by decide)).trans hl)
      ((us _ (by decide)).trans hr) ((us _ (by decide)).trans hi)
      ((us _ (by decide)).trans hz) hpos hz1 h1
    refine ⟨8,le_rfl,T,Runs.seq init (Runs.branch_nonzero (by change U.scalar 8≠0; simp [uf,hmask]) last),hT,?_⟩
    simpa [testAt,hmask] using hresult
  · refine ⟨3,by omega,U,Runs.seq init (Runs.branch_zero (by change U.scalar 8=0; simp [uf,hmask])
      (Runs.skip (Store.size_le_of_bounded hU))),hU,?_⟩
    simp [testAt,hmask,IndexedRefinement.boolNat,us 7 (by decide),hz]

private structure Invariant (xs : List ℕ) (m l r B i : ℕ) (S : Store Reg Arr) : Prop where
  bounded : S.Bounded B
  right_eq : S.scalar 1=m
  leftOne_eq : S.scalar 2=l
  rightOne_eq : S.scalar 3=r
  index_eq : S.scalar 4=i
  todo_eq : S.scalar 5=xs.length-i
  one_eq : S.scalar 6=1
  result_eq : S.scalar 7=prefixTest xs m l r i
  mask_eq : S.array ()=xs

def scanLoop : Code := countedLoop 4 5 0 6 body

theorem scanLoop_runs (S : Store Reg Arr) (B m l r : ℕ) (xs : List ℕ) (hS : S.Bounded B)
    (hn : S.scalar 0=xs.length) (hm : S.scalar 1=m) (hl : S.scalar 2=l) (hr : S.scalar 3=r)
    (hone : S.scalar 6=1) (hz : S.scalar 7=1) (ha : S.array ()=xs) (hpos : 0<m) (h1 : 1≤B) :
    ∃ t≤11*xs.length+3,∃ T,Runs (storageBound Reg Arr B) scanLoop S t T ∧ T.Bounded B ∧
      T.scalar 7=prefixTest xs m l r xs.length := by
  have hlen : xs.length≤B := by simpa [ha] using hS.2.1 ()
  let I := Invariant xs m l r B
  have hcopy := hS.setScalar 5 (hS.1 0)
  have start : I 0 ((S.setScalar 5 (S.scalar 0)).setScalar 4 0) := by
    refine ⟨hcopy.setScalar _ (Nat.zero_le _),?_,?_,?_,?_,?_,?_,?_,ha⟩
    all_goals simp [hm,hl,hr,hn,hone,hz,prefixTest,IndexedRefinement.boolNat]
  have control : ∀ i≤xs.length,∀ U,I i U → U.scalar 4=i ∧ U.scalar 5=xs.length-i ∧
      U.scalar 6=1 ∧ U.size≤storageBound Reg Arr B := by
    intro i hi U hU
    exact ⟨hU.index_eq,hU.todo_eq,hU.one_eq,Store.size_le_of_bounded hU.bounded⟩
  have step : ∀ i<xs.length,∀ U,I i U → ∃ t≤8,∃ V,Runs (storageBound Reg Arr B) body U t V ∧
      V.scalar 4=i ∧ V.scalar 5=xs.length-i ∧ V.scalar 6=1 ∧
      (V.setScalar 4 (i+1)).size≤storageBound Reg Arr B ∧ I (i+1) (advance 4 5 V) := by
    intro i hi U hU
    obtain ⟨t,ht,V,run,hV,hresult⟩ := body_runs U B m l r i (prefixTest xs m l r i) xs hU.bounded
      hU.right_eq hU.leftOne_eq hU.rightOne_eq hU.index_eq hU.one_eq hU.result_eq hU.mask_eq
      hi hpos (prefix_le ..) h1
    have frames (j : Reg) (hj : j.val<7) : V.scalar j=U.scalar j := by
      apply run.scalar_eq_of_not_mem
      simp [body,atoms,readAtoms,checkAtoms,NatArrayLanguage.sequence,Program.scalarWrites,Atom.scalarWrites]
      repeat' constructor
      all_goals apply Fin.ne_of_val_ne; omega
    have arrays : V.array ()=U.array () := run.array_eq_of_not_mem () (by
      simp [body,atoms,readAtoms,checkAtoms,NatArrayLanguage.sequence,Program.arrayWrites,Atom.arrayWrites])
    have hvi := (frames 4 (by decide)).trans hU.index_eq
    have hvt := (frames 5 (by decide)).trans hU.todo_eq
    have hvo := (frames 6 (by decide)).trans hU.one_eq
    have mid := hV.setScalar 4 (show i+1≤B by omega)
    refine ⟨t,ht,V,run,hvi,hvt,hvo,Store.size_le_of_bounded mid,?_⟩
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [advance,hvi] using mid.setScalar 5 (show V.scalar 5-1≤B by rw [hvt];omega)
    · simpa [advance] using (frames 1 (by decide)).trans hU.right_eq
    · simpa [advance] using (frames 2 (by decide)).trans hU.leftOne_eq
    · simpa [advance] using (frames 3 (by decide)).trans hU.rightOne_eq
    · simp [advance,hvi]
    · simp [advance,hvt]; omega
    · simpa [advance] using hvo
    · simpa [advance,prefix_succ] using hresult
    · simpa [advance,arrays] using hU.mask_eq
  obtain ⟨t,ht,T,run,hT⟩ := countedLoop_runs (storageBound Reg Arr B) 4 5 0 6 body xs.length 8 I S
    (Store.size_le_of_bounded hS) (Store.size_le_of_bounded hcopy) start control
    (by decide) (by decide) step
  exact ⟨t,by omega,T,run,hT.bounded,hT.result_eq⟩

def prelude : List (Atom Reg Arr) := [.const 6 1,.const 7 1]
def scan : Code := .seq (atoms prelude) scanLoop

theorem scan_runs (S : Store Reg Arr) (B m l r : ℕ) (xs : List ℕ) (hS : S.Bounded B)
    (hn : S.scalar 0=xs.length) (hm : S.scalar 1=m) (hl : S.scalar 2=l) (hr : S.scalar 3=r)
    (ha : S.array ()=xs) (hpos : 0<m) (h1 : 1≤B) :
    ∃ t≤11*xs.length+5,∃ T,Runs (storageBound Reg Arr B) scan S t T ∧ T.Bounded B ∧
      T.scalar 7≤1 ∧ (T.scalar 7=1 ↔ ∀ i<xs.length,IndexedRefinement.read xs i=1 → (i/m=l ↔ i%m=r)) := by
  have valid : ValidAtoms B prelude S := by simp [prelude,ValidAtoms,Atom.Valid,Atom.SmallResult,h1]
  obtain ⟨init,hU⟩ := atoms_runs hS prelude valid
  let U := applyAtoms prelude S
  obtain ⟨t,ht,T,run,hT,hresult⟩ := scanLoop_runs U B m l r xs hU
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar,hn])
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar,hm])
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar,hl])
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar,hr])
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar])
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar]) ha hpos h1
  refine ⟨2+t,by omega,T,Runs.seq init run,hT,by rw [hresult]; exact prefix_le ..,?_⟩
  rw [hresult]
  simp [prefixTest,IndexedRefinement.boolNat_eq_one,List.all_eq_true,testAt]
  constructor
  · intro h i hi hm
    exact (h i hi).resolve_left (not_not.mpr hm)
  · intro h i hi
    by_cases hm : IndexedRefinement.read xs i=1
    · exact Or.inr (h i hi hm)
    · exact Or.inl hm


section Semantics
variable {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
  [DecidableEq G] [DecidableEq H] {n m k : ℕ}

def pairEnumeration (e : G ≃ Fin n) (e' : H ≃ Fin m) : Fin (n*m) ≃ G×H :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr e.symm e'.symm)

theorem pair_kernel_iff (e : G ≃ Fin n) (e' : H ≃ Fin m) (j : Fin (n*m)) :
    (j.val/m=(e 1).val ↔ j.val%m=(e' 1).val) ↔
      ((pairEnumeration e e' j).1=1 ↔ (pairEnumeration e e' j).2=1) := by
  have hl : (e (pairEnumeration e e' j).1).val=j.val/m := by
    simp [pairEnumeration]
  have hr : (e' (pairEnumeration e e' j).2).val=j.val%m := by
    simp [pairEnumeration]
  have left : j.val/m=(e 1).val ↔ (pairEnumeration e e' j).1=1 := by
    constructor
    · intro h;apply e.injective;apply Fin.ext;exact hl.trans h
    · intro h;rw [h] at hl;exact hl.symm
  have right : j.val%m=(e' 1).val ↔ (pairEnumeration e e' j).2=1 := by
    constructor
    · intro h;apply e'.injective;apply Fin.ext;exact hr.trans h
    · intro h;rw [h] at hr;exact hr.symm
  exact iff_congr left right

theorem scan_paired_runs (e : G ≃ Fin n) (e' : H ≃ Fin m) (a : Fin k → G) (b : Fin k → H)
    (S : Store Reg Arr) (B : ℕ) (hS : S.Bounded B)
    (hn : S.scalar 0=n*m) (hm : S.scalar 1=m)
    (hl : S.scalar 2=(e 1).val) (hr : S.scalar 3=(e' 1).val)
    (hlen : (S.array ()).length=n*m)
    (hmask : ∀ j : Fin (n*m),IndexedRefinement.read (S.array ()) j.val=1 ↔
      pairEnumeration e e' j∈FiniteWordTypes.explore a b (Fintype.card (G×H))) :
    ∃ t≤11*(n*m)+5,∃ T,Runs (storageBound Reg Arr B) scan S t T ∧ T.Bounded B ∧
      T.scalar 7≤1 ∧ (T.scalar 7=1 ↔ FiniteWordTypes.sameWordType a b=true) := by
  have hmpos : 0<m := by have := (e' 1).isLt;omega
  have hnpos : 0<n := by have := (e 1).isLt;omega
  have h1 : 1≤B := by have := hS.1 0;rw [hn] at this;have := Nat.mul_pos hnpos hmpos;omega
  obtain ⟨t,ht,T,run,hT,hflag,heq⟩ := scan_runs S B m (e 1).val (e' 1).val (S.array ()) hS
    (hn.trans hlen.symm) hm hl hr rfl hmpos h1
  refine ⟨t,by simpa [hlen] using ht,T,run,hT,hflag,heq.trans ?_⟩
  simp only [FiniteWordTypes.sameWordType,decide_eq_true_eq]
  constructor
  · intro h x hx
    obtain ⟨j,rfl⟩ := (pairEnumeration e e').surjective x
    exact (pair_kernel_iff e e' j).mp (h j.val (by simpa [hlen] using j.isLt) ((hmask j).mpr hx))
  · intro h i hi hread
    let j : Fin (n*m) := ⟨i,by simpa [hlen] using hi⟩
    exact (pair_kernel_iff e e' j).mpr (h _ ((hmask j).mp hread))
end Semantics
end GroupWL.MachinePrograms.PairedKernelScan
