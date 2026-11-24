import GroupWL.IndexedNeighbors
import GroupWL.MachinePrograms.NatArrayComponents

/-! Materialize both neighbor multiplicities and padded neighbor targets. -/
namespace GroupWL.MachinePrograms.NeighborArrays
open NatArrayLanguage
abbrev Reg := NeighborScan.Reg ⊕ Fin 5
abbrev Arr := Unit ⊕ Fin 2
abbrev Code := Program Reg Arr
set_option maxRecDepth 4096

def pointPrepare (targets : Bool) : List (Atom Reg Arr) :=
  if targets then [.divmod (.inl 1) (.inl 2) (.inr 0) (.inl 0)]
  else [.copy (.inl 1) (.inr 0),.const (.inl 2) 0]
def point (targets : Bool) : Code := .seq (atoms (pointPrepare targets)) (NeighborScan.scan.map Sum.inl Sum.inl)
def fill (targets : Bool) : Code := ArrayTabulate.tabulate (.inr 0) (.inr 1) (.inr 2) (.inr 3) (.inr 4)
  (.inl (if targets then 7 else 6)) (.inr (if targets then 1 else 0)) (point targets)

structure Context {n : ℕ} (adj : Fin n → Fin n → Bool) (S : Store Reg Arr) : Prop where
  order_eq : S.scalar (.inl 0)=n
  table_eq : S.array (.inl ())=GraphInitial.tableWord adj

theorem point_runs {n : ℕ} (adj : Fin n → Fin n → Bool) (targets : Bool) (a x : Fin n)
    (hx : targets=false → x.val=0) (S : Store Reg Arr) (B : ℕ) (hS : S.Bounded B)
    (hP : Context adj S) (hi : S.scalar (.inr 0)=if targets then (finProdFinEquiv (a,x)).val else a.val)
    (hroom : n*n≤B) :
    ∃ t≤12*n+8,∃ T,Runs (storageBound Reg Arr B) (point targets) S t T ∧ T.Bounded B ∧ Context adj T ∧
      (∀ j : Fin 5,T.scalar (.inr j)=S.scalar (.inr j)) ∧
      (∀ j : Fin 2,T.array (.inr j)=S.array (.inr j)) ∧
      T.scalar (.inl 6)=(IndexedNeighbors.rowList adj a).length ∧
      T.scalar (.inl 7)=IndexedRefinement.read ((IndexedNeighbors.rowList adj a).map Fin.val) x.val := by
  have hnpos : 0<n := by have := a.isLt;omega
  have valid : ValidAtoms B (pointPrepare targets) S := by
    cases targets <;> simp [pointPrepare,ValidAtoms,Atom.Valid,Atom.SmallResult,hP.order_eq,hnpos]
  obtain ⟨first,hU⟩ := atoms_runs hS (pointPrepare targets) valid
  let U := applyAtoms (pointPrepare targets) S
  have un : U.left.scalar 0=n := by cases targets <;> simp [U,applyAtoms,pointPrepare,Atom.apply,Store.left,Store.setScalar,hP.order_eq]
  have ua : U.left.scalar 1=a.val := by
    cases targets with
    | false => simpa [U,applyAtoms,pointPrepare,Atom.apply,Store.left,Store.setScalar] using hi
    | true =>
      simp only [if_true] at hi
      simp [U,applyAtoms,pointPrepare,Atom.apply,Store.left,Store.setScalar,hP.order_eq,hi,
        finProdFinEquiv,Nat.add_mul_div_left,Nat.div_eq_of_lt x.isLt,hnpos]
  have ux : U.left.scalar 2=x.val := by
    cases targets with
    | false => simp [U,applyAtoms,pointPrepare,Atom.apply,Store.left,Store.setScalar,hx rfl]
    | true =>
      simp only [if_true] at hi
      simp [U,applyAtoms,pointPrepare,Atom.apply,Store.left,Store.setScalar,hP.order_eq,hi,
        finProdFinEquiv,Nat.mod_eq_of_lt x.isLt]
  have uaTable : U.left.array ()=GraphInitial.tableWord adj := by
    cases targets <;> simpa [U,applyAtoms,pointPrepare,Atom.apply,Store.left] using hP.table_eq
  obtain ⟨t,ht,V,last,hV,hcount,hpicked⟩ := NeighborScan.scan_runs (GraphInitial.tableWord adj) n a.val x.val B U.left
    hU.left un ua ux uaTable (GraphInitial.tableWord_length adj) a.isLt hroom
  let T := V.join U.right
  have lifted := last.left_bounded hU
  have vn : V.scalar 0=U.left.scalar 0 := last.scalar_eq_of_not_mem 0 (by
    simp [NeighborScan.scan,NeighborScan.prelude,NeighborScan.scanLoop,NeighborScan.body,NeighborScan.active,
      NeighborScan.prepare,countedLoop,atoms,NatArrayLanguage.sequence,Program.scalarWrites,Atom.scalarWrites])
  have va : V.array ()=U.left.array () := last.array_eq_of_not_mem () (by
    simp [NeighborScan.scan,NeighborScan.prelude,NeighborScan.scanLoop,NeighborScan.body,NeighborScan.active,
      NeighborScan.prepare,countedLoop,atoms,NatArrayLanguage.sequence,Program.arrayWrites,Atom.arrayWrites])
  refine ⟨(pointPrepare targets).length+t,?_,T,Runs.seq first lifted,hV.join hU.right,
    ⟨vn.trans un,va.trans uaTable⟩,?_,?_,?_,?_⟩
  · cases targets <;> simp [pointPrepare] <;>omega
  · intro j;cases targets <;> simp [T,U,applyAtoms,pointPrepare,Atom.apply,Store.right,Store.setScalar]
  · intro j;cases targets <;>rfl
  · simpa [T,IndexedNeighbors.scan_neighbors] using hcount
  · simpa [T,IndexedNeighbors.scan_neighbors] using hpicked

theorem fanouts_runs {n : ℕ} (adj : Fin n → Fin n → Bool) (hnpos : 0<n)
    (S : Store Reg Arr) (B : ℕ) (hS : S.Bounded B) (hP : Context adj S)
    (hlimit : S.scalar (.inr 2)=n) (hone : S.scalar (.inr 3)=1) (hzero : S.scalar (.inr 4)=0)
    (hroom : n*n≤B) :
    ∃ t≤n*(12*n+12)+4,∃ T,Runs (storageBound Reg Arr B) (fill false) S t T ∧ T.Bounded B ∧
      Context adj T ∧ T.array (.inr 0)=(IndexedNeighbors.data hnpos adj).fanoutWord := by
  apply ArrayTabulate.tabulate_runs (.inr 0) (.inr 1) (.inr 2) (.inr 3) (.inr 4) (.inl 6) (.inr 0) (point false)
    (fun a => (IndexedNeighbors.rowList adj a).length) (Context adj) B (12*n+8)
  · intro U v hU;exact ⟨by simpa using hU.order_eq,hU.table_eq⟩
  · intro U v hU;exact ⟨by simpa using hU.order_eq,hU.table_eq⟩
  · intro U xs hU;exact ⟨hU.order_eq,by simpa using hU.table_eq⟩
  · decide
  · decide
  · decide
  · intro i U hp hb hi htodo hone
    obtain ⟨t,ht,V,run,hV,hPV,frames,arrays,hcount,_⟩ := point_runs adj false i ⟨0,hnpos⟩ (by simp)
      U B hb hp hi hroom
    exact ⟨t,ht,V,run,hV,hPV,(frames 0).trans hi,(frames 1).trans htodo,(frames 3).trans hone,hcount,arrays 0⟩
  · exact hS
  · exact hP
  · exact hlimit
  · exact hone
  · exact hzero

def targetWord {n : ℕ} (adj : Fin n → Fin n → Bool) : List ℕ :=
  List.ofFn (fun i : Fin (n*n) => IndexedRefinement.read
    ((IndexedNeighbors.rowList adj (finProdFinEquiv.symm i).1).map Fin.val) (finProdFinEquiv.symm i).2.val)

theorem targetWord_eq {n : ℕ} (adj : Fin n → Fin n → Bool) (hnpos : 0<n) :
    targetWord adj=(IndexedNeighbors.data hnpos adj).targetWord := by
  apply List.ext_getElem
  · simp [targetWord]
  · intro j hj hj'
    have hjn : j<n*n := by simpa [targetWord] using hj
    let ax := finProdFinEquiv.symm (⟨j,hjn⟩ : Fin (n*n))
    have haddress : ax.2.val+n*ax.1.val=j := congrArg Fin.val (Equiv.apply_symm_apply finProdFinEquiv ⟨j,hjn⟩)
    have he := IndexedRefinement.Data.targetWord_read (IndexedNeighbors.data hnpos adj) ax.1 ax.2 0
    simp only [Fin.val_zero,Nat.mul_one,Nat.zero_add,Nat.one_mul] at he
    rw [haddress,IndexedNeighbors.data_target,IndexedNeighbors.scan_neighbors] at he
    simpa only [IndexedRefinement.read,List.getElem?_eq_getElem hj',Option.getD_some,targetWord,List.getElem_ofFn,ax] using he.symm

theorem targets_runs {n : ℕ} (adj : Fin n → Fin n → Bool) (hnpos : 0<n)
    (S : Store Reg Arr) (B : ℕ) (hS : S.Bounded B) (hP : Context adj S)
    (hlimit : S.scalar (.inr 2)=n*n) (hone : S.scalar (.inr 3)=1) (hzero : S.scalar (.inr 4)=0)
    (hroom : n*n≤B) :
    ∃ t≤(n*n)*(12*n+12)+4,∃ T,Runs (storageBound Reg Arr B) (fill true) S t T ∧ T.Bounded B ∧
      Context adj T ∧ T.array (.inr 1)=(IndexedNeighbors.data hnpos adj).targetWord := by
  rw [←targetWord_eq]
  apply ArrayTabulate.tabulate_runs (.inr 0) (.inr 1) (.inr 2) (.inr 3) (.inr 4) (.inl 7) (.inr 1) (point true)
    (fun i => IndexedRefinement.read ((IndexedNeighbors.rowList adj (finProdFinEquiv.symm i).1).map Fin.val) (finProdFinEquiv.symm i).2.val)
    (Context adj) B (12*n+8)
  · intro U v hU;exact ⟨by simpa using hU.order_eq,hU.table_eq⟩
  · intro U v hU;exact ⟨by simpa using hU.order_eq,hU.table_eq⟩
  · intro U xs hU;exact ⟨hU.order_eq,by simpa using hU.table_eq⟩
  · decide
  · decide
  · decide
  · intro i U hp hb hi htodo hone
    let ax := finProdFinEquiv.symm i
    obtain ⟨t,ht,V,run,hV,hPV,frames,arrays,_,hpicked⟩ := point_runs adj true ax.1 ax.2 (by simp)
      U B hb hp (by change U.scalar (.inr 0)=i.val%n+n*(i.val/n);exact hi.trans (Nat.mod_add_div i.val n).symm) hroom
    exact ⟨t,ht,V,run,hV,hPV,(frames 0).trans hi,(frames 1).trans htodo,(frames 3).trans hone,hpicked,arrays 1⟩
  · exact hS
  · exact hP
  · exact hlimit
  · exact hone
  · exact hzero

def prelude : List (Atom Reg Arr) := [.copy (.inr 2) (.inl 0),.const (.inr 3) 1,.const (.inr 4) 0]
def generate : Code := .seq (atoms prelude) (.seq (fill false)
  (.seq (.atom (.binary .mul (.inr 2) (.inl 0) (.inl 0))) (fill true)))

theorem generate_runs {n : ℕ} (adj : Fin n → Fin n → Bool) (hnpos : 0<n)
    (S : Store Reg Arr) (B : ℕ) (hS : S.Bounded B) (hP : Context adj S) (hroom : n*n≤B) :
    ∃ t≤50*(n+1)^3,∃ T,Runs (storageBound Reg Arr B) generate S t T ∧ T.Bounded B ∧ Context adj T ∧
      T.array (.inr 0)=(IndexedNeighbors.data hnpos adj).fanoutWord ∧
      T.array (.inr 1)=(IndexedNeighbors.data hnpos adj).targetWord := by
  have h1 : 1≤B := by nlinarith
  have valid : ValidAtoms B prelude S := by simp [prelude,ValidAtoms,Atom.Valid,Atom.SmallResult,h1]
  obtain ⟨init,hU⟩ := atoms_runs hS prelude valid
  let U := applyAtoms prelude S
  have hPU : Context adj U := ⟨by simpa [U,applyAtoms,prelude,Atom.apply,Store.setScalar] using hP.order_eq,hP.table_eq⟩
  obtain ⟨t,ht,V,first,hV,hPV,hfanout⟩ := fanouts_runs adj hnpos U B hU hPU
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar,hP.order_eq])
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar])
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar]) hroom
  have middle := atom_runs hV (.binary .mul (.inr 2) (.inl 0) (.inl 0)) trivial
    (by simpa [Atom.SmallResult,BinaryOp.eval,hPV.order_eq] using hroom)
  let W := (Atom.binary .mul (.inr 2) (.inl 0) (.inl 0)).apply V
  have hW : W.Bounded B := Atom.apply_bounded hV _ (by simpa [Atom.SmallResult,BinaryOp.eval,hPV.order_eq] using hroom)
  have hPW : Context adj W := ⟨by simpa [W,Atom.apply,Store.setScalar] using hPV.order_eq,hPV.table_eq⟩
  have frames (j : Fin 5) (hj : j=3 ∨ j=4) : V.scalar (.inr j)=U.scalar (.inr j) := by
    apply first.scalar_eq_of_not_mem
    rcases hj with rfl|rfl <;> decide
  obtain ⟨u,hu,T,last,hT,hPT,htarget⟩ := targets_runs adj hnpos W B hW hPW
    (by simp [W,Atom.apply,BinaryOp.eval,Store.setScalar,hPV.order_eq])
    (by simp [W,Atom.apply,Store.setScalar,frames 3 (Or.inl rfl),U,applyAtoms,prelude])
    (by simp [W,Atom.apply,Store.setScalar,frames 4 (Or.inr rfl),U,applyAtoms,prelude]) hroom
  refine ⟨3+(t+(1+u)),by nlinarith,T,Runs.seq init (Runs.seq first (Runs.seq middle last)),hT,hPT,?_,htarget⟩
  rw [last.array_eq_of_not_mem (.inr 0) (by decide)]
  exact hfanout
end GroupWL.MachinePrograms.NeighborArrays
