import GroupWL.MachinePrograms.ProductGroupOperation
import GroupWL.MachinePrograms.GroupInitial
import GroupWL.MachinePrograms.NatArrayComponents

/-! Build the multiplication table of a direct product from its two tables. -/
namespace GroupWL.MachinePrograms.ProductGroupTable
open NatArrayLanguage
abbrev Reg := Fin 19
abbrev Arr := Fin 3
abbrev Code := Program Reg Arr
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

def bodyAtoms : List (Atom Reg Arr) := [
  .divmod 8 9 4 2,.divmod 10 11 8 1,.divmod 12 13 9 1,
  .binary .mul 14 0 10,.binary .add 14 14 12,.read 15 0 14,
  .binary .mul 14 1 11,.binary .add 14 14 13,.read 16 1 14,
  .binary .mul 17 1 15,.binary .add 17 17 16,.write 2 4 17]
def body : Code := atoms bodyAtoms

theorem body_runs {n m : ℕ} (f : Fin n → Fin n → Fin n) (g : Fin m → Fin m → Fin m)
    (a c : Fin n) (b d : Fin m) (S : Store Reg Arr) (B : ℕ) (hS : S.Bounded B)
    (hn : S.scalar 0=n) (hm : S.scalar 1=m) (hN : S.scalar 2=n*m)
    (hi : S.scalar 4=(finProdFinEquiv (finProdFinEquiv (a,b),finProdFinEquiv (c,d))).val)
    (ht : S.array 0=GroupInitial.tableWord f) (ht' : S.array 1=GroupInitial.tableWord g)
    (hlen : (S.array 2).length=(n*m)*(n*m)) (hnB : n*n≤B) (hmB : m*m≤B) (hNB : n*m≤B) :
    ∃ T,Runs (storageBound Reg Arr B) body S 12 T ∧ T.Bounded B ∧
      T.array 2=(S.array 2).set (S.scalar 4) (finProdFinEquiv (f a c,g b d)).val := by
  have hnpos : 0<n := by have := a.isLt;omega
  have hmpos : 0<m := by have := b.isLt;omega
  have hNpos : 0<n*m := Nat.mul_pos hnpos hmpos
  have hx := (finProdFinEquiv (a,b)).isLt
  have hy := (finProdFinEquiv (c,d)).isLt
  have hz := (finProdFinEquiv (finProdFinEquiv (a,b),finProdFinEquiv (c,d))).isLt
  have hc1 : n*a.val≤B := by have := (finProdFinEquiv (a,c)).isLt;dsimp at this;nlinarith
  have hc2 : n*a.val+c.val≤B := by have := (finProdFinEquiv (a,c)).isLt;dsimp at this;omega
  have hc3 : m*b.val≤B := by have := (finProdFinEquiv (b,d)).isLt;dsimp at this;nlinarith
  have hc4 : m*b.val+d.val≤B := by have := (finProdFinEquiv (b,d)).isLt;dsimp at this;omega
  have hc5 : m*(f a c).val≤B := by have := (finProdFinEquiv (f a c,g b d)).isLt;dsimp at this;nlinarith
  have hc6 : m*(f a c).val+(g b d).val≤B := by
    have := (finProdFinEquiv (f a c,g b d)).isLt;dsimp at this;omega
  have hax : (finProdFinEquiv (a,b)).val/m=a.val := by simp [finProdFinEquiv,Nat.add_mul_div_left,b.isLt,hmpos]
  have hbx : (finProdFinEquiv (a,b)).val%m=b.val := by
    change (b.val+m*a.val)%m=b.val
    rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt b.isLt]
  have hcy : (finProdFinEquiv (c,d)).val/m=c.val := by simp [finProdFinEquiv,Nat.add_mul_div_left,d.isLt,hmpos]
  have hdy : (finProdFinEquiv (c,d)).val%m=d.val := by
    change (d.val+m*c.val)%m=d.val
    rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt d.isLt]
  have hxz : S.scalar 4/(n*m)=(finProdFinEquiv (a,b)).val := by
    rw [hi];change ((finProdFinEquiv (c,d)).val+(n*m)*(finProdFinEquiv (a,b)).val)/(n*m)=_
    rw [Nat.add_mul_div_left _ _ hNpos,Nat.div_eq_of_lt hy,zero_add]
  have hyz : S.scalar 4%(n*m)=(finProdFinEquiv (c,d)).val := by
    rw [hi];change ((finProdFinEquiv (c,d)).val+(n*m)*(finProdFinEquiv (a,b)).val)%(n*m)=_
    rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hy]
  have readLeft : (S.array 0)[n*a.val+c.val]?.getD 0=(f a c).val := by
    simpa [ht,Nat.add_comm] using GroupInitial.tableWord_read f a c
  have readRight : (S.array 1)[m*b.val+d.val]?.getD 0=(g b d).val := by
    simpa [ht',Nat.add_comm] using GroupInitial.tableWord_read g b d
  have haidx := (finProdFinEquiv (a,c)).isLt
  have hbidx := (finProdFinEquiv (b,d)).isLt
  change c.val+n*a.val<n*n at haidx
  change d.val+m*b.val<m*m at hbidx
  have hl0 : (S.array 0).length=n*n := by simp [ht]
  have hl1 : (S.array 1).length=m*m := by simp [ht']
  have valid : ValidAtoms B bodyAtoms S := by
    simp +decide only [bodyAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,Function.update_apply,if_true,if_false,hn,hm,hN,hxz,hyz,hax,hbx,hcy,hdy,hl0,hl1,hlen,readLeft,readRight]
    repeat' constructor
    all_goals first | exact hNpos | exact hmpos | exact hc1 | exact hc2 | exact hc3 | exact hc4 | exact hc5 | exact hc6 | trivial | skip
    all_goals first | simpa only [hi] using hz | omega
  obtain ⟨run,hT⟩ := atoms_runs hS bodyAtoms valid
  refine ⟨_,run,hT,?_⟩
  simp +decide only [applyAtoms,bodyAtoms,List.foldl_cons,List.foldl_nil,Atom.apply,BinaryOp.eval,
    Store.setScalar,Function.update_apply,if_true,if_false,hn,hm,hN,hxz,hyz,hax,hbx,hcy,hdy,readLeft,readRight]
  change (S.setArray 2 ((S.array 2).set (S.scalar 4) (m*(f a c).val+(g b d).val))).array 2 = _
  simp [finProdFinEquiv,Nat.add_comm]

private structure Invariant {n m : ℕ} (f : Fin n → Fin n → Fin n) (g : Fin m → Fin m → Fin m)
    (B i : ℕ) (S : Store Reg Arr) : Prop where
  bounded : S.Bounded B
  left_eq : S.scalar 0=n
  right_eq : S.scalar 1=m
  order_eq : S.scalar 2=n*m
  index_eq : S.scalar 4=i
  todo_eq : S.scalar 5=(n*m)*(n*m)-i
  one_eq : S.scalar 6=1
  table_eq : S.array 0=GroupInitial.tableWord f
  table'_eq : S.array 1=GroupInitial.tableWord g
  length_eq : (S.array 2).length=(n*m)*(n*m)
  values_eq : ∀ j < i,IndexedRefinement.read (S.array 2) j=
    IndexedRefinement.read (GroupInitial.tableWord (productOp f g)) j

def fill : Code := countedLoop 4 5 3 6 body

theorem fill_runs {n m : ℕ} (f : Fin n → Fin n → Fin n) (g : Fin m → Fin m → Fin m)
    (S : Store Reg Arr) (B : ℕ) (hS : S.Bounded B)
    (hn : S.scalar 0=n) (hm : S.scalar 1=m) (hN : S.scalar 2=n*m)
    (htotal : S.scalar 3=(n*m)*(n*m)) (hone : S.scalar 6=1)
    (ht : S.array 0=GroupInitial.tableWord f) (ht' : S.array 1=GroupInitial.tableWord g)
    (hlen : (S.array 2).length=(n*m)*(n*m)) (hnB : n*n≤B) (hmB : m*m≤B) (hNB : n*m≤B) :
    ∃ t≤15*((n*m)*(n*m))+3,∃ T,Runs (storageBound Reg Arr B) fill S t T ∧ T.Bounded B ∧
      T.array 2=GroupInitial.tableWord (productOp f g) := by
  have hsize : (n*m)*(n*m)≤B := by simpa [hlen] using hS.2.1 2
  let I := Invariant f g B
  have hcopy := hS.setScalar 5 (hS.1 3)
  have start : I 0 ((S.setScalar 5 (S.scalar 3)).setScalar 4 0) := by
    refine ⟨hcopy.setScalar _ (Nat.zero_le _),?_,?_,?_,?_,?_,?_,ht,ht',hlen,?_⟩
    · simp [hn]
    · simp [hm]
    · simp [hN]
    · simp
    · simp [htotal]
    · simp [hone]
    · intro j hj;omega
  have control : ∀ i≤(n*m)*(n*m),∀ U,I i U → U.scalar 4=i ∧ U.scalar 5=(n*m)*(n*m)-i ∧
      U.scalar 6=1 ∧ U.size≤storageBound Reg Arr B := by
    intro i hi U hU
    exact ⟨hU.index_eq,hU.todo_eq,hU.one_eq,Store.size_le_of_bounded hU.bounded⟩
  have step : ∀ i<(n*m)*(n*m),∀ U,I i U → ∃ t≤12,∃ V,Runs (storageBound Reg Arr B) body U t V ∧
      V.scalar 4=i ∧ V.scalar 5=(n*m)*(n*m)-i ∧ V.scalar 6=1 ∧
      (V.setScalar 4 (i+1)).size≤storageBound Reg Arr B ∧ I (i+1) (advance 4 5 V) := by
    intro i hi U hU
    let z : Fin ((n*m)*(n*m)) := ⟨i,hi⟩
    let x : Fin (n*m) := (finProdFinEquiv.symm z).1
    let y : Fin (n*m) := (finProdFinEquiv.symm z).2
    let a : Fin n := (finProdFinEquiv.symm x).1
    let b : Fin m := (finProdFinEquiv.symm x).2
    let c : Fin n := (finProdFinEquiv.symm y).1
    let d : Fin m := (finProdFinEquiv.symm y).2
    have ex : finProdFinEquiv (a,b)=x := Equiv.apply_symm_apply _ x
    have ey : finProdFinEquiv (c,d)=y := Equiv.apply_symm_apply _ y
    have ez : finProdFinEquiv (x,y)=z := Equiv.apply_symm_apply _ z
    have hei : U.scalar 4=(finProdFinEquiv (finProdFinEquiv (a,b),finProdFinEquiv (c,d))).val := by
      rw [ex,ey,ez];exact hU.index_eq
    obtain ⟨V,run,hV,harray⟩ := body_runs f g a c b d U B hU.bounded hU.left_eq hU.right_eq hU.order_eq
      hei hU.table_eq hU.table'_eq hU.length_eq hnB hmB hNB
    have hvalue : (finProdFinEquiv (f a c,g b d)).val=
        IndexedRefinement.read (GroupInitial.tableWord (productOp f g)) i := by
      have hr := GroupInitial.tableWord_read (productOp f g) x y
      have hzval : y.val+(n*m)*x.val=i := congrArg Fin.val ez
      rw [hzval] at hr
      exact hr.symm
    have frames (j : Reg) (hj : j.val<8) : V.scalar j=U.scalar j := by
      apply run.scalar_eq_of_not_mem
      simp [body,atoms,bodyAtoms,NatArrayLanguage.sequence,Program.scalarWrites,Atom.scalarWrites]
      repeat' constructor
      all_goals apply Fin.ne_of_val_ne;omega
    have arrays (j : Arr) (hj : j≠2) : V.array j=U.array j := run.array_eq_of_not_mem j (by
      simp [body,atoms,bodyAtoms,NatArrayLanguage.sequence,Program.arrayWrites,Atom.arrayWrites,hj])
    have hvi := (frames 4 (by decide)).trans hU.index_eq
    have hvt := (frames 5 (by decide)).trans hU.todo_eq
    have hvo := (frames 6 (by decide)).trans hU.one_eq
    have mid := hV.setScalar 4 (show i+1≤B by omega)
    refine ⟨12,le_rfl,V,run,hvi,hvt,hvo,Store.size_le_of_bounded mid,?_⟩
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [advance,hvi] using mid.setScalar 5 (show V.scalar 5-1≤B by rw [hvt];omega)
    · simpa [advance] using (frames 0 (by decide)).trans hU.left_eq
    · simpa [advance] using (frames 1 (by decide)).trans hU.right_eq
    · simpa [advance] using (frames 2 (by decide)).trans hU.order_eq
    · simp [advance,hvi]
    · simp [advance,hvt];omega
    · simpa [advance] using hvo
    · simpa [advance,arrays 0 (by decide)] using hU.table_eq
    · simpa [advance,arrays 1 (by decide)] using hU.table'_eq
    · simpa [advance,harray] using hU.length_eq
    · intro j hj
      change IndexedRefinement.read (V.array 2) j=_
      rw [harray,hU.index_eq,hvalue]
      by_cases hji : j=i
      · subst j;simp [IndexedRefinement.read,hU.length_eq,hi]
      · have hj' : j < i := by omega
        simpa [IndexedRefinement.read,List.getElem?_set,hji,Ne.symm hji] using hU.values_eq j hj'
  obtain ⟨t,htt,T,run,hT⟩ := countedLoop_runs (storageBound Reg Arr B) 4 5 3 6 body
    ((n*m)*(n*m)) 12 I S (Store.size_le_of_bounded hS) (Store.size_le_of_bounded hcopy)
    start control (by decide) (by decide) step
  refine ⟨t,by omega,T,run,hT.bounded,?_⟩
  apply List.ext_getElem
  · simpa [GroupInitial.tableWord] using hT.length_eq
  · intro j hj hj'
    have hh := hT.values_eq j (by simpa [hT.length_eq] using hj)
    simpa only [IndexedRefinement.read,List.getElem?_eq_getElem hj,List.getElem?_eq_getElem hj',Option.getD_some] using hh

def prelude : List (Atom Reg Arr) := [
  .binary .mul 2 0 1,.binary .mul 3 2 2,.const 6 1,.const 18 0,.allocate 2 3 18]
def generate : Code := .seq (atoms prelude) fill

theorem generate_runs {n m : ℕ} (f : Fin n → Fin n → Fin n) (g : Fin m → Fin m → Fin m)
    (S : Store Reg Arr) (B : ℕ) (hS : S.Bounded B)
    (hn : S.scalar 0=n) (hm : S.scalar 1=m)
    (ht : S.array 0=GroupInitial.tableWord f) (ht' : S.array 1=GroupInitial.tableWord g)
    (hpos : 0<n*m) (hsize : (n*m)*(n*m)≤B) :
    ∃ t≤15*((n*m)*(n*m))+8,∃ T,Runs (storageBound Reg Arr B) generate S t T ∧ T.Bounded B ∧
      T.array 2=GroupInitial.tableWord (productOp f g) := by
  have hNB : n*m≤B := by nlinarith
  have hnB : n*n≤B := by
    have hmpos : 0<m := Nat.pos_of_mul_pos_left hpos
    have hle : n≤n*m := Nat.le_mul_of_pos_right _ hmpos
    exact (Nat.mul_self_le_mul_self hle).trans hsize
  have hmB : m*m≤B := by
    have hnpos : 0<n := Nat.pos_of_mul_pos_right hpos
    have hle : m≤n*m := Nat.le_mul_of_pos_left _ hnpos
    exact (Nat.mul_self_le_mul_self hle).trans hsize
  have h1 : 1≤B := by omega
  have valid : ValidAtoms B prelude S := by
    simp [prelude,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar,hn,hm,hNB,hsize,h1]
  obtain ⟨init,hU⟩ := atoms_runs hS prelude valid
  let U := applyAtoms prelude S
  obtain ⟨t,htime,T,run,hT,hword⟩ := fill_runs f g U B hU
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar,hn])
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar,hm])
    (by simp [U,applyAtoms,prelude,Atom.apply,BinaryOp.eval,Store.setScalar,hn,hm])
    (by simp [U,applyAtoms,prelude,Atom.apply,BinaryOp.eval,Store.setScalar,hn,hm])
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar])
    (by simpa [U,applyAtoms,prelude,Atom.apply,Store.setArray] using ht)
    (by simpa [U,applyAtoms,prelude,Atom.apply,Store.setArray] using ht')
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar,Store.setArray,BinaryOp.eval,hn,hm]) hnB hmB hNB
  exact ⟨5+t,by omega,T,Runs.seq init run,hT,hword⟩
end GroupWL.MachinePrograms.ProductGroupTable
