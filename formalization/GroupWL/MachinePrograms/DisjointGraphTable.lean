import GroupWL.MachinePrograms.GraphInitial
import GroupWL.MachinePrograms.ArrayTabulate

/-! A concrete adjacency matrix for the disjoint union of two finite graphs. -/
namespace GroupWL.MachinePrograms.DisjointGraphTable
open NatArrayLanguage
abbrev Reg := Fin 15
abbrev Arr := Fin 3
abbrev Code := Program Reg Arr
set_option maxRecDepth 4096

def sumAdj {n m : ℕ} (f : Fin n → Fin n → Bool) (g : Fin m → Fin m → Bool)
    (x y : Fin (n+m)) : Bool :=
  match finSumFinEquiv.symm x,finSumFinEquiv.symm y with
  | .inl a,.inl b => f a b
  | .inr a,.inr b => g a b
  | _,_ => false

def selectBase (n m : ℕ) (right : Bool) := if right then m else n

def queryAtoms (right : Bool) : List (Atom Reg Arr) :=
  (if right then [.binary .sub 7 7 0,.binary .sub 8 8 0] else []) ++
  [.binary .mul 12 (if right then 1 else 0) 7,.binary .add 12 8 12,
    .read 13 (if right then 1 else 0) 12]

theorem query_runs (right : Bool) (n m : ℕ)
    (f : Fin (selectBase n m right) → Fin (selectBase n m right) → Bool)
    (a b : Fin (selectBase n m right)) (S : Store Reg Arr) (B : ℕ) (hS : S.Bounded B)
    (hn : S.scalar 0=n) (hm : S.scalar 1=m)
    (ha : S.scalar 7=(if right then n else 0)+a.val) (hb : S.scalar 8=(if right then n else 0)+b.val)
    (ht : S.array (if right then 1 else 0)=GraphInitial.tableWord f)
    (hroom : selectBase n m right*selectBase n m right≤B) :
    ∃ t≤5,∃ T,Runs (storageBound Reg Arr B) (atoms (queryAtoms right)) S t T ∧ T.Bounded B ∧
      T.scalar 13=IndexedRefinement.boolNat (f a b) := by
  have hindex : b.val+selectBase n m right*a.val<selectBase n m right*selectBase n m right := (finProdFinEquiv (a,b)).isLt
  have hadd : b.val+selectBase n m right*a.val≤B := (Nat.le_of_lt hindex).trans hroom
  have hmul : selectBase n m right*a.val≤B :=
    (Nat.mul_le_mul_left _ (Nat.le_of_lt a.isLt)).trans hroom
  have har := hS.1 7
  have hbr := hS.1 8
  have valid : ValidAtoms B (queryAtoms right) S := by
    cases right <;> dsimp [selectBase] at *
    all_goals
      simp [queryAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar,
        hn,hm,ha,hb,ht,GraphInitial.tableWord_read,hmul,hadd,hindex] <;> omega
  obtain ⟨run,hT⟩ := atoms_runs hS _ valid
  refine ⟨(queryAtoms right).length,by cases right <;> decide,_,run,hT,?_⟩
  cases right <;> dsimp [selectBase] at * <;> simp [applyAtoms,queryAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,
    hn,hm,ha,hb,ht,GraphInitial.tableWord_read]

def prepare : List (Atom Reg Arr) := [.divmod 7 8 3 2,.binary .lt 9 7 0,.binary .lt 10 8 0,.binary .eq 11 9 10]
def point : Code := .seq (atoms prepare)
  (.branch 11 (.branch 9 (atoms (queryAtoms false)) (atoms (queryAtoms true))) (.atom (.const 13 0)))

structure Context {n m : ℕ} (f : Fin n → Fin n → Bool) (g : Fin m → Fin m → Bool) (S : Store Reg Arr) : Prop where
  left_eq : S.scalar 0=n
  right_eq : S.scalar 1=m
  total_eq : S.scalar 2=n+m
  left_table : S.array 0=GraphInitial.tableWord f
  right_table : S.array 1=GraphInitial.tableWord g

theorem point_runs {n m : ℕ} (f : Fin n → Fin n → Bool) (g : Fin m → Fin m → Bool)
    (x y : Fin (n+m)) (S : Store Reg Arr) (B : ℕ) (hS : S.Bounded B) (hP : Context f g S)
    (hi : S.scalar 3=(finProdFinEquiv (x,y)).val) (hroom : (n+m)*(n+m)≤B) :
    ∃ t≤11,∃ T,Runs (storageBound Reg Arr B) point S t T ∧ T.Bounded B ∧ Context f g T ∧
      T.scalar 3=S.scalar 3 ∧ T.scalar 4=S.scalar 4 ∧ T.scalar 5=S.scalar 5 ∧ T.array 2=S.array 2 ∧
      T.scalar 13=IndexedRefinement.boolNat (sumAdj f g x y) := by
  have hpos : 0<n+m := by have := x.isLt;omega
  have h1 : 1≤B := by nlinarith
  have hnB : n*n≤B := (Nat.mul_self_le_mul_self (Nat.le_add_right _ _)).trans hroom
  have hmB : m*m≤B := (Nat.mul_self_le_mul_self (Nat.le_add_left _ _)).trans hroom
  have valid : ValidAtoms B prepare S := by
    simp [prepare,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar,hP.total_eq,hpos]
    split_ifs <;>omega
  obtain ⟨first,hU⟩ := atoms_runs hS prepare valid
  let U := applyAtoms prepare S
  have us (j : Reg) (hj : j.val<7) : U.scalar j=S.scalar j := by
    have h7 : j≠7 := Fin.ne_of_val_ne (by omega)
    have h8 : j≠8 := Fin.ne_of_val_ne (by omega)
    have h9 : j≠9 := Fin.ne_of_val_ne (by omega)
    have h10 : j≠10 := Fin.ne_of_val_ne (by omega)
    have h11 : j≠11 := Fin.ne_of_val_ne (by omega)
    simp [U,applyAtoms,prepare,Atom.apply,Store.setScalar,h7,h8,h9,h10,h11]
  have ux : U.scalar 7=x.val := by
    simp [U,applyAtoms,prepare,Atom.apply,Store.setScalar,hP.total_eq,hi,finProdFinEquiv,
      Nat.add_mul_div_left,Nat.div_eq_of_lt y.isLt,hpos]
  have uy : U.scalar 8=y.val := by
    simp [U,applyAtoms,prepare,Atom.apply,Store.setScalar,hP.total_eq,hi,finProdFinEquiv,Nat.mod_eq_of_lt y.isLt]
  have u9 : U.scalar 9=if x.val<n then 1 else 0 := by
    simp [U,applyAtoms,prepare,Atom.apply,BinaryOp.eval,Store.setScalar,hP.left_eq,hP.total_eq,hi,finProdFinEquiv,
      Nat.add_mul_div_left,Nat.div_eq_of_lt y.isLt,hpos]
  have u11 : U.scalar 11=if (x.val<n ↔ y.val<n) then 1 else 0 := by
    simp [U,applyAtoms,prepare,Atom.apply,BinaryOp.eval,Store.setScalar,hP.left_eq,hP.total_eq,hi,finProdFinEquiv,
      Nat.add_mul_div_left,Nat.div_eq_of_lt y.isLt,Nat.mod_eq_of_lt y.isLt,hpos]
    split_ifs <;>simp_all <;>omega
  have rest : ∃ t≤7,∃ T,Runs (storageBound Reg Arr B)
      (.branch 11 (.branch 9 (atoms (queryAtoms false)) (atoms (queryAtoms true))) (.atom (.const 13 0)))
      U t T ∧ T.Bounded B ∧ T.scalar 13=IndexedRefinement.boolNat (sumAdj f g x y) := by
    obtain ⟨x,rfl⟩ := finSumFinEquiv.surjective x
    obtain ⟨y,rfl⟩ := finSumFinEquiv.surjective y
    cases x with
    | inl a => cases y with
      | inl b =>
        obtain ⟨t,ht,T,run,hT,hout⟩ := query_runs false n m f a b U B hU
          ((us 0 (by decide)).trans hP.left_eq) ((us 1 (by decide)).trans hP.right_eq)
          (by simpa using ux) (by simpa using uy) hP.left_table hnB
        refine ⟨(t+1)+1,by omega,T,Runs.branch_nonzero (by simp [u11,a.isLt,b.isLt])
          (Runs.branch_nonzero (by simp [u9,a.isLt]) run),hT,?_⟩
        simpa [sumAdj] using hout
      | inr b =>
        have run := atom_runs hU (.const 13 0) trivial (Nat.zero_le B)
        refine ⟨2,by omega,_,Runs.branch_zero (by simp [u11,a.isLt,show ¬n+b.val<n by omega]) run,
          Atom.apply_bounded hU _ (Nat.zero_le B),?_⟩
        simp [Atom.apply,sumAdj,IndexedRefinement.boolNat]
    | inr a => cases y with
      | inl b =>
        have run := atom_runs hU (.const 13 0) trivial (Nat.zero_le B)
        refine ⟨2,by omega,_,Runs.branch_zero (by simp [u11,b.isLt,show ¬n+a.val<n by omega]) run,
          Atom.apply_bounded hU _ (Nat.zero_le B),?_⟩
        simp [Atom.apply,sumAdj,IndexedRefinement.boolNat]
      | inr b =>
        obtain ⟨t,ht,T,run,hT,hout⟩ := query_runs true n m g a b U B hU
          ((us 0 (by decide)).trans hP.left_eq) ((us 1 (by decide)).trans hP.right_eq)
          (by simpa using ux) (by simpa using uy) hP.right_table hmB
        refine ⟨(t+1)+1,by omega,T,Runs.branch_nonzero (by simp [u11,show ¬n+a.val<n by omega,show ¬n+b.val<n by omega])
          (Runs.branch_zero (by simp [u9,show ¬n+a.val<n by omega]) run),hT,?_⟩
        simpa [sumAdj] using hout
  obtain ⟨t,ht,T,last,hT,hout⟩ := rest
  have run : Runs (storageBound Reg Arr B) point S (4+t) T := Runs.seq first last
  have sf (j : Reg) (hj : j.val<7) : T.scalar j=S.scalar j := by
    apply run.scalar_eq_of_not_mem
    simp [point,prepare,queryAtoms,atoms,NatArrayLanguage.sequence,Program.scalarWrites,Atom.scalarWrites]
    repeat' constructor
    all_goals apply Fin.ne_of_val_ne;omega
  have af (j : Arr) : T.array j=S.array j := run.array_eq_of_not_mem j (by
    simp [point,prepare,queryAtoms,atoms,NatArrayLanguage.sequence,Program.arrayWrites,Atom.arrayWrites])
  exact ⟨4+t,by omega,T,run,hT,⟨(sf 0 (by decide)).trans hP.left_eq,(sf 1 (by decide)).trans hP.right_eq,
    (sf 2 (by decide)).trans hP.total_eq,(af 0).trans hP.left_table,(af 1).trans hP.right_table⟩,
    sf 3 (by decide),sf 4 (by decide),sf 5 (by decide),af 2,hout⟩

def fill : Code := ArrayTabulate.tabulate 3 4 14 5 6 13 2 point

theorem fill_runs {n m : ℕ} (f : Fin n → Fin n → Bool) (g : Fin m → Fin m → Bool)
    (S : Store Reg Arr) (B : ℕ) (hS : S.Bounded B) (hP : Context f g S)
    (hlimit : S.scalar 14=(n+m)*(n+m)) (hone : S.scalar 5=1) (hzero : S.scalar 6=0) (hroom : (n+m)*(n+m)≤B) :
    ∃ t≤((n+m)*(n+m))*15+4,∃ T,Runs (storageBound Reg Arr B) fill S t T ∧ T.Bounded B ∧
      Context f g T ∧ T.array 2=GraphInitial.tableWord (sumAdj f g) := by
  apply ArrayTabulate.tabulate_runs 3 4 14 5 6 13 2 point
    (fun i => IndexedRefinement.boolNat (sumAdj f g (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2))
    (Context f g) B 11
  · intro U v hU;exact ⟨by simpa using hU.left_eq,by simpa using hU.right_eq,by simpa using hU.total_eq,hU.left_table,hU.right_table⟩
  · intro U v hU;exact ⟨by simpa using hU.left_eq,by simpa using hU.right_eq,by simpa using hU.total_eq,hU.left_table,hU.right_table⟩
  · intro U xs hU;exact ⟨hU.left_eq,hU.right_eq,hU.total_eq,by simpa using hU.left_table,by simpa using hU.right_table⟩
  · decide
  · decide
  · decide
  · intro i U hp hb hi htodo hone
    let xy := finProdFinEquiv.symm i
    obtain ⟨t,ht,V,run,hV,hPV,hidx,htd,ho,ha,hvalue⟩ := point_runs f g xy.1 xy.2 U B hb hp
      (by change U.scalar 3= i.val%(n+m)+(n+m)*(i.val/(n+m));exact hi.trans (Nat.mod_add_div i.val (n+m)).symm) hroom
    exact ⟨t,ht,V,run,hV,hPV,hidx.trans hi,htd.trans htodo,ho.trans hone,hvalue,ha⟩
  · exact hS
  · exact hP
  · exact hlimit
  · exact hone
  · exact hzero

def prelude : List (Atom Reg Arr) := [.binary .add 2 0 1,.binary .mul 14 2 2,.const 5 1,.const 6 0]
def generate : Code := .seq (atoms prelude) fill

theorem generate_runs {n m : ℕ} (f : Fin n → Fin n → Bool) (g : Fin m → Fin m → Bool)
    (S : Store Reg Arr) (B : ℕ) (hS : S.Bounded B) (hn : S.scalar 0=n) (hm : S.scalar 1=m)
    (ht : S.array 0=GraphInitial.tableWord f) (ht' : S.array 1=GraphInitial.tableWord g)
    (hpos : 0<n+m) (hroom : (n+m)*(n+m)≤B) :
    ∃ t≤((n+m)*(n+m))*15+8,∃ T,Runs (storageBound Reg Arr B) generate S t T ∧ T.Bounded B ∧
      Context f g T ∧ T.array 2=GraphInitial.tableWord (sumAdj f g) := by
  have hN : n+m≤B := by nlinarith
  have h1 : 1≤B := by omega
  have valid : ValidAtoms B prelude S := by
    simp [prelude,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar,hn,hm,hN,hroom,h1]
  obtain ⟨first,hU⟩ := atoms_runs hS prelude valid
  let U := applyAtoms prelude S
  have hP : Context f g U := by
    refine ⟨?_,?_,?_,ht,ht'⟩
    all_goals simp [U,applyAtoms,prelude,Atom.apply,BinaryOp.eval,Store.setScalar,hn,hm]
  obtain ⟨t,htt,T,last,hT,hPT,hword⟩ := fill_runs f g U B hU hP
    (by simp [U,applyAtoms,prelude,Atom.apply,BinaryOp.eval,Store.setScalar,hn,hm])
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar])
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar]) hroom
  exact ⟨4+t,by omega,T,Runs.seq first last,hT,hPT,hword⟩
end GroupWL.MachinePrograms.DisjointGraphTable
