import GroupWL.MachinePrograms.NatArrayFrames
import GroupWL.MachinePrograms.NatArrayCountedLoops

/-! Array concatenation by bounded indexed reads and writes. -/
namespace GroupWL.MachinePrograms.NatArrayConcat
open NatArrayLanguage
abbrev Reg := Fin 10
abbrev Arr := Fin 3
abbrev Code := Program Reg Arr
set_option maxRecDepth 2048

def choose : Code := .branch 6 (.atom (.read 8 0 3))
  (atoms [.binary .sub 7 3 0,.read 8 1 7])

def body : Code := .seq (.atom (.binary .lt 6 3 0)) (.seq choose (.atom (.write 2 3 8)))

theorem body_runs (S : Store Reg Arr) (B i : ℕ) (xs ys : List ℕ) (hS : S.Bounded B)
    (hx : S.array 0=xs) (hy : S.array 1=ys) (hl : S.scalar 0=xs.length) (hi : S.scalar 3=i)
    (hout : (S.array 2).length=xs.length+ys.length) (hil : i<xs.length+ys.length) :
    ∃ t≤5,∃ T,Runs (storageBound Reg Arr B) body S t T ∧ T.Bounded B ∧
      T.array 2=(S.array 2).set i ((xs++ys)[i]?.getD 0) := by
  have h1 : 1≤B := by have := hS.2.1 2; omega
  let A := S.setScalar 6 (if i<xs.length then 1 else 0)
  have first : Runs (storageBound Reg Arr B) (.atom (.binary .lt 6 3 0)) S 1 A := by
    have run := atom_runs hS (.binary .lt 6 3 0) trivial
      (by simp [Atom.SmallResult,BinaryOp.eval,hi,hl]; split_ifs <;> omega)
    simpa [Atom.apply,BinaryOp.eval,A,hi,hl] using run
  have hA : A.Bounded B := hS.setScalar _ (by split_ifs <;> omega)
  have branch : ∃ t≤3,∃ U,Runs (storageBound Reg Arr B) choose A t U ∧ U.Bounded B ∧
      U.scalar 8=(xs++ys)[i]?.getD 0 ∧ U.scalar 3=i ∧ U.array 2=S.array 2 := by
    by_cases hix : i<xs.length
    · have valid : (Atom.read 8 0 3).Valid A := by simp [Atom.Valid,A,hi,hx,hix]
      have read := atom_runs hA (.read 8 0 3) valid trivial
      refine ⟨2,by omega,_,Runs.branch_nonzero (by simp [A,hix]) read,
        (Atom.read 8 0 3).apply_bounded hA trivial,?_,?_,rfl⟩
      · simp [Atom.apply,A,hx,hi,List.getElem?_append_left hix]
      · simp [Atom.apply,A,hi]
    · have hsmall : (Atom.binary .sub 7 3 0).SmallResult B A := by
        simp [Atom.SmallResult,BinaryOp.eval,A,hi,hl]
        have := hS.1 3
        omega
      have valid : ValidAtoms B [.binary .sub 7 3 0,.read 8 1 7] A := by
        simp [ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
          Store.setScalar,Function.update_apply,A,hi,hl,hy]
        have hbound := hS.1 3
        constructor <;> omega
      obtain ⟨run,hU⟩ := atoms_runs hA _ valid
      refine ⟨3,le_rfl,_,Runs.branch_zero (by simp [A,hix]) run,hU,?_,?_,rfl⟩
      · simp [applyAtoms,Atom.apply,BinaryOp.eval,A,Store.setScalar,hi,hl,hy,
          List.getElem?_append_right (by omega : xs.length ≤ i)]
      · simp [applyAtoms,Atom.apply,Store.setScalar,A,hi]
  obtain ⟨t,ht,U,run,hU,hvalue,hindex,harray⟩ := branch
  have valid : (Atom.write 2 3 8).Valid U := by simp [Atom.Valid,hindex,harray,hout,hil]
  have write := atom_runs hU (.write 2 3 8) valid trivial
  refine ⟨1+(t+1),by omega,_,Runs.seq first (Runs.seq run write),
    (Atom.write 2 3 8).apply_bounded hU trivial,?_⟩
  simp [Atom.apply,hindex,harray,hvalue]

private structure Invariant (xs ys : List ℕ) (B i : ℕ) (S : Store Reg Arr) : Prop where
  bounded : S.Bounded B
  left_eq : S.array 0=xs
  right_eq : S.array 1=ys
  leftLength_eq : S.scalar 0=xs.length
  index_eq : S.scalar 3=i
  todo_eq : S.scalar 4=xs.length+ys.length-i
  one_eq : S.scalar 5=1
  length_eq : (S.array 2).length=xs.length+ys.length
  values_eq : ∀ j < i,(S.array 2)[j]?.getD 0=(xs++ys)[j]?.getD 0

def fill : Code := countedLoop 3 4 2 5 body

theorem fill_runs (S : Store Reg Arr) (B : ℕ) (xs ys : List ℕ) (hS : S.Bounded B)
    (hx : S.array 0=xs) (hy : S.array 1=ys) (hl : S.scalar 0=xs.length)
    (htotal : S.scalar 2=xs.length+ys.length) (hone : S.scalar 5=1)
    (hout : (S.array 2).length=xs.length+ys.length) :
    ∃ t≤8*(xs.length+ys.length)+3,∃ T,Runs (storageBound Reg Arr B) fill S t T ∧
      T.Bounded B ∧ T.array 2=xs++ys := by
  have hsize : xs.length+ys.length≤B := by simpa [htotal] using hS.1 2
  let I := Invariant xs ys B
  have hcopy : (S.setScalar 4 (S.scalar 2)).Bounded B := hS.setScalar _ (hS.1 _)
  have hstart : I 0 ((S.setScalar 4 (S.scalar 2)).setScalar 3 0) := by
    refine ⟨hcopy.setScalar _ (Nat.zero_le _),hx,hy,?_,?_,?_,?_,hout,?_⟩
    · simp [hl]
    · simp
    · simp [htotal]
    · simp [hone]
    · intro j hj; omega
  have control : ∀ i≤xs.length+ys.length,∀ U,I i U → U.scalar 3=i ∧
      U.scalar 4=xs.length+ys.length-i ∧ U.scalar 5=1 ∧ U.size≤storageBound Reg Arr B := by
    intro i hi U hU
    exact ⟨hU.index_eq,hU.todo_eq,hU.one_eq,Store.size_le_of_bounded hU.bounded⟩
  have step : ∀ i<xs.length+ys.length,∀ U,I i U → ∃ t≤5,∃ V,
      Runs (storageBound Reg Arr B) body U t V ∧ V.scalar 3=i ∧
      V.scalar 4=xs.length+ys.length-i ∧ V.scalar 5=1 ∧
      (V.setScalar 3 (i+1)).size≤storageBound Reg Arr B ∧ I (i+1) (advance 3 4 V) := by
    intro i hi U hU
    obtain ⟨t,ht,V,run,hV,harray⟩ := body_runs U B i xs ys hU.bounded hU.left_eq hU.right_eq
      hU.leftLength_eq hU.index_eq hU.length_eq hi
    have scalars (r : Reg) (hr : r∈({0,3,4,5} : Finset Reg)) : V.scalar r=U.scalar r := by
      apply run.scalar_eq_of_not_mem
      fin_cases r <;> simp_all [body,choose,atoms,NatArrayLanguage.sequence,Program.scalarWrites,Atom.scalarWrites]
    have arrays (a : Arr) (ha : a≠2) : V.array a=U.array a := run.array_eq_of_not_mem a (by
      simp [body,choose,atoms,NatArrayLanguage.sequence,Program.arrayWrites,Atom.arrayWrites,ha])
    have hvi : V.scalar 3=i := (scalars _ (by simp)).trans hU.index_eq
    have hvr : V.scalar 4=xs.length+ys.length-i := (scalars _ (by simp)).trans hU.todo_eq
    have hvo : V.scalar 5=1 := (scalars _ (by simp)).trans hU.one_eq
    have hmid := hV.setScalar 3 (show i+1≤B by omega)
    refine ⟨t,ht,V,run,hvi,hvr,hvo,Store.size_le_of_bounded hmid,?_⟩
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [advance,hvi] using hmid.setScalar 4 (show V.scalar 4-1≤B by rw [hvr]; omega)
    · simpa [advance] using (arrays 0 (by decide)).trans hU.left_eq
    · simpa [advance] using (arrays 1 (by decide)).trans hU.right_eq
    · simpa [advance] using (scalars 0 (by simp)).trans hU.leftLength_eq
    · simp [advance,hvi]
    · simp [advance,hvr]; omega
    · simpa [advance] using hvo
    · simpa [advance,harray] using hU.length_eq
    · intro j hj
      change (V.array 2)[j]?.getD 0=(xs++ys)[j]?.getD 0
      rw [harray]
      by_cases hji : j=i
      · subst j; simp [hU.length_eq,hi]
      · have hji' : j < i := by omega
        simpa [List.getElem?_set,hji,Ne.symm hji] using hU.values_eq j hji'
  obtain ⟨t,ht,T,run,hT⟩ := countedLoop_runs (storageBound Reg Arr B) 3 4 2 5 body
    (xs.length+ys.length) 5 I S (Store.size_le_of_bounded hS) (Store.size_le_of_bounded hcopy)
    hstart control (by decide) (by decide) step
  refine ⟨t,by omega,T,run,hT.bounded,?_⟩
  apply List.ext_getElem
  · simpa using hT.length_eq
  · intro j hj hj'
    have hh := hT.values_eq j (by simpa [hT.length_eq] using hj)
    simpa only [List.getElem?_eq_getElem hj,List.getElem?_eq_getElem hj',Option.getD_some] using hh

def prelude : List (Atom Reg Arr) := [
  .arrayLength 0 0,.arrayLength 1 1,.binary .add 2 0 1,.const 5 1,.const 9 0,.allocate 2 2 9]

def concat : Code := .seq (atoms prelude) fill

theorem concat_runs (S : Store Reg Arr) (B : ℕ) (hS : S.Bounded B)
    (hlen : (S.array 0).length+(S.array 1).length≤B) (h1 : 1≤B) :
    ∃ t≤8*((S.array 0).length+(S.array 1).length)+9,∃ T,
      Runs (storageBound Reg Arr B) concat S t T ∧ T.Bounded B ∧
      T.array 2=S.array 0++S.array 1 ∧ T.array 0=S.array 0 ∧ T.array 1=S.array 1 := by
  have hvalid : ValidAtoms B prelude S := by
    simp [prelude,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,Function.update_apply,hlen,h1]
  obtain ⟨init,hU⟩ := atoms_runs hS prelude hvalid
  let U := applyAtoms prelude S
  have hx : U.array 0=S.array 0 := by simp [U,applyAtoms,prelude,Atom.apply,Store.setArray,Store.setScalar]
  have hy : U.array 1=S.array 1 := by simp [U,applyAtoms,prelude,Atom.apply,Store.setArray,Store.setScalar]
  have hl : U.scalar 0=(S.array 0).length := by simp [U,applyAtoms,prelude,Atom.apply,Store.setArray,Store.setScalar]
  have ht : U.scalar 2=(S.array 0).length+(S.array 1).length := by
    simp [U,applyAtoms,prelude,Atom.apply,BinaryOp.eval,Store.setArray,Store.setScalar]
  have ho : U.scalar 5=1 := by simp [U,applyAtoms,prelude,Atom.apply,Store.setArray,Store.setScalar]
  have hu : (U.array 2).length=(S.array 0).length+(S.array 1).length := by
    simp [U,applyAtoms,prelude,Atom.apply,BinaryOp.eval,Store.setArray,Store.setScalar]
  obtain ⟨t,htt,T,rest,hT,hout⟩ := fill_runs U B (S.array 0) (S.array 1) hU hx hy hl ht ho hu
  have run : Runs (storageBound Reg Arr B) concat S (6+t) T := Runs.seq init rest
  refine ⟨6+t,by omega,T,run,hT,hout,?_,?_⟩
  all_goals apply run.array_eq_of_not_mem
  all_goals simp [concat,prelude,fill,body,choose,countedLoop,atoms,NatArrayLanguage.sequence,
    Program.arrayWrites,Atom.arrayWrites]

end GroupWL.MachinePrograms.NatArrayConcat
