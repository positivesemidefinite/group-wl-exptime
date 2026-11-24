import GroupWL.MachinePrograms.NatArrayFrames
import GroupWL.MachinePrograms.NatArrayCountedLoops
import GroupWL.FiniteWL
import GroupWL.IndexedRefinement

/-! The Version-I initial relation is computed by table lookups and a finite
loop over coordinate triples. No group operation is an instruction. -/
namespace GroupWL.MachinePrograms.GroupInitial
open NatArrayLanguage
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

inductive Reg where
  | leftSize | rightSize | arity | limit | one | index | todo | quotient
  | first | second | third | leftFirst | leftSecond | leftThird
  | rightFirst | rightSecond | rightThird | address | leftProduct | rightProduct
  | leftEqual | rightEqual | equality | leftMult | rightMult | multiplication | result
  deriving DecidableEq,Fintype

inductive Arr where
  | leftTable | rightTable | leftTuple | rightTuple
  deriving DecidableEq,Fintype

abbrev Code := Program Reg Arr

def tableWord {n : ℕ} (mul : Fin n → Fin n → Fin n) : List ℕ :=
  List.ofFn (fun z : Fin (n*n) => (mul (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2).val)

def tupleWord {n k : ℕ} (a : Fin k → Fin n) : List ℕ := List.ofFn (fun i => (a i).val)

@[simp] theorem tableWord_length {n : ℕ} (mul : Fin n → Fin n → Fin n) :
    (tableWord mul).length=n*n := List.length_ofFn

@[simp] theorem tupleWord_length {n k : ℕ} (a : Fin k → Fin n) :
    (tupleWord a).length=k := List.length_ofFn

theorem tableWord_read {n : ℕ} (mul : Fin n → Fin n → Fin n) (a b : Fin n) :
    (tableWord mul)[b.val+n*a.val]?.getD 0=(mul a b).val := by
  have hi : b.val+n*a.val<n*n := (finProdFinEquiv (a,b)).isLt
  simp only [tableWord,List.getElem?_ofFn,dif_pos hi,Option.getD_some]
  change (mul (finProdFinEquiv.symm (finProdFinEquiv (a,b))).1
    (finProdFinEquiv.symm (finProdFinEquiv (a,b))).2).val=_
  rw [Equiv.symm_apply_apply]

theorem tupleWord_read {n k : ℕ} (a : Fin k → Fin n) (i : Fin k) :
    (tupleWord a)[i.val]?.getD 0=(a i).val := by simp [tupleWord,i.isLt]

def tripleTest {n m k : ℕ} (mul : Fin n → Fin n → Fin n) (mul' : Fin m → Fin m → Fin m)
    (a : Fin k → Fin n) (b : Fin k → Fin m) (i j l : Fin k) : Bool :=
  decide ((a i=a j ↔ b i=b j) ∧ (mul (a i) (a j)=a l ↔ mul' (b i) (b j)=b l))

def tripleAtoms : List (Atom Reg Arr) := [
  .read .leftFirst .leftTuple .first, .read .leftSecond .leftTuple .second,
  .read .leftThird .leftTuple .third,
  .read .rightFirst .rightTuple .first, .read .rightSecond .rightTuple .second,
  .read .rightThird .rightTuple .third,
  .binary .mul .address .leftSize .leftFirst,
  .binary .add .address .leftSecond .address,
  .read .leftProduct .leftTable .address,
  .binary .mul .address .rightSize .rightFirst,
  .binary .add .address .rightSecond .address,
  .read .rightProduct .rightTable .address,
  .binary .eq .leftEqual .leftFirst .leftSecond,
  .binary .eq .rightEqual .rightFirst .rightSecond,
  .binary .eq .equality .leftEqual .rightEqual,
  .binary .eq .leftMult .leftProduct .leftThird,
  .binary .eq .rightMult .rightProduct .rightThird,
  .binary .eq .multiplication .leftMult .rightMult,
  .binary .mul .result .result .equality,
  .binary .mul .result .result .multiplication]

def tripleBody : Code := atoms tripleAtoms

theorem tripleBody_runs {n m k : ℕ}
    (mul : Fin n → Fin n → Fin n) (mul' : Fin m → Fin m → Fin m)
    (a : Fin k → Fin n) (b : Fin k → Fin m) (i j l : Fin k)
    (S : Store Reg Arr) (B result : ℕ) (hS : S.Bounded B)
    (ht : S.array .leftTable=tableWord mul) (ht' : S.array .rightTable=tableWord mul')
    (ha : S.array .leftTuple=tupleWord a) (hb : S.array .rightTuple=tupleWord b)
    (hn : S.scalar .leftSize=n) (hm : S.scalar .rightSize=m)
    (hi : S.scalar .first=i.val) (hj : S.scalar .second=j.val) (hl : S.scalar .third=l.val)
    (hr : S.scalar .result=result) (hr1 : result≤1)
    (hroom : n*n≤B) (hroom' : m*m≤B) (h1 : 1≤B) :
    ∃ T,Runs (storageBound Reg Arr B) tripleBody S 20 T ∧ T.Bounded B ∧
      T.scalar .result=result*IndexedRefinement.boolNat (tripleTest mul mul' a b i j l) := by
  have hia := (finProdFinEquiv (a i,a j)).isLt
  have hib := (finProdFinEquiv (b i,b j)).isLt
  have hna : n*(a i).val≤B := (Nat.mul_le_mul_left n (Nat.le_of_lt (a i).isLt)).trans hroom
  have hmb : m*(b i).val≤B := (Nat.mul_le_mul_left m (Nat.le_of_lt (b i).isLt)).trans hroom'
  have hvalid : ValidAtoms B tripleAtoms S := by
    simp only [tripleAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,Function.update_apply]
    simp only [hn,hm,hi,hj,hl,hr,ht,ht',ha,hb,reduceCtorEq,if_true,if_false,
      tupleWord_length,tupleWord_read,tableWord_length,tableWord_read]
    repeat' constructor
    all_goals first | exact i.isLt | exact j.isLt | exact l.isLt | exact hia | exact hib | exact hna | exact hmb | trivial | skip
    all_goals (try split_ifs) <;> simp_all <;> omega
  obtain ⟨run,hT⟩ := atoms_runs hS tripleAtoms hvalid
  refine ⟨applyAtoms tripleAtoms S,run,hT,?_⟩
  simp only [applyAtoms,tripleAtoms,List.foldl_cons,List.foldl_nil,Atom.apply,BinaryOp.eval,
    Store.setScalar,Function.update_apply]
  simp only [hn,hm,hi,hj,hl,hr,ht,ht',ha,hb,reduceCtorEq,if_true,if_false,
    tupleWord_read,tableWord_read]
  simp only [tripleTest,IndexedRefinement.boolNat,Fin.ext_iff]
  split_ifs <;> simp_all <;> omega

def signature {n k : ℕ} (mul : Fin n → Fin n → Fin n) (a : Fin k → Fin n) :=
  (fun i j => decide (a i=a j),fun i j l => decide (mul (a i) (a j)=a l))

theorem signature_eq_iff {n m k : ℕ}
    (mul : Fin n → Fin n → Fin n) (mul' : Fin m → Fin m → Fin m)
    (a : Fin k → Fin n) (b : Fin k → Fin m) :
    signature mul a=signature mul' b ↔ ∀ i j l,tripleTest mul mul' a b i j l=true := by
  constructor
  · intro h i j l
    have he := congrFun (congrFun (congrArg Prod.fst h) i) j
    have hm := congrFun (congrFun (congrFun (congrArg Prod.snd h) i) j) l
    simpa [tripleTest,signature] using
      And.intro (Bool.eq_iff_iff.mp he) (Bool.eq_iff_iff.mp hm)
  · intro h
    apply Prod.ext
    · funext i j
      apply Bool.eq_iff_iff.mpr
      have hh := h i j i
      simp only [tripleTest,decide_eq_true_eq] at hh
      simpa [signature] using hh.1
    · funext i j l
      apply Bool.eq_iff_iff.mpr
      have hh := h i j l
      simp only [tripleTest,decide_eq_true_eq] at hh
      simpa [signature] using hh.2

def testAt {n m k : ℕ} (mul : Fin n → Fin n → Fin n) (mul' : Fin m → Fin m → Fin m)
    (a : Fin k → Fin n) (b : Fin k → Fin m) (index : ℕ) : Bool :=
  if hi : index < k^3 then
    let v := finFunctionFinEquiv.symm (⟨index,hi⟩ : Fin (k^3))
    tripleTest mul mul' a b (v 0) (v 1) (v 2)
  else false

def prefixTest {n m k : ℕ} (mul : Fin n → Fin n → Fin n) (mul' : Fin m → Fin m → Fin m)
    (a : Fin k → Fin n) (b : Fin k → Fin m) (i : ℕ) : ℕ :=
  IndexedRefinement.boolNat ((List.range i).all (testAt mul mul' a b))

theorem prefixTest_le {n m k : ℕ} (mul : Fin n → Fin n → Fin n)
    (mul' : Fin m → Fin m → Fin m) (a : Fin k → Fin n) (b : Fin k → Fin m) (i : ℕ) :
    prefixTest mul mul' a b i≤1 := IndexedRefinement.boolNat_le_one _

theorem prefixTest_succ {n m k : ℕ} (mul : Fin n → Fin n → Fin n)
    (mul' : Fin m → Fin m → Fin m) (a : Fin k → Fin n) (b : Fin k → Fin m) (i : ℕ) :
    prefixTest mul mul' a b (i+1)=
      prefixTest mul mul' a b i*IndexedRefinement.boolNat (testAt mul mul' a b i) := by
  simp only [prefixTest,List.range_succ,List.all_append,List.all_cons,List.all_nil,Bool.and_true]
  generalize (List.range i).all (testAt mul mul' a b)=x
  generalize testAt mul mul' a b i=y
  cases x <;> cases y <;> rfl

theorem prefixTest_correct {n m k : ℕ} (mul : Fin n → Fin n → Fin n)
    (mul' : Fin m → Fin m → Fin m) (a : Fin k → Fin n) (b : Fin k → Fin m) :
    prefixTest mul mul' a b (k^3)=1 ↔ signature mul a=signature mul' b := by
  rw [signature_eq_iff]
  simp only [prefixTest,IndexedRefinement.boolNat_eq_one,List.all_eq_true,List.mem_range]
  constructor
  · intro h i j l
    let v : Fin 3 → Fin k := ![i,j,l]
    have hh := h (finFunctionFinEquiv v).val (finFunctionFinEquiv v).isLt
    rw [testAt,dif_pos (finFunctionFinEquiv v).isLt] at hh
    change tripleTest mul mul' a b ((finFunctionFinEquiv.symm (finFunctionFinEquiv v)) 0)
      ((finFunctionFinEquiv.symm (finFunctionFinEquiv v)) 1)
      ((finFunctionFinEquiv.symm (finFunctionFinEquiv v)) 2)=true at hh
    rw [Equiv.symm_apply_apply] at hh
    exact hh
  · intro h index hi
    exact (by simpa [testAt,hi] using (h
      (finFunctionFinEquiv.symm (⟨index,hi⟩ : Fin (k^3)) 0)
      (finFunctionFinEquiv.symm (⟨index,hi⟩ : Fin (k^3)) 1)
      (finFunctionFinEquiv.symm (⟨index,hi⟩ : Fin (k^3)) 2)))

def decodeTripleAtoms : List (Atom Reg Arr) := [
  .divmod .quotient .first .index .arity,
  .divmod .quotient .second .quotient .arity,
  .divmod .quotient .third .quotient .arity]

def decodeTriple : Code := atoms decodeTripleAtoms

theorem decodeTriple_runs (S : Store Reg Arr) (B k : ℕ) (z : Fin (k^3))
    (hS : S.Bounded B) (hk : S.scalar .arity=k) (hz : S.scalar .index=z.val) :
    ∃ T,Runs (storageBound Reg Arr B) decodeTriple S 3 T ∧ T.Bounded B ∧
      T.scalar .first=(finFunctionFinEquiv.symm z 0).val ∧
      T.scalar .second=(finFunctionFinEquiv.symm z 1).val ∧
      T.scalar .third=(finFunctionFinEquiv.symm z 2).val := by
  have hkpos : 0<k := by
    by_contra h
    have hk0 : k=0 := by omega
    have hzlt := z.isLt
    simp [hk0] at hzlt
  have hvalid : ValidAtoms B decodeTripleAtoms S := by
    simp only [decodeTripleAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,
      Store.setScalar,Function.update_apply,reduceCtorEq,if_false,hk]
    exact ⟨⟨by decide,hkpos⟩,trivial,⟨by decide,hkpos⟩,trivial,⟨by decide,hkpos⟩,trivial,trivial⟩
  obtain ⟨run,hT⟩ := atoms_runs hS decodeTripleAtoms hvalid
  refine ⟨applyAtoms decodeTripleAtoms S,run,hT,?_,?_,?_⟩
  all_goals
    simp only [applyAtoms,decodeTripleAtoms,List.foldl_cons,List.foldl_nil,Atom.apply,
      Store.setScalar,Function.update_apply,reduceCtorEq,if_true,if_false,hk,hz]
  · change z.val%k=z.val/k^0%k
    simp
  · change z.val/k%k=z.val/k^1%k
    simp
  · change z.val/k/k%k=z.val/k^2%k
    rw [Nat.div_div_eq_div_mul,pow_two]

def entryBody : Code := .seq decodeTriple tripleBody

theorem entryBody_runs {n m k : ℕ}
    (mul : Fin n → Fin n → Fin n) (mul' : Fin m → Fin m → Fin m)
    (a : Fin k → Fin n) (b : Fin k → Fin m) (z : Fin (k^3))
    (S : Store Reg Arr) (B result : ℕ) (hS : S.Bounded B)
    (ht : S.array .leftTable=tableWord mul) (ht' : S.array .rightTable=tableWord mul')
    (ha : S.array .leftTuple=tupleWord a) (hb : S.array .rightTuple=tupleWord b)
    (hn : S.scalar .leftSize=n) (hm : S.scalar .rightSize=m)
    (hk : S.scalar .arity=k) (hz : S.scalar .index=z.val)
    (hr : S.scalar .result=result) (hr1 : result≤1)
    (hroom : n*n≤B) (hroom' : m*m≤B) (h1 : 1≤B) :
    ∃ T,Runs (storageBound Reg Arr B) entryBody S 23 T ∧ T.Bounded B ∧
      T.scalar .result=result*IndexedRefinement.boolNat (testAt mul mul' a b z.val) := by
  obtain ⟨U,run,hU,hi,hj,hl⟩ := decodeTriple_runs S B k z hS hk hz
  have arrays (ar : Arr) : U.array ar=S.array ar := run.array_eq_of_not_mem ar (by
    simp [decodeTriple,atoms,decodeTripleAtoms,NatArrayLanguage.sequence,Program.arrayWrites,Atom.arrayWrites])
  have scalars (r : Reg) (h₁ : r≠.quotient) (h₂ : r≠.first) (h₃ : r≠.second) (h₄ : r≠.third) :
      U.scalar r=S.scalar r := run.scalar_eq_of_not_mem r (by
    simp [decodeTriple,atoms,decodeTripleAtoms,NatArrayLanguage.sequence,Program.scalarWrites,Atom.scalarWrites,
      h₁,h₂,h₃,h₄])
  obtain ⟨T,rest,hT,hresult⟩ := tripleBody_runs mul mul' a b
    (finFunctionFinEquiv.symm z 0) (finFunctionFinEquiv.symm z 1) (finFunctionFinEquiv.symm z 2)
    U B result hU (by simpa [arrays] using ht) (by simpa [arrays] using ht')
    (by simpa [arrays] using ha) (by simpa [arrays] using hb)
    ((scalars _ (by decide) (by decide) (by decide) (by decide)).trans hn)
    ((scalars _ (by decide) (by decide) (by decide) (by decide)).trans hm) hi hj hl
    ((scalars _ (by decide) (by decide) (by decide) (by decide)).trans hr) hr1 hroom hroom' h1
  exact ⟨T,Runs.seq run rest,hT,by simpa [testAt,z.isLt] using hresult⟩

private structure CompareInvariant {n m k : ℕ}
    (mul : Fin n → Fin n → Fin n) (mul' : Fin m → Fin m → Fin m)
    (a : Fin k → Fin n) (b : Fin k → Fin m) (B i : ℕ) (S : Store Reg Arr) : Prop where
  bounded : S.Bounded B
  index_eq : S.scalar .index=i
  todo_eq : S.scalar .todo=k^3-i
  one_eq : S.scalar .one=1
  left_eq : S.scalar .leftSize=n
  right_eq : S.scalar .rightSize=m
  arity_eq : S.scalar .arity=k
  result_eq : S.scalar .result=prefixTest mul mul' a b i
  table_eq : S.array .leftTable=tableWord mul
  table'_eq : S.array .rightTable=tableWord mul'
  tuple_eq : S.array .leftTuple=tupleWord a
  tuple'_eq : S.array .rightTuple=tupleWord b

def compareLoop : Code := countedLoop .index .todo .limit .one entryBody

theorem compareLoop_runs {n m k : ℕ}
    (mul : Fin n → Fin n → Fin n) (mul' : Fin m → Fin m → Fin m)
    (a : Fin k → Fin n) (b : Fin k → Fin m)
    (S : Store Reg Arr) (B : ℕ) (hS : S.Bounded B)
    (ht : S.array .leftTable=tableWord mul) (ht' : S.array .rightTable=tableWord mul')
    (ha : S.array .leftTuple=tupleWord a) (hb : S.array .rightTuple=tupleWord b)
    (hn : S.scalar .leftSize=n) (hm : S.scalar .rightSize=m)
    (hk : S.scalar .arity=k) (hlimit : S.scalar .limit=k^3)
    (hr : S.scalar .result=1) (hone : S.scalar .one=1)
    (hroom : n*n≤B) (hroom' : m*m≤B) (h1 : 1≤B) :
    ∃ t≤26*k^3+3,∃ T,Runs (storageBound Reg Arr B) compareLoop S t T ∧
      T.Bounded B ∧ T.scalar .result=prefixTest mul mul' a b (k^3) := by
  have hcube : k^3≤B := by simpa [hlimit] using hS.1 .limit
  let I := CompareInvariant mul mul' a b B
  have hcopy : (S.setScalar .todo (S.scalar .limit)).Bounded B := hS.setScalar _ (hS.1 _)
  have hstart : I 0 ((S.setScalar .todo (S.scalar .limit)).setScalar .index 0) := by
    refine ⟨hcopy.setScalar _ (Nat.zero_le _),?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simp
    · simp [hlimit]
    · simp [hone]
    · simp [hn]
    · simp [hm]
    · simp [hk]
    · simp [prefixTest,IndexedRefinement.boolNat,hr]
    · simpa using ht
    · simpa using ht'
    · simpa using ha
    · simpa using hb
  have hcontrol : ∀ i≤k^3,∀ U,I i U → U.scalar .index=i ∧ U.scalar .todo=k^3-i ∧
      U.scalar .one=1 ∧ U.size≤storageBound Reg Arr B := by
    intro i hi U hU
    exact ⟨hU.index_eq,hU.todo_eq,hU.one_eq,Store.size_le_of_bounded hU.bounded⟩
  have hstep : ∀ i<k^3,∀ U,I i U → ∃ t≤23,∃ V,
      Runs (storageBound Reg Arr B) entryBody U t V ∧
      V.scalar .index=i ∧ V.scalar .todo=k^3-i ∧ V.scalar .one=1 ∧
      (V.setScalar .index (i+1)).size≤storageBound Reg Arr B ∧ I (i+1) (advance .index .todo V) := by
    intro i hi U hU
    obtain ⟨V,run,hV,hresult⟩ := entryBody_runs mul mul' a b ⟨i,hi⟩ U B
      (prefixTest mul mul' a b i) hU.bounded hU.table_eq hU.table'_eq hU.tuple_eq hU.tuple'_eq
      hU.left_eq hU.right_eq hU.arity_eq hU.index_eq hU.result_eq
      (prefixTest_le ..) hroom hroom' h1
    have frames (r : Reg) (h : r∈({.index,.todo,.one,.leftSize,.rightSize,.arity} : Finset Reg)) :
        V.scalar r=U.scalar r := by
      apply run.scalar_eq_of_not_mem
      cases r <;> simp_all [entryBody,decodeTriple,tripleBody,atoms,decodeTripleAtoms,tripleAtoms,
        NatArrayLanguage.sequence,Program.scalarWrites,Atom.scalarWrites]
    have arrays (ar : Arr) : V.array ar=U.array ar := run.array_eq_of_not_mem ar (by
      simp [entryBody,decodeTriple,tripleBody,atoms,decodeTripleAtoms,tripleAtoms,
        NatArrayLanguage.sequence,Program.arrayWrites,Atom.arrayWrites])
    have hvi : V.scalar .index=i := (frames _ (by simp)).trans hU.index_eq
    have hvrem : V.scalar .todo=k^3-i := (frames _ (by simp)).trans hU.todo_eq
    have hvone : V.scalar .one=1 := (frames _ (by simp)).trans hU.one_eq
    have hmid := hV.setScalar Reg.index (show i+1≤B by omega)
    refine ⟨23,le_rfl,V,run,hvi,hvrem,hvone,Store.size_le_of_bounded hmid,?_⟩
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [advance,hvi] using hmid.setScalar Reg.todo (show V.scalar .todo-1≤B by rw [hvrem]; omega)
    · simp [advance,hvi]
    · simp [advance,hvrem]; omega
    · simpa [advance] using hvone
    · simpa [advance] using (frames _ (by simp)).trans hU.left_eq
    · simpa [advance] using (frames _ (by simp)).trans hU.right_eq
    · simpa [advance] using (frames _ (by simp)).trans hU.arity_eq
    · simpa [advance,prefixTest_succ] using hresult
    · simpa [advance,arrays] using hU.table_eq
    · simpa [advance,arrays] using hU.table'_eq
    · simpa [advance,arrays] using hU.tuple_eq
    · simpa [advance,arrays] using hU.tuple'_eq
  obtain ⟨t,htt,T,run,hT⟩ := countedLoop_runs (storageBound Reg Arr B)
    .index .todo .limit .one entryBody (k^3) 23 I S
    (Store.size_le_of_bounded hS) (Store.size_le_of_bounded hcopy) hstart hcontrol
    (by decide) (by decide) hstep
  exact ⟨t,by omega,T,run,hT.bounded,hT.result_eq⟩

def comparePrelude : List (Atom Reg Arr) := [
  .const .one 1,.const .result 1,.binary .mul .limit .arity .arity,
  .binary .mul .limit .limit .arity]

def compareTuples : Code := .seq (atoms comparePrelude) compareLoop

theorem compareTuples_runs {n m k : ℕ}
    (mul : Fin n → Fin n → Fin n) (mul' : Fin m → Fin m → Fin m)
    (a : Fin k → Fin n) (b : Fin k → Fin m)
    (S : Store Reg Arr) (B : ℕ) (hS : S.Bounded B)
    (ht : S.array .leftTable=tableWord mul) (ht' : S.array .rightTable=tableWord mul')
    (ha : S.array .leftTuple=tupleWord a) (hb : S.array .rightTuple=tupleWord b)
    (hn : S.scalar .leftSize=n) (hm : S.scalar .rightSize=m) (hk : S.scalar .arity=k)
    (hroom : n*n≤B) (hroom' : m*m≤B) (hcube : k^3≤B) (h1 : 1≤B) :
    ∃ t≤26*k^3+7,∃ T,Runs (storageBound Reg Arr B) compareTuples S t T ∧
      T.Bounded B ∧ T.scalar .result≤1 ∧
        (T.scalar .result=1 ↔ signature mul a=signature mul' b) := by
  have hsq : k*k≤B := by
    cases k with
    | zero => simp
    | succ k =>
      calc
        (k+1)*(k+1) ≤ (k+1)^3 := by nlinarith
        _ ≤ B := hcube
  have hvalid : ValidAtoms B comparePrelude S := by
    simp only [comparePrelude,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,Function.update_apply,reduceCtorEq,if_true,if_false,hk]
    refine ⟨trivial,h1,trivial,h1,trivial,hsq,trivial,?_,trivial⟩
    simpa [pow_succ,pow_two] using hcube
  obtain ⟨first,hA⟩ := atoms_runs hS comparePrelude hvalid
  let A := applyAtoms comparePrelude S
  have harray (ar : Arr) : A.array ar=S.array ar := rfl
  have hscalar (r : Reg) (hr : r≠.one) (hr' : r≠.result) (hr'' : r≠.limit) : A.scalar r=S.scalar r := by
    simp [A,applyAtoms,comparePrelude,Atom.apply,Store.setScalar,hr,hr',hr'']
  have hlim : A.scalar .limit=k^3 := by
    simp [A,applyAtoms,comparePrelude,Atom.apply,BinaryOp.eval,Store.setScalar,hk,pow_succ,pow_two]
  obtain ⟨t,htt,T,rest,hT,heq⟩ := compareLoop_runs mul mul' a b A B hA
    (by simpa [harray] using ht) (by simpa [harray] using ht')
    (by simpa [harray] using ha) (by simpa [harray] using hb)
    ((hscalar _ (by decide) (by decide) (by decide)).trans hn)
    ((hscalar _ (by decide) (by decide) (by decide)).trans hm)
    ((hscalar _ (by decide) (by decide) (by decide)).trans hk) hlim
    (by simp [A,applyAtoms,comparePrelude,Atom.apply,Store.setScalar])
    (by simp [A,applyAtoms,comparePrelude,Atom.apply,Store.setScalar]) hroom hroom' h1
  exact ⟨4+t,by omega,T,Runs.seq first rest,hT,by rw [heq]; exact prefixTest_le ..,
    by rw [heq,prefixTest_correct]⟩

def encodedMul {G : Type*} [Mul G] {n : ℕ} (e : G ≃ Fin n) : Fin n → Fin n → Fin n :=
  fun a b => e (e.symm a*e.symm b)

theorem signature_encoded {G : Type*} [Group G] [DecidableEq G] {n k : ℕ}
    (e : G ≃ Fin n) (a : Fin k → G) :
    signature (encodedMul e) (e ∘ a)=FiniteWL.atomicI a := by
  apply Prod.ext
  · funext i j
    simp [signature,FiniteWL.atomicI,Function.comp_def,e.injective.eq_iff]
  · funext i j l
    simp [signature,FiniteWL.atomicI,encodedMul,Function.comp_def,e.injective.eq_iff]

theorem compareGroupTuples_runs {G H : Type*} [Group G] [Group H] [DecidableEq G] [DecidableEq H]
    {n m k : ℕ} (e : G ≃ Fin n) (e' : H ≃ Fin m) (a : Fin k → G) (b : Fin k → H)
    (S : Store Reg Arr) (B : ℕ) (hS : S.Bounded B)
    (ht : S.array .leftTable=tableWord (encodedMul e))
    (ht' : S.array .rightTable=tableWord (encodedMul e'))
    (ha : S.array .leftTuple=tupleWord (e ∘ a)) (hb : S.array .rightTuple=tupleWord (e' ∘ b))
    (hn : S.scalar .leftSize=n) (hm : S.scalar .rightSize=m) (hk : S.scalar .arity=k)
    (hroom : n*n≤B) (hroom' : m*m≤B) (hcube : k^3≤B) (h1 : 1≤B) :
    ∃ t≤26*k^3+7,∃ T,Runs (storageBound Reg Arr B) compareTuples S t T ∧
      T.Bounded B ∧ T.scalar .result≤1 ∧
        (T.scalar .result=1 ↔ FiniteWL.atomicI a=FiniteWL.atomicI b) := by
  simpa only [signature_encoded] using compareTuples_runs (encodedMul e) (encodedMul e')
    (e ∘ a) (e' ∘ b) S B hS ht ht' ha hb hn hm hk hroom hroom' hcube h1

end GroupWL.MachinePrograms.GroupInitial
