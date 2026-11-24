import GroupWL.MachinePrograms.IndexedWLHistogram

/-! Counted replacement-vector matching in the concrete matrix algorithm. -/
namespace GroupWL.MachinePrograms.IndexedWL
open NatArrayLanguage
open GroupWL.IndexedRefinement
set_option maxRecDepth 2048
set_option linter.unusedSimpArgs false

def coordinateAtoms : List (Atom Reg Arr) := [
  .binary .add .targetIndex .slotBase .coordinate,
  .read .targetCode .targets .targetIndex,
  .read .digit .vector .coordinate,
  .binary .mul .matrixIndex .n .digit,
  .binary .add .matrixIndex .targetCode .matrixIndex,
  .read .temp .matrix .matrixIndex,
  .binary .mul .matched .matched .temp]

def coordinateBody : Code := atoms coordinateAtoms

theorem coordinateBody_runs {n k b : ℕ} (D : Data n k b)
    (R : Finset (Fin n×Fin n)) (a : Fin n) (x : Fin b) (v : Fin (n^k))
    (i : Fin k) (S : Store Reg Arr) (m matched : ℕ)
    (hbound : S.Bounded m) (hmatrix : S.array .matrix=matrixWord R)
    (htargets : S.array .targets=D.targetWord)
    (hvector : S.array .vector=vectorWord n k v.val)
    (hn : S.scalar .n=n) (hi : S.scalar .coordinate=i.val)
    (hbase : S.scalar .slotBase=k*(x.val+b*a.val))
    (hmatched : S.scalar .matched=matched) (hm : matched≤1)
    (hroom : n*n≤m) (htargetRoom : (n*b)*k≤m) (hone : 1≤m) :
    ∃ T,Runs (storageBound Reg Arr m) coordinateBody S 7 T ∧ T.Bounded m ∧
      T.scalar .matched=matched*boolNat (Decidable.decide (
        (finFunctionFinEquiv.symm v i,D.target a x i)∈R)) := by
  let d := finFunctionFinEquiv.symm v i
  let target := D.target a x i
  have hd : d.val<n := d.isLt
  have ht : target.val<n := target.isLt
  have hiTarget : i.val+k*(x.val+b*a.val)<(n*b)*k :=
    (finProdFinEquiv (finProdFinEquiv (a,x),i)).isLt
  have hiCell : target.val+n*d.val<n*n := (finProdFinEquiv (d,target)).isLt
  have hmul : n*d.val≤m := (Nat.mul_le_mul_left n (Nat.le_of_lt hd)).trans hroom
  have hbool : boolNat (Decidable.decide ((d,target)∈R))≤1 := by
    unfold boolNat; split <;> omega
  have hprod : matched*boolNat (Decidable.decide ((d,target)∈R))≤m :=
    (Nat.mul_le_mul hm hbool).trans (by simpa using hone)
  have hreadT : (D.targetWord)[k*(x.val+b*a.val)+i.val]?.getD 0=target.val := by
    simpa only [Nat.add_comm,IndexedRefinement.read] using D.targetWord_read a x i
  have hreadV : (vectorWord n k v.val)[i.val]?.getD 0=d.val := by
    simpa only [IndexedRefinement.read,digit_equiv] using vectorWord_read n k v.val i
  have hreadR : (matrixWord R)[target.val+n*d.val]?.getD 0=
      boolNat (Decidable.decide ((d,target)∈R)) := matrixWord_read R d target
  have hvalid : ValidAtoms m coordinateAtoms S := by
    simp only [coordinateAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,
      BinaryOp.eval,Store.setScalar,Function.update_apply]
    simp only [hn,hi,hbase,hmatched,htargets,hvector,hmatrix]
    simp only [reduceCtorEq,if_false,if_true]
    simp only [hreadT,hreadV,hreadR,Data.targetWord_length,vectorWord_length,matrixWord_length]
    exact ⟨trivial,by omega,by omega,trivial,i.isLt,trivial,trivial,hmul,
      trivial,(Nat.le_of_lt hiCell).trans hroom,hiCell,trivial,trivial,hprod,trivial⟩
  obtain ⟨run,hT⟩ := atoms_runs hbound coordinateAtoms hvalid
  refine ⟨applyAtoms coordinateAtoms S,run,hT,?_⟩
  simp only [applyAtoms,coordinateAtoms,List.foldl_cons,List.foldl_nil,Atom.apply,
    BinaryOp.eval,Store.setScalar,Function.update_apply]
  simp only [hn,hi,hbase,hmatched,htargets,hvector,hmatrix,reduceCtorEq,if_false,if_true]
  simp only [hreadT,hreadV,hreadR,d,target]


private def matchBit {n k b : ℕ} (D : Data n k b) (R : Finset (Fin n×Fin n))
    (a : Fin n) (x : Fin b) (v : Fin (n^k)) (i : ℕ) : Bool :=
  IndexedRefinement.read (matrixWord R)
    (IndexedRefinement.read D.targetWord (i+k*(x.val+b*a.val))+n*digit n v.val i)==1

private def matchPrefix {n k b : ℕ} (D : Data n k b) (R : Finset (Fin n×Fin n))
    (a : Fin n) (x : Fin b) (v : Fin (n^k)) (i : ℕ) : ℕ :=
  boolNat ((List.range i).all (matchBit D R a x v))

private theorem matchPrefix_le {n k b : ℕ} (D : Data n k b) (R : Finset (Fin n×Fin n))
    (a : Fin n) (x : Fin b) (v : Fin (n^k)) (i : ℕ) : matchPrefix D R a x v i ≤ 1 := by
  unfold matchPrefix boolNat; split <;> omega

private theorem matchBit_eq {n k b : ℕ} (D : Data n k b) (R : Finset (Fin n×Fin n))
    (a : Fin n) (x : Fin b) (v : Fin (n^k)) (i : Fin k) :
    matchBit D R a x v i.val=
      Decidable.decide ((finFunctionFinEquiv.symm v i,D.target a x i)∈R) := by
  unfold matchBit
  rw [D.targetWord_read a x i,digit_equiv v i,matrixWord_read]
  cases h : Decidable.decide ((finFunctionFinEquiv.symm v i,D.target a x i)∈R) <;> simp [boolNat]

private theorem matchPrefix_succ {n k b : ℕ} (D : Data n k b) (R : Finset (Fin n×Fin n))
    (a : Fin n) (x : Fin b) (v : Fin (n^k)) (i : Fin k) :
    matchPrefix D R a x v (i.val+1)=matchPrefix D R a x v i.val *
      boolNat (Decidable.decide ((finFunctionFinEquiv.symm v i,D.target a x i)∈R)) := by
  unfold matchPrefix
  rw [List.range_succ]
  simp only [List.all_append,List.all_cons,List.all_nil,Bool.and_true,matchBit_eq]
  generalize (List.range i.val).all _ = flag
  generalize Decidable.decide ((finFunctionFinEquiv.symm v i,D.target a x i)∈R) = other
  cases flag <;> cases other <;> rfl

private structure CoordinateInvariant {n k b : ℕ} (D : Data n k b)
    (R : Finset (Fin n×Fin n)) (a : Fin n) (x : Fin b) (v : Fin (n^k))
    (m i : ℕ) (S : Store Reg Arr) : Prop where
  bounded : S.Bounded m
  index_eq : S.scalar .coordinate=i
  remaining_eq : S.scalar .coordinateTodo=k-i
  one_eq : S.scalar .one=1
  n_eq : S.scalar .n=n
  base_eq : S.scalar .slotBase=k*(x.val+b*a.val)
  matched_eq : S.scalar .matched=matchPrefix D R a x v i
  matrix_eq : S.array .matrix=matrixWord R
  targets_eq : S.array .targets=D.targetWord
  vector_eq : S.array .vector=vectorWord n k v.val

theorem coordinateLoop_runs {n k b : ℕ} (D : Data n k b)
    (R : Finset (Fin n×Fin n)) (a : Fin n) (x : Fin b) (v : Fin (n^k))
    (S : Store Reg Arr) (m : ℕ)
    (hbound : S.Bounded m) (hmatrix : S.array .matrix=matrixWord R)
    (htargets : S.array .targets=D.targetWord)
    (hvector : S.array .vector=vectorWord n k v.val)
    (hn : S.scalar .n=n) (hk : S.scalar .arity=k) (hone : S.scalar .one=1)
    (hbase : S.scalar .slotBase=k*(x.val+b*a.val)) (hmatched : S.scalar .matched=1)
    (hroom : n*n≤m) (htargetRoom : (n*b)*k≤m) (hkroom : k≤m) (hm : 1≤m) :
    ∃ t≤10*k+3,∃ T,
      Runs (storageBound Reg Arr m) (loop .coordinate .coordinateTodo .arity coordinateBody) S t T ∧
      T.Bounded m ∧ T.scalar .matched=boolNat (vectorMatches D (matrixWord R) a.val x.val v.val) := by
  let I := CoordinateInvariant D R a x v m
  have hcopy : (S.setScalar .coordinateTodo (S.scalar .arity)).Bounded m :=
    hbound.setScalar _ (by simpa [hk] using hkroom)
  have hstart : I 0 ((S.setScalar .coordinateTodo (S.scalar .arity)).setScalar .coordinate 0) := by
    refine ⟨hcopy.setScalar _ (Nat.zero_le _),?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simp
    · simp [hk]
    · simp [hone]
    · simp [hn]
    · simp [hbase]
    · simpa [matchPrefix,boolNat] using hmatched
    · simpa using hmatrix
    · simpa using htargets
    · simpa using hvector
  have control : ∀ i≤k,∀ T,I i T →
      T.scalar .coordinate=i ∧ T.scalar .coordinateTodo=k-i ∧
      T.scalar .one=1 ∧ T.size≤storageBound Reg Arr m := by
    intro i hi T hT
    exact ⟨hT.index_eq,hT.remaining_eq,hT.one_eq,Store.size_le_of_bounded hT.bounded⟩
  have step : ∀ i<k,∀ T,I i T →
      ∃ t≤7,∃ U,Runs (storageBound Reg Arr m) coordinateBody T t U ∧
        U.scalar .coordinate=i ∧ U.scalar .coordinateTodo=k-i ∧ U.scalar .one=1 ∧
        (U.setScalar .coordinate (i+1)).size≤storageBound Reg Arr m ∧
        I (i+1) (advance .coordinate .coordinateTodo U) := by
    intro i hi T hT
    obtain ⟨U,run,hU,heq⟩ := coordinateBody_runs D R a x v ⟨i,hi⟩ T m
      (matchPrefix D R a x v i) hT.bounded hT.matrix_eq hT.targets_eq hT.vector_eq hT.n_eq
      hT.index_eq hT.base_eq hT.matched_eq (matchPrefix_le D R a x v i) hroom htargetRoom hm
    have scalarFrame (r : Reg) (h : r∉coordinateBody.scalarWrites) :
        U.scalar r=T.scalar r := run.scalar_eq_of_not_mem r h
    have hiU : U.scalar .coordinate=i := by rw [scalarFrame .coordinate (by decide),hT.index_eq]
    have hrU : U.scalar .coordinateTodo=k-i := by rw [scalarFrame .coordinateTodo (by decide),hT.remaining_eq]
    have h1U : U.scalar .one=1 := by rw [scalarFrame .one (by decide),hT.one_eq]
    have hnU : U.scalar .n=n := by rw [scalarFrame .n (by decide),hT.n_eq]
    have hbU : U.scalar .slotBase=k*(x.val+b*a.val) := by rw [scalarFrame .slotBase (by decide),hT.base_eq]
    have arrays (a : Arr) : U.array a=T.array a := run.array_eq_of_not_mem a (by
      simp [coordinateBody,atoms,coordinateAtoms,NatArrayLanguage.sequence,
        Program.arrayWrites,Atom.arrayWrites])
    have hmid := hU.setScalar Reg.coordinate (show i+1≤m by omega)
    refine ⟨7,le_rfl,U,run,hiU,hrU,h1U,Store.size_le_of_bounded hmid,?_⟩
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [advance,hiU] using hmid.setScalar Reg.coordinateTodo
        (show U.scalar .coordinateTodo-1≤m by rw [hrU]; omega)
    · simp [advance,hiU]
    · simp [advance,hrU]; omega
    · simpa [advance] using h1U
    · simpa [advance] using hnU
    · simpa [advance] using hbU
    · rw [matchPrefix_succ D R a x v ⟨i,hi⟩]
      simpa [advance] using heq
    · simpa [advance,arrays] using hT.matrix_eq
    · simpa [advance,arrays] using hT.targets_eq
    · simpa [advance,arrays] using hT.vector_eq
  obtain ⟨t,ht,T,run,hT⟩ := countedLoop_runs (storageBound Reg Arr m) .coordinate .coordinateTodo
    .arity .one coordinateBody k 7 I S (Store.size_le_of_bounded hbound)
    (Store.size_le_of_bounded hcopy) hstart control (by decide) (by decide) step
  exact ⟨t,by omega,T,run,hT.bounded,hT.matched_eq⟩



private def slotPrelude : List (Atom Reg Arr) := [
  .const .matched 1, .binary .mul .slotBase .arity .slot,
  .binary .add .slotBase .rowBase .slotBase]

def slotBody (destination : Reg) : Code := NatArrayLanguage.sequence [
  atom (.const .matched 1),
  atom (.binary .mul .slotBase .arity .slot),
  atom (.binary .add .slotBase .rowBase .slotBase),
  loop .coordinate .coordinateTodo .arity coordinateBody,
  atom (.binary .add destination destination .matched)]

theorem slotBody_runs {n k b : ℕ} (D : Data n k b)
    (R : Finset (Fin n×Fin n)) (a : Fin n) (x : Fin b) (v : Fin (n^k))
    (destination : Reg) (hdestination : destination=.leftCount ∨ destination=.rightCount)
    (S : Store Reg Arr) (m accumulated : ℕ)
    (hbound : S.Bounded m) (hmatrix : S.array .matrix=matrixWord R)
    (htargets : S.array .targets=D.targetWord) (hvector : S.array .vector=vectorWord n k v.val)
    (hn : S.scalar .n=n) (hk : S.scalar .arity=k) (hone : S.scalar .one=1)
    (hx : S.scalar .slot=x.val) (hbase : S.scalar .rowBase=k*(b*a.val))
    (hdest : S.scalar destination=accumulated)
    (hroom : n*n≤m) (htargetRoom : (n*b)*k≤m) (hkroom : k≤m)
    (hm : 1≤m) (hacc : accumulated+1≤m) :
    ∃ t≤10*k+7,∃ T,Runs (storageBound Reg Arr m) (slotBody destination) S t T ∧
      T.Bounded m ∧ T.scalar destination=
        accumulated+boolNat (vectorMatches D (matrixWord R) a.val x.val v.val) := by
  have hslot : k*(x.val+b*a.val)≤m := by
    have hi := (finProdFinEquiv (a,x)).isLt
    calc
      _ ≤ k*(n*b) := Nat.mul_le_mul_left k (Nat.le_of_lt hi)
      _ = (n*b)*k := Nat.mul_comm _ _
      _ ≤ m := htargetRoom
  have hmul : k*x.val≤m :=
    (Nat.mul_le_mul_left k (Nat.le_add_right _ _)).trans hslot
  have hsum : k*(b*a.val)+k*x.val=k*(x.val+b*a.val) := by ring
  have hvalid : ValidAtoms m slotPrelude S := by
    simp [slotPrelude,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,hk,hx,hbase,hm,hmul,hsum,hslot]
  obtain ⟨pre,hpre⟩ := atoms_runs hbound slotPrelude hvalid
  let U := applyAtoms slotPrelude S
  have frame (r : Reg) (hr : r≠.matched) (hs : r≠.slotBase) : U.scalar r=S.scalar r := by
    apply pre.scalar_eq_of_not_mem
    simp [atoms,slotPrelude,NatArrayLanguage.sequence,Program.scalarWrites,Atom.scalarWrites,hr,hs]
  have arrays (a : Arr) : U.array a=S.array a := by
    apply pre.array_eq_of_not_mem
    simp [atoms,slotPrelude,NatArrayLanguage.sequence,Program.arrayWrites,Atom.arrayWrites]
  have hbaseU : U.scalar .slotBase=k*(x.val+b*a.val) := by
    simp [U,applyAtoms,slotPrelude,Atom.apply,BinaryOp.eval,Store.setScalar,hbase,hk,hx,hsum]
  have hmatchedU : U.scalar .matched=1 := by
    simp [U,applyAtoms,slotPrelude,Atom.apply,Store.setScalar]
  obtain ⟨t,ht,V,run,hV,heq⟩ := coordinateLoop_runs D R a x v U m hpre
    (by simpa [arrays] using hmatrix) (by simpa [arrays] using htargets)
    (by simpa [arrays] using hvector)
    (by rw [frame .n (by decide) (by decide)]; exact hn)
    (by rw [frame .arity (by decide) (by decide)]; exact hk)
    (by rw [frame .one (by decide) (by decide)]; exact hone)
    hbaseU hmatchedU hroom htargetRoom hkroom hm
  have hdestV : V.scalar destination=accumulated := by
    rw [run.scalar_eq_of_not_mem destination (by
      rcases hdestination with rfl|rfl <;> decide)]
    rw [frame destination (by rcases hdestination with rfl|rfl <;> decide)
      (by rcases hdestination with rfl|rfl <;> decide)]
    exact hdest
  have hmatch : boolNat (vectorMatches D (matrixWord R) a.val x.val v.val)≤1 := by
    unfold boolNat; split <;> omega
  have hlast : (Atom.binary .add destination destination .matched).SmallResult m V := by
    change V.scalar destination+V.scalar .matched≤m
    rw [hdestV,heq]
    exact (Nat.add_le_add_left hmatch _).trans hacc
  have last := atom_runs hV (.binary .add destination destination .matched) trivial hlast
  have hlastB := Atom.apply_bounded hV (.binary .add destination destination .matched) hlast
  have rest : Runs (storageBound Reg Arr m) (NatArrayLanguage.sequence [
      loop .coordinate .coordinateTodo .arity coordinateBody,
      atom (.binary .add destination destination .matched)]) U (t+(1+0))
      ((Atom.binary .add destination destination .matched).apply V) :=
    .seq run (.seq last (.skip last.end_bound))
  have full := sequence_append_runs (slotPrelude.map .atom)
    [loop .coordinate .coordinateTodo .arity coordinateBody,
      atom (.binary .add destination destination .matched)] pre rest
  refine ⟨3+t+1,by omega,_,?_,hlastB,?_⟩
  · convert full using 1 <;> simp [slotBody,slotPrelude,atom] <;> omega
  · simp [Atom.apply,BinaryOp.eval,hdestV,heq]



private def slotPrefix {n k b : ℕ} (D : Data n k b) (R : Finset (Fin n×Fin n))
    (a : Fin n) (v : Fin (n^k)) (i : ℕ) : ℕ :=
  (List.range i).countP (fun x => vectorMatches D (matrixWord R) a.val x v.val)

private theorem slotPrefix_le {n k b : ℕ} (D : Data n k b) (R : Finset (Fin n×Fin n))
    (a : Fin n) (v : Fin (n^k)) (i : ℕ) : slotPrefix D R a v i ≤ i := by
  simpa [slotPrefix] using List.countP_le_length (p := fun x => vectorMatches D (matrixWord R) a.val x v.val)
    (l := List.range i)

private theorem slotPrefix_succ {n k b : ℕ} (D : Data n k b) (R : Finset (Fin n×Fin n))
    (a : Fin n) (v : Fin (n^k)) (i : ℕ) :
    slotPrefix D R a v (i+1)=slotPrefix D R a v i+
      boolNat (vectorMatches D (matrixWord R) a.val i v.val) := by
  simp [slotPrefix,List.range_succ,List.countP_append,boolNat]

private structure SlotInvariant {n k b : ℕ} (D : Data n k b)
    (R : Finset (Fin n×Fin n)) (a : Fin n) (v : Fin (n^k))
    (destination : Reg) (m i : ℕ) (S : Store Reg Arr) : Prop where
  bounded : S.Bounded m
  index_eq : S.scalar .slot=i
  remaining_eq : S.scalar .slotTodo=D.fanout a-i
  one_eq : S.scalar .one=1
  n_eq : S.scalar .n=n
  k_eq : S.scalar .arity=k
  base_eq : S.scalar .rowBase=k*(b*a.val)
  destination_eq : S.scalar destination=slotPrefix D R a v i
  matrix_eq : S.array .matrix=matrixWord R
  targets_eq : S.array .targets=D.targetWord
  vector_eq : S.array .vector=vectorWord n k v.val

theorem slotLoop_runs {n k b : ℕ} (D : Data n k b)
    (R : Finset (Fin n×Fin n)) (a : Fin n) (v : Fin (n^k))
    (destination : Reg) (hdestination : destination=.leftCount ∨ destination=.rightCount)
    (S : Store Reg Arr) (m : ℕ)
    (hbound : S.Bounded m) (hmatrix : S.array .matrix=matrixWord R)
    (htargets : S.array .targets=D.targetWord) (hvector : S.array .vector=vectorWord n k v.val)
    (hn : S.scalar .n=n) (hk : S.scalar .arity=k) (hone : S.scalar .one=1)
    (hfanout : S.scalar .fanout=D.fanout a) (hbase : S.scalar .rowBase=k*(b*a.val))
    (hdest : S.scalar destination=0)
    (hroom : n*n≤m) (htargetRoom : (n*b)*k≤m) (hkroom : k≤m) (hbroom : b≤m) (hm : 1≤m) :
    ∃ t≤b*(10*k+10)+3,∃ T,
      Runs (storageBound Reg Arr m) (loop .slot .slotTodo .fanout (slotBody destination)) S t T ∧
      T.Bounded m ∧ T.scalar destination=vectorCount D (matrixWord R) a.val v.val := by
  have hfroom : D.fanout a≤m := (D.fanout_le a).trans hbroom
  have hdi : destination≠Reg.slot := by rcases hdestination with rfl|rfl <;> decide
  have hdr : destination≠Reg.slotTodo := by rcases hdestination with rfl|rfl <;> decide
  let I := SlotInvariant D R a v destination m
  have hcopy : (S.setScalar .slotTodo (S.scalar .fanout)).Bounded m :=
    hbound.setScalar _ (by simpa [hfanout] using hfroom)
  have hstart : I 0 ((S.setScalar .slotTodo (S.scalar .fanout)).setScalar .slot 0) := by
    refine ⟨hcopy.setScalar _ (Nat.zero_le _),?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simp
    · simp [hfanout]
    · simp [hone]
    · simp [hn]
    · simp [hk]
    · simp [hbase]
    · simpa [slotPrefix,hdi,hdr] using hdest
    · simpa using hmatrix
    · simpa using htargets
    · simpa using hvector
  have control : ∀ i≤D.fanout a,∀ T,I i T →
      T.scalar .slot=i ∧ T.scalar .slotTodo=D.fanout a-i ∧
      T.scalar .one=1 ∧ T.size≤storageBound Reg Arr m := by
    intro i hi T hT
    exact ⟨hT.index_eq,hT.remaining_eq,hT.one_eq,Store.size_le_of_bounded hT.bounded⟩
  have step : ∀ i<D.fanout a,∀ T,I i T →
      ∃ t≤10*k+7,∃ U,Runs (storageBound Reg Arr m) (slotBody destination) T t U ∧
        U.scalar .slot=i ∧ U.scalar .slotTodo=D.fanout a-i ∧ U.scalar .one=1 ∧
        (U.setScalar .slot (i+1)).size≤storageBound Reg Arr m ∧
        I (i+1) (advance .slot .slotTodo U) := by
    intro i hi T hT
    let x : Fin b := ⟨i,lt_of_lt_of_le hi (D.fanout_le a)⟩
    have hacc : slotPrefix D R a v i+1≤m := by
      have := slotPrefix_le D R a v i
      omega
    obtain ⟨t,ht,U,run,hU,heq⟩ := slotBody_runs D R a x v destination hdestination T m
      (slotPrefix D R a v i) hT.bounded hT.matrix_eq hT.targets_eq hT.vector_eq hT.n_eq
      hT.k_eq hT.one_eq hT.index_eq hT.base_eq hT.destination_eq hroom htargetRoom hkroom hm hacc
    have scalarFrame (r : Reg) (h : r∉(slotBody destination).scalarWrites) :
        U.scalar r=T.scalar r := run.scalar_eq_of_not_mem r h
    have hiU : U.scalar .slot=i := by
      rw [scalarFrame .slot (by rcases hdestination with rfl|rfl <;> decide),hT.index_eq]
    have hrU : U.scalar .slotTodo=D.fanout a-i := by
      rw [scalarFrame .slotTodo (by rcases hdestination with rfl|rfl <;> decide),hT.remaining_eq]
    have h1U : U.scalar .one=1 := by
      rw [scalarFrame .one (by rcases hdestination with rfl|rfl <;> decide),hT.one_eq]
    have hnU : U.scalar .n=n := by
      rw [scalarFrame .n (by rcases hdestination with rfl|rfl <;> decide),hT.n_eq]
    have hkU : U.scalar .arity=k := by
      rw [scalarFrame .arity (by rcases hdestination with rfl|rfl <;> decide),hT.k_eq]
    have hbU : U.scalar .rowBase=k*(b*a.val) := by
      rw [scalarFrame .rowBase (by rcases hdestination with rfl|rfl <;> decide),hT.base_eq]
    have arrays (a : Arr) : U.array a=T.array a := run.array_eq_of_not_mem a (by
      simp [slotBody,coordinateBody,coordinateAtoms,loop,atom,atoms,NatArrayLanguage.sequence,
        Program.arrayWrites,Atom.arrayWrites])
    have hmid := hU.setScalar Reg.slot (show i+1≤m by omega)
    refine ⟨t,ht,U,run,hiU,hrU,h1U,Store.size_le_of_bounded hmid,?_⟩
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [advance,hiU] using hmid.setScalar Reg.slotTodo
        (show U.scalar .slotTodo-1≤m by rw [hrU]; omega)
    · simp [advance,hiU]
    · simp [advance,hrU]; omega
    · simpa [advance] using h1U
    · simpa [advance] using hnU
    · simpa [advance] using hkU
    · simpa [advance] using hbU
    · rw [slotPrefix_succ]
      simpa [advance,hdi,hdr] using heq
    · simpa [advance,arrays] using hT.matrix_eq
    · simpa [advance,arrays] using hT.targets_eq
    · simpa [advance,arrays] using hT.vector_eq
  obtain ⟨t,ht,T,run,hT⟩ := countedLoop_runs (storageBound Reg Arr m) .slot .slotTodo
    .fanout .one (slotBody destination) (D.fanout a) (10*k+7) I S
    (Store.size_le_of_bounded hbound) (Store.size_le_of_bounded hcopy)
    hstart control (by decide) (by decide) step
  refine ⟨t,?_,T,run,hT.bounded,?_⟩
  · have := Nat.mul_le_mul_right (10*k+10) (D.fanout_le a)
    nlinarith
  · simpa [slotPrefix,vectorCount,D.fanoutWord_read] using hT.destination_eq



private def countPrelude (rowReg destination : Reg) : List (Atom Reg Arr) := [
  .const destination 0, .read .fanout .fanouts rowReg,
  .binary .mul .rowBase .width rowReg, .binary .mul .rowBase .arity .rowBase]

theorem countAt_runs {n k b : ℕ} (D : Data n k b)
    (R : Finset (Fin n×Fin n)) (a : Fin n) (v : Fin (n^k))
    (rowReg destination : Reg)
    (hrowChoice : rowReg=.row ∨ rowReg=.column)
    (hdestination : destination=.leftCount ∨ destination=.rightCount)
    (S : Store Reg Arr) (m : ℕ)
    (hbound : S.Bounded m) (hmatrix : S.array .matrix=matrixWord R)
    (hfanouts : S.array .fanouts=D.fanoutWord) (htargets : S.array .targets=D.targetWord)
    (hvector : S.array .vector=vectorWord n k v.val)
    (hn : S.scalar .n=n) (hk : S.scalar .arity=k) (hb : S.scalar .width=b)
    (hone : S.scalar .one=1) (hrow : S.scalar rowReg=a.val)
    (hroom : n*n≤m) (htargetRoom : (n*b)*k≤m) (hpairRoom : n*b≤m)
    (hkroom : k≤m) (hbroom : b≤m) (hm : 1≤m) :
    ∃ t≤b*(10*k+10)+7,∃ T,
      Runs (storageBound Reg Arr m) (countAt rowReg destination) S t T ∧
      T.Bounded m ∧ T.scalar destination=vectorCount D (matrixWord R) a.val v.val := by
  have hrd : rowReg≠destination := by
    rcases hrowChoice with rfl|rfl <;> rcases hdestination with rfl|rfl <;> decide
  have hrf : rowReg≠Reg.fanout := by rcases hrowChoice with rfl|rfl <;> decide
  have hrr : rowReg≠Reg.rowBase := by rcases hrowChoice with rfl|rfl <;> decide
  have hd (r : Reg) (hr : r=.n ∨ r=.arity ∨ r=.width ∨ r=.one) : r≠destination := by
    rcases hdestination with rfl|rfl <;> rcases hr with rfl|rfl|rfl|rfl <;> decide
  have hmul : b*a.val≤m := by
    calc
      b*a.val ≤ b*n := Nat.mul_le_mul_left b (Nat.le_of_lt a.isLt)
      _ = n*b := Nat.mul_comm _ _
      _ ≤ m := hpairRoom
  have hmul' : k*(b*a.val)≤m := by
    calc
      _ ≤ k*(n*b) := Nat.mul_le_mul_left k (by nlinarith [Nat.le_of_lt a.isLt])
      _ = (n*b)*k := Nat.mul_comm _ _
      _ ≤ m := htargetRoom
  have hread : (D.fanoutWord)[a.val]?.getD 0=D.fanout a := D.fanoutWord_read a
  have hvalid : ValidAtoms m (countPrelude rowReg destination) S := by
    simp only [countPrelude,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,
      BinaryOp.eval,Store.setScalar,Function.update_apply]
    simp [hfanouts,hrow,hrd,hrf,hrr,hd .arity (by simp),hd .width (by simp),hk,hb,
      a.isLt,hmul,hmul']
  obtain ⟨pre,hpre⟩ := atoms_runs hbound (countPrelude rowReg destination) hvalid
  let U := applyAtoms (countPrelude rowReg destination) S
  have frame (r : Reg) (hr : r≠destination) (hf : r≠.fanout) (hb : r≠.rowBase) :
      U.scalar r=S.scalar r := by
    apply pre.scalar_eq_of_not_mem
    simp [atoms,countPrelude,NatArrayLanguage.sequence,Program.scalarWrites,Atom.scalarWrites,hr,hf,hb]
  have arrays (a : Arr) : U.array a=S.array a := by
    apply pre.array_eq_of_not_mem
    simp [atoms,countPrelude,NatArrayLanguage.sequence,Program.arrayWrites,Atom.arrayWrites]
  have hfanoutU : U.scalar .fanout=D.fanout a := by
    simp [U,applyAtoms,countPrelude,Atom.apply,Store.setScalar,hrd,hrow,hfanouts,hread,Data.fanoutWord]
  have hbaseU : U.scalar .rowBase=k*(b*a.val) := by
    simp [U,applyAtoms,countPrelude,Atom.apply,BinaryOp.eval,Store.setScalar,
      hrd,hrf,hrow,hd .arity (by simp),hd .width (by simp),hk,hb]
  have hdestU : U.scalar destination=0 := by
    have hd₁ : destination≠Reg.fanout := by rcases hdestination with rfl|rfl <;> decide
    have hd₂ : destination≠Reg.rowBase := by rcases hdestination with rfl|rfl <;> decide
    simp [U,applyAtoms,countPrelude,Atom.apply,Store.setScalar,hd₁,hd₂]
  obtain ⟨t,ht,T,run,hT,heq⟩ := slotLoop_runs D R a v destination hdestination U m hpre
    (by simpa [arrays] using hmatrix) (by simpa [arrays] using htargets)
    (by simpa [arrays] using hvector)
    (by rw [frame .n (hd .n (by simp)) (by decide) (by decide)]; exact hn)
    (by rw [frame .arity (hd .arity (by simp)) (by decide) (by decide)]; exact hk)
    (by rw [frame .one (hd .one (by simp)) (by decide) (by decide)]; exact hone)
    hfanoutU hbaseU hdestU hroom htargetRoom hkroom hbroom hm
  have rest : Runs (storageBound Reg Arr m)
      (NatArrayLanguage.sequence [loop .slot .slotTodo .fanout (slotBody destination)]) U (t+0) T :=
    .seq run (.skip run.end_bound)
  have full := sequence_append_runs ((countPrelude rowReg destination).map .atom)
    [loop .slot .slotTodo .fanout (slotBody destination)] pre rest
  refine ⟨4+t,by omega,T,?_,hT,heq⟩
  convert full using 1 <;> simp [countAt,countPrelude,slotBody,coordinateBody,coordinateAtoms,atom,atoms] <;> omega


end GroupWL.MachinePrograms.IndexedWL

