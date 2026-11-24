import GroupWL.MachinePrograms.IndexedWLRounds

/-! Initialization and complete execution of the compressed relation client. -/
namespace GroupWL.MachinePrograms.IndexedWL
open NatArrayLanguage GroupWL.IndexedRefinement
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

private structure PowerInvariant (n k m i : ℕ) (S : Store Reg Arr) : Prop where
  bounded : S.Bounded m
  index_eq : S.scalar .coordinate=i
  remaining_eq : S.scalar .coordinateTodo=k-i
  one_eq : S.scalar .one=1
  n_eq : S.scalar .n=n
  power_eq : S.scalar .vectorLimit=n^i

def powerBody : Code := atom (.binary .mul .vectorLimit .vectorLimit .n)
def powerLoop : Code := loop .coordinate .coordinateTodo .arity powerBody

theorem powerLoop_runs (S : Store Reg Arr) (n k m : ℕ)
    (hbound : S.Bounded m) (hn : S.scalar .n=n) (hk : S.scalar .arity=k)
    (hone : S.scalar .one=1) (hpower : S.scalar .vectorLimit=1)
    (hpos : 0<n) (hpowroom : n^k≤m) (hkroom : k≤m) :
    ∃t≤4*k+3,∃T,Runs (storageBound Reg Arr m) powerLoop S t T ∧
      T.Bounded m ∧ T.scalar .vectorLimit=n^k := by
  let I := PowerInvariant n k m
  have hcopy := hbound.setScalar Reg.coordinateTodo (show S.scalar .arity≤m by simpa [hk] using hkroom)
  have start : I 0 ((S.setScalar .coordinateTodo (S.scalar .arity)).setScalar .coordinate 0) := by
    refine ⟨hcopy.setScalar _ (Nat.zero_le _),?_,?_,?_,?_,?_⟩
    · simp
    · simp [hk]
    · simp [hone]
    · simp [hn]
    · simpa using hpower
  have control : ∀i≤k,∀T,I i T →
      T.scalar .coordinate=i ∧ T.scalar .coordinateTodo=k-i ∧ T.scalar .one=1 ∧
      T.size≤storageBound Reg Arr m := by
    intro i hi T hT
    exact ⟨hT.index_eq,hT.remaining_eq,hT.one_eq,Store.size_le_of_bounded hT.bounded⟩
  have step : ∀i<k,∀T,I i T → ∃t≤1,∃U,
      Runs (storageBound Reg Arr m) powerBody T t U ∧
      U.scalar .coordinate=i ∧ U.scalar .coordinateTodo=k-i ∧ U.scalar .one=1 ∧
      (U.setScalar .coordinate (i+1)).size≤storageBound Reg Arr m ∧
      I (i+1) (advance .coordinate .coordinateTodo U) := by
    intro i hi T hT
    have hp : n^(i+1)≤m := (Nat.pow_le_pow_right hpos (by omega)).trans hpowroom
    have small : (Atom.binary .mul .vectorLimit .vectorLimit .n).SmallResult m T := by
      simpa [Atom.SmallResult,BinaryOp.eval,hT.power_eq,hT.n_eq,pow_succ] using hp
    have run := atom_runs hT.bounded (.binary .mul .vectorLimit .vectorLimit .n) trivial small
    have boundU := Atom.apply_bounded hT.bounded (.binary .mul .vectorLimit .vectorLimit .n) small
    let U := (Atom.binary .mul .vectorLimit .vectorLimit .n).apply T
    have hiU : U.scalar .coordinate=i := by simp [U,Atom.apply,hT.index_eq]
    have hrU : U.scalar .coordinateTodo=k-i := by simp [U,Atom.apply,hT.remaining_eq]
    have h1U : U.scalar .one=1 := by simp [U,Atom.apply,hT.one_eq]
    have hnU : U.scalar .n=n := by simp [U,Atom.apply,hT.n_eq]
    have hpU : U.scalar .vectorLimit=n^(i+1) := by
      simp [U,Atom.apply,BinaryOp.eval,hT.power_eq,hT.n_eq,pow_succ]
    have mid := boundU.setScalar Reg.coordinate (show i+1≤m by omega)
    refine ⟨1,le_rfl,U,run,hiU,hrU,h1U,Store.size_le_of_bounded mid,?_⟩
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · simpa [advance,hiU] using mid.setScalar Reg.coordinateTodo (show U.scalar .coordinateTodo-1≤m by rw [hrU]; omega)
    · simp [advance,hiU]
    · simp [advance,hrU]; omega
    · simpa [advance] using h1U
    · simpa [advance] using hnU
    · simpa [advance] using hpU
  obtain ⟨t,ht,T,run,hT⟩ := countedLoop_runs (storageBound Reg Arr m) .coordinate .coordinateTodo .arity .one
    powerBody k 1 I S (Store.size_le_of_bounded hbound) (Store.size_le_of_bounded hcopy)
    start control (by decide) (by decide) step
  exact ⟨t,by omega,T,run,hT.bounded,hT.power_eq⟩

structure Input {n k b : ℕ} (D : Data n k b) (R : Finset (Fin n×Fin n))
    (m : ℕ) (S : Store Reg Arr) : Prop where
  bounded : S.Bounded m
  n_eq : S.scalar .n=n
  arity_eq : S.scalar .arity=k
  width_eq : S.scalar .width=b
  matrix_eq : S.array .matrix=matrixWord R
  fanouts_eq : S.array .fanouts=D.fanoutWord
  targets_eq : S.array .targets=D.targetWord

def initialAtoms : List (Atom Reg Arr) := [
  .const .zero 0,.const .one 1,.binary .mul .square .n .n,.const .vectorLimit 1]

def allocateAtoms : List (Atom Reg Arr) := [
  .allocate .vector .arity .zero,.allocate .nextMatrix .square .zero]

def setupStatements : List Code := initialAtoms.map .atom ++ [powerLoop] ++ allocateAtoms.map .atom
def setup : Code := NatArrayLanguage.sequence setupStatements

theorem setup_runs {n k b m : ℕ} (D : Data n k b) (R : Finset (Fin n×Fin n))
    (S : Store Reg Arr) (room : Room n k b m) (input : Input D R m S) :
    ∃t≤4*k+9,∃T,Runs (storageBound Reg Arr m) setup S t T ∧ Context D R m T ∧
      T.scalar .vectorLimit=n^k ∧ T.scalar .square=n*n ∧ (T.array .nextMatrix).length=n*n := by
  have valid : ValidAtoms m initialAtoms S := by
    simp [initialAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,input.n_eq,room.one,room.matrix]
  obtain ⟨init,hinit⟩ := atoms_runs input.bounded initialAtoms valid
  let U := applyAtoms initialAtoms S
  have initFrame (r : Reg) (hr : r∉(atoms initialAtoms).scalarWrites) :
      U.scalar r=S.scalar r := init.scalar_eq_of_not_mem r hr
  have hnU : U.scalar .n=n := by rw [initFrame .n (by decide),input.n_eq]
  have hkU : U.scalar .arity=k := by rw [initFrame .arity (by decide),input.arity_eq]
  have h1U : U.scalar .one=1 := by simp [U,applyAtoms,initialAtoms,Atom.apply,Store.setScalar]
  have hpU : U.scalar .vectorLimit=1 := by simp [U,applyAtoms,initialAtoms,Atom.apply,Store.setScalar]
  have hsqU : U.scalar .square=n*n := by
    simp [U,applyAtoms,initialAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,input.n_eq]
  obtain ⟨t,ht,V,run,hV,hpV⟩ := powerLoop_runs U n k m hinit hnU hkU h1U hpU D.positive room.vectors room.arity
  have validAlloc : ValidAtoms m allocateAtoms V := by simp [allocateAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult]
  obtain ⟨alloc,halloc⟩ := atoms_runs hV allocateAtoms validAlloc
  let T := applyAtoms allocateAtoms V
  have scalarFrame (r : Reg) (hri : r∉(atoms initialAtoms).scalarWrites) (hrp : r∉powerLoop.scalarWrites) :
      T.scalar r=S.scalar r := by
    rw [alloc.scalar_eq_of_not_mem r (by
      simp [atoms,allocateAtoms,NatArrayLanguage.sequence,Program.scalarWrites,Atom.scalarWrites]),
      run.scalar_eq_of_not_mem r hrp,initFrame r hri]
  have scalarAfter (r : Reg) (hrp : r∉powerLoop.scalarWrites) : T.scalar r=U.scalar r := by
    rw [alloc.scalar_eq_of_not_mem r (by
      simp [atoms,allocateAtoms,NatArrayLanguage.sequence,Program.scalarWrites,Atom.scalarWrites]),
      run.scalar_eq_of_not_mem r hrp]
  have arrays (a : Arr) (ha : a≠.vector) (ha' : a≠.nextMatrix) : T.array a=S.array a := by
    rw [alloc.array_eq_of_not_mem a (by
      simp [atoms,allocateAtoms,NatArrayLanguage.sequence,Program.arrayWrites,Atom.arrayWrites,ha,ha']),
      run.array_eq_of_not_mem a (by
        simp [powerLoop,powerBody,loop,atom,NatArrayLanguage.sequence,Program.arrayWrites,Atom.arrayWrites]),
      init.array_eq_of_not_mem a (by
        simp [atoms,initialAtoms,NatArrayLanguage.sequence,Program.arrayWrites,Atom.arrayWrites])]
  have hkV : V.scalar .arity=k := by rw [run.scalar_eq_of_not_mem .arity (by decide),hkU]
  have hsqV : V.scalar .square=n*n := by rw [run.scalar_eq_of_not_mem .square (by decide),hsqU]
  have hlenVec : (T.array .vector).length=k := by
    simp [T,applyAtoms,allocateAtoms,Atom.apply,Store.setArray,hkV]
  have hlenNext : (T.array .nextMatrix).length=n*n := by
    simp [T,applyAtoms,allocateAtoms,Atom.apply,Store.setArray,hsqV]
  have pRun : Runs (storageBound Reg Arr m) (NatArrayLanguage.sequence [powerLoop]) U (t+0) V :=
    .seq run (.skip run.end_bound)
  have first := sequence_append_runs (initialAtoms.map .atom) [powerLoop] init pRun
  have full := sequence_append_runs (initialAtoms.map .atom++[powerLoop]) (allocateAtoms.map .atom) first alloc
  refine ⟨4+t+2,by omega,T,?_,?_,?_,?_,hlenNext⟩
  · convert full using 1 <;> simp [setup,setupStatements,initialAtoms,allocateAtoms] <;> omega
  · refine ⟨halloc,?_,?_,?_,?_,?_,?_,?_,hlenVec⟩
    · rw [scalarFrame .n (by decide) (by decide)]; exact input.n_eq
    · rw [scalarFrame .arity (by decide) (by decide)]; exact input.arity_eq
    · rw [scalarFrame .width (by decide) (by decide)]; exact input.width_eq
    · rw [scalarAfter .one (by decide),h1U]
    · rw [arrays .matrix (by decide) (by decide)]; exact input.matrix_eq
    · rw [arrays .fanouts (by decide) (by decide)]; exact input.fanouts_eq
    · rw [arrays .targets (by decide) (by decide)]; exact input.targets_eq
  · rw [alloc.scalar_eq_of_not_mem .vectorLimit (by decide)]; exact hpV
  · rw [scalarAfter .square (by decide),hsqU]


def refinementCost (n k b : ℕ) : ℕ := 4*k+(n*n)*(roundCost n k b+3)+12

/-- Complete operational correctness of the materialized refinement phase. -/
theorem refinement_runs {n k b m : ℕ} (D : Data n k b) (initialEq : Fin n → Fin n → Bool)
    (S : Store Reg Arr) (room : Room n k b m)
    (input : Input D (CompressedRefinement.table D.edges initialEq 0) m S) :
    ∃t≤refinementCost n k b,∃T,Runs (storageBound Reg Arr m) refinement S t T ∧
      Context D (CompressedRefinement.table D.edges initialEq (n*n)) m T := by
  obtain ⟨ts,hts,U,rs,ctxU,limitU,squareU,nextU⟩ := setup_runs D _ S room input
  obtain ⟨tr,htr,T,rr,ctxT⟩ := refinementLoop_runs D initialEq U room ctxU limitU squareU nextU
  have rest : Runs (storageBound Reg Arr m)
      (NatArrayLanguage.sequence [loop .round .roundTodo .square round]) U (tr+0) T :=
    .seq rr (.skip rr.end_bound)
  have full := sequence_append_runs setupStatements [loop .round .roundTodo .square round] rs rest
  refine ⟨ts+tr,by unfold refinementCost; omega,T,?_,ctxT⟩
  convert full using 1 <;> simp [refinement,setupStatements,initialAtoms,allocateAtoms,powerLoop,powerBody,atom] <;> omega

def decisionCost (n k b left right : ℕ) : ℕ :=
  refinementCost n k b+n*(7*(left+right)+17)+4

/-- The complete indexed algorithm executes real arithmetic and array loops.
Its result agrees with the previously verified concrete matrix algorithm. -/
theorem decide_runs {n k b m : ℕ} (D : Data n k b) (initialEq : Fin n → Fin n → Bool)
    (S : Store Reg Arr) (room : Room n k b m)
    (input : Input D (CompressedRefinement.table D.edges initialEq 0) m S)
    (left right : List (Fin n))
    (hleft : S.array .leftSelection=left.map Fin.val)
    (hright : S.array .rightSelection=right.map Fin.val)
    (hlenL : left.length≤m) (hlenR : right.length≤m) :
    ∃t≤decisionCost n k b left.length right.length,∃T,
      Runs (storageBound Reg Arr m) decide S t T ∧ T.Bounded m ∧
      T.scalar .result=boolNat (IndexedRefinement.run D
        (matrixWord (CompressedRefinement.table D.edges initialEq 0))
        (left.map Fin.val) (right.map Fin.val)) := by
  obtain ⟨tr,htr,U,rr,ctxU⟩ := refinement_runs D initialEq S room input
  have leftU : U.array .leftSelection=left.map Fin.val := by
    rw [rr.array_eq_of_not_mem .leftSelection (by decide),hleft]
  have rightU : U.array .rightSelection=right.map Fin.val := by
    rw [rr.array_eq_of_not_mem .rightSelection (by decide),hright]
  obtain ⟨th,hth,T,rh,hT,heq⟩ := histogram_runs U n m _ left right ctxU.bounded ctxU.matrix_eq
    leftU rightU ctxU.n_eq ctxU.one_eq room.matrix room.one hlenL hlenR
  refine ⟨tr+th,by unfold decisionCost; omega,T,.seq rr rh,hT,?_⟩
  simpa only [IndexedRefinement.run,refine_correct] using heq

theorem decide_runs_correct {n k b m : ℕ} (D : Data n k b) {C : Type*} [DecidableEq C]
    (initial : Fin n → C) (initialEq : Fin n → Fin n → Bool)
    (heq : ∀ a c,initialEq a c=true ↔ initial a=initial c)
    (S : Store Reg Arr) (room : Room n k b m)
    (input : Input D (CompressedRefinement.table D.edges initialEq 0) m S)
    (left right : List (Fin n))
    (hleft : S.array .leftSelection=left.map Fin.val)
    (hright : S.array .rightSelection=right.map Fin.val)
    (hlenL : left.length≤m) (hlenR : right.length≤m) :
    ∃t≤decisionCost n k b left.length right.length,∃T,
      Runs (storageBound Reg Arr m) decide S t T ∧ T.Bounded m ∧
      (T.scalar .result≠0 ↔ ∀r,
        (left : Multiset (Fin n)).map (CompressedRefinement.labels D.edges initial r)=
          (right : Multiset (Fin n)).map (CompressedRefinement.labels D.edges initial r)) := by
  obtain ⟨t,ht,T,run,hT,hresult⟩ := decide_runs D initialEq S room input left right hleft hright hlenL hlenR
  refine ⟨t,ht,T,run,hT,?_⟩
  rw [hresult]
  have hbool (flag : Bool) : boolNat flag≠0 ↔ flag=true := by cases flag <;> simp [boolNat]
  rw [hbool,IndexedRefinement.run_correct D initial initialEq heq left right]


end GroupWL.MachinePrograms.IndexedWL

