import GroupWL.MachinePrograms.GraphInitial
import GroupWL.MachinePrograms.IndexedWLDecode
import GroupWL.MachinePrograms.NatArrayComponents
import GroupWL.IndexedTuples

/-! Concrete assembly of the initial pair-comparison matrix. Group tables
and tuple decoders occupy disjoint finite register components. -/
namespace GroupWL.MachinePrograms.GraphMatrixPrograms
open NatArrayLanguage
open GroupWL.IndexedRefinement
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

abbrev Reg := GraphInitial.Reg ⊕ IndexedWL.Reg
abbrev Arr := GraphInitial.Arr ⊕ IndexedWL.Arr
abbrev Code := Program Reg Arr

def indexReg (right : Bool) : Reg := .inr (if right then .column else .row)
def sizeReg (right : Bool) : Reg := .inl (if right then .rightSize else .leftSize)
def tableArr (right : Bool) : Arr := .inl (if right then .rightTable else .leftTable)
def tupleArr (right : Bool) : Arr := .inl (if right then .rightTuple else .leftTuple)
def sourceSize (second : Bool) : Reg := .inr (if second then .rightCount else .leftCount)
def sourceTable (second : Bool) : Arr := .inr (if second then .targets else .fanouts)

def selectBase (n m : ℕ) (second : Bool) : ℕ := if second then m else n
def selectCode (cutoff index : ℕ) (second : Bool) : ℕ := if second then index-cutoff else index
def selectTable (left right : List ℕ) (second : Bool) : List ℕ := if second then right else left

def configAtoms (right second : Bool) : List (Atom Reg Arr) := [
  if second then .binary .sub (.inr .value) (indexReg right) (.inr .vectorLimit)
    else .copy (.inr .value) (indexReg right),
  .copy (.inr .n) (sourceSize second),
  .copy (sizeReg right) (sourceSize second),
  .copyArray (tableArr right) (sourceTable second)]

def decode : Code := IndexedWL.decodeVector.map Sum.inr Sum.inr

def loadTuple (right : Bool) : Code := NatArrayLanguage.sequence [
  .atom (.binary .lt (.inr .flag) (indexReg right) (.inr .vectorLimit)),
  .branch (.inr .flag) (atoms (configAtoms right false)) (atoms (configAtoms right true)),
  decode,
  .atom (.copyArray (tupleArr right) (.inr .vector))]

theorem config_runs (right second : Bool) (S : Store Reg Arr) (B n m cutoff index : ℕ)
    (hS : S.Bounded B) (hn : S.scalar (.inr .leftCount)=n) (hm : S.scalar (.inr .rightCount)=m)
    (hcut : S.scalar (.inr .vectorLimit)=cutoff) (hi : S.scalar (indexReg right)=index)
    (leftTable rightTable : List ℕ)
    (ht : S.array (.inr .fanouts)=leftTable) (ht' : S.array (.inr .targets)=rightTable) :
    ∃T,Runs (storageBound Reg Arr B) (atoms (configAtoms right second)) S 4 T ∧
      T.Bounded B ∧ T.scalar (.inr .n)=selectBase n m second ∧
      T.scalar (.inr .value)=selectCode cutoff index second ∧
      T.scalar (sizeReg right)=selectBase n m second ∧
      T.array (tableArr right)=selectTable leftTable rightTable second := by
  have hindex : index≤B := by simpa [hi] using hS.1 (indexReg right)
  have valid : ValidAtoms B (configAtoms right second) S := by
    cases second <;> simp [configAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,BinaryOp.eval,hi,hcut]
    omega
  obtain ⟨run,hT⟩ := atoms_runs hS (configAtoms right second) valid
  refine ⟨applyAtoms (configAtoms right second) S,?_,hT,?_,?_,?_,?_⟩
  · simpa [configAtoms] using run
  all_goals
    cases right <;> cases second <;>
      simp [applyAtoms,configAtoms,indexReg,sizeReg,tableArr,sourceSize,sourceTable,
        selectBase,selectCode,selectTable,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,
        hn,hm,hcut,ht,ht'] at hi ⊢
    all_goals simp_all


theorem loadTuple_runs (right : Bool) (S : Store Reg Arr) (B n m k cutoff index : ℕ)
    (hS : S.Bounded B) (hn : S.scalar (.inr .leftCount)=n) (hm : S.scalar (.inr .rightCount)=m)
    (hcut : S.scalar (.inr .vectorLimit)=cutoff) (hi : S.scalar (indexReg right)=index)
    (hk : S.scalar (.inr .arity)=k) (hone : S.scalar (.inr .one)=1)
    (hlen : (S.array (.inr .vector)).length=k) (hnpos : 0<n) (hmpos : 0<m) (h1 : 1≤B)
    (leftTable rightTable : List ℕ)
    (ht : S.array (.inr .fanouts)=leftTable) (ht' : S.array (.inr .targets)=rightTable) :
    ∃t≤6*k+11,∃T,Runs (storageBound Reg Arr B) (loadTuple right) S t T ∧ T.Bounded B ∧
      T.scalar (sizeReg right)=selectBase n m (Decidable.decide (cutoff ≤ index)) ∧
      T.array (tableArr right)=selectTable leftTable rightTable (Decidable.decide (cutoff ≤ index)) ∧
      T.array (tupleArr right)=vectorWord (selectBase n m (Decidable.decide (cutoff ≤ index))) k
        (selectCode cutoff index (Decidable.decide (cutoff ≤ index))) ∧
      (T.array (.inr .vector)).length=k := by
  let second := Decidable.decide (cutoff ≤ index)
  let flagAtom : Atom Reg Arr := .binary .lt (.inr .flag) (indexReg right) (.inr .vectorLimit)
  have smallFlag : flagAtom.SmallResult B S := by
    change (if S.scalar (indexReg right)<S.scalar (.inr .vectorLimit) then 1 else 0)≤B
    split <;> omega
  have first := atom_runs hS flagAtom trivial smallFlag
  have hU := Atom.apply_bounded hS flagAtom smallFlag
  let U := flagAtom.apply S
  have scalarU (r : Reg) (hr : r≠.inr .flag) : U.scalar r=S.scalar r := by
    simp [U,flagAtom,Atom.apply,hr]
  have hiU : U.scalar (indexReg right)=index := by
    rw [scalarU (indexReg right) (by cases right <;> decide),hi]
  obtain ⟨V,config,hV,baseV,codeV,sizeV,tableV⟩ := config_runs right second U B n m cutoff index hU
    (by rw [scalarU _ (by decide),hn]) (by rw [scalarU _ (by decide),hm])
    (by rw [scalarU _ (by decide),hcut]) hiU leftTable rightTable
    (by simpa [U,Atom.apply,flagAtom] using ht) (by simpa [U,Atom.apply,flagAtom] using ht')
  have flagU : U.scalar (.inr .flag)=(if index<cutoff then 1 else 0) := by
    simp [U,flagAtom,Atom.apply,BinaryOp.eval,hi,hcut]
  have choose : Runs (storageBound Reg Arr B)
      (.branch (.inr .flag) (atoms (configAtoms right false)) (atoms (configAtoms right true))) U 5 V := by
    by_cases hlt : index<cutoff
    · have hs : second=false := by simp [second,show ¬cutoff ≤ index by omega]
      have hvflag : U.scalar (.inr .flag)≠0 := by simp [flagU,hlt]
      simpa only [hs] using Runs.branch_nonzero (q := atoms (configAtoms right true)) hvflag config
    · have hs : second=true := by simp [second,show cutoff ≤ index by omega]
      have hvflag : U.scalar (.inr .flag)=0 := by simp [flagU,hlt]
      simpa only [hs] using Runs.branch_zero (p := atoms (configAtoms right false)) hvflag config
  have configScalar (r : Reg) (hr : r∉(atoms (configAtoms right second)).scalarWrites) :
      V.scalar r=U.scalar r := config.scalar_eq_of_not_mem r hr
  have arityV : V.scalar (.inr .arity)=k := by
    rw [configScalar _ (by cases right <;> cases second <;> decide),scalarU _ (by decide),hk]
  have oneV : V.scalar (.inr .one)=1 := by
    rw [configScalar _ (by cases right <;> cases second <;> decide),scalarU _ (by decide),hone]
  have lengthV : (V.array (.inr .vector)).length=k := by
    rw [config.array_eq_of_not_mem _ (by cases right <;> cases second <;> decide)]
    simpa [U,Atom.apply,flagAtom] using hlen
  have positive : 0<selectBase n m second := by cases second <;> simpa [selectBase] using (by assumption : 0<_)
  obtain ⟨td,htd,W,decoder,hW,vectorW⟩ := IndexedWL.decodeVector_runs V.right B (selectBase n m second) k
    (selectCode cutoff index second) hV.right baseV positive arityV codeV oneV lengthV
  have lifted := decoder.right_bounded hV
  let X := V.left.join W
  have hX : X.Bounded B := hV.left.join hW
  have last := atom_runs hX (.copyArray (tupleArr right) (.inr .vector)) trivial trivial
  have boundLast := Atom.apply_bounded hX (.copyArray (tupleArr right) (.inr .vector)) trivial
  let T := (Atom.copyArray (tupleArr right) (.inr .vector)).apply X
  refine ⟨1+(5+(td+(1+0))),by omega,T,?_,boundLast,?_,?_,?_,?_⟩
  · exact .seq first (.seq choose (.seq lifted (.seq last (.skip last.end_bound))))
  · simpa only [T,Atom.apply,Store.setArray_scalar,Store.join_scalar_left,sizeReg] using sizeV
  · have hne : tableArr right≠tupleArr right := by cases right <;> decide
    change (X.setArray (tupleArr right) (X.array (.inr .vector))).array (tableArr right)=_
    rw [Store.setArray_other X (tupleArr right) (tableArr right) _ hne]
    exact tableV
  · simp [T,Atom.apply,X,tupleArr,vectorW,second]
  · simp [T,Atom.apply,X,tupleArr,vectorW]



def selectMul {n m : ℕ} (mul : Fin n → Fin n → Bool) (mul' : Fin m → Fin m → Bool) :
    (second : Bool) → Fin (selectBase n m second) → Fin (selectBase n m second) → Bool
  | false => mul
  | true => mul'

theorem selectMul_tableWord {n m : ℕ} (mul : Fin n → Fin n → Bool) (mul' : Fin m → Fin m → Bool)
    (second : Bool) : GraphInitial.tableWord (selectMul mul mul' second)=
      selectTable (GraphInitial.tableWord mul) (GraphInitial.tableWord mul') second := by
  cases second <;> rfl

def pointCode {n m k : ℕ} (i : Fin (n^k+m^k)) :
    Fin ((selectBase n m (Decidable.decide (n^k ≤ i.val)))^k) :=
  ⟨selectCode (n^k) i.val (Decidable.decide (n^k ≤ i.val)),by
    have hi := i.isLt
    by_cases h : n^k ≤ i.val
    · simp [selectBase,selectCode,h]; omega
    · simpa [selectBase,selectCode,h] using Nat.lt_of_not_ge h⟩

def pointMul {n m k : ℕ} (mul : Fin n → Fin n → Bool) (mul' : Fin m → Fin m → Bool)
    (i : Fin (n^k+m^k)) := selectMul mul mul' (Decidable.decide (n^k ≤ i.val))

def pointSignature {n m k : ℕ} (mul : Fin n → Fin n → Bool) (mul' : Fin m → Fin m → Bool)
    (i : Fin (n^k+m^k)) :=
  GraphInitial.signature (pointMul mul mul' i) (finFunctionFinEquiv.symm (pointCode i))

theorem vectorWord_eq_tupleWord {n k : ℕ} (v : Fin (n^k)) :
    vectorWord n k v.val=GraphInitial.tupleWord (finFunctionFinEquiv.symm v) := rfl

def compare : Code := GraphInitial.compareTuples.map Sum.inl Sum.inl

def comparePair : Code := NatArrayLanguage.sequence [
  loadTuple false,loadTuple true,
  .atom (.copy (.inl .arity) (.inr .arity)),compare]

theorem comparePair_runs {n m k B : ℕ}
    (mul : Fin n → Fin n → Bool) (mul' : Fin m → Fin m → Bool)
    (i j : Fin (n^k+m^k)) (S : Store Reg Arr)
    (hS : S.Bounded B) (hn : S.scalar (.inr .leftCount)=n) (hm : S.scalar (.inr .rightCount)=m)
    (hcut : S.scalar (.inr .vectorLimit)=n^k)
    (hi : S.scalar (.inr .row)=i.val) (hj : S.scalar (.inr .column)=j.val)
    (hk : S.scalar (.inr .arity)=k) (hone : S.scalar (.inr .one)=1)
    (hlen : (S.array (.inr .vector)).length=k) (hnpos : 0<n) (hmpos : 0<m)
    (hroom : n*n≤B) (hroom' : m*m≤B) (hcube : k^3≤B) (h1 : 1≤B)
    (ht : S.array (.inr .fanouts)=GraphInitial.tableWord mul)
    (ht' : S.array (.inr .targets)=GraphInitial.tableWord mul') :
    ∃t≤26*k^3+12*k+30,∃T,Runs (storageBound Reg Arr B) comparePair S t T ∧ T.Bounded B ∧
      T.scalar (.inl .result)≤1 ∧
      (T.scalar (.inl .result)=1 ↔ pointSignature mul mul' i=pointSignature mul mul' j) ∧
      (T.array (.inr .vector)).length=k := by
  obtain ⟨tl,htl,U,rl,hU,sizeL,tableL,tupleL,lenU⟩ := loadTuple_runs false S B n m k (n^k) i.val
    hS hn hm hcut hi hk hone hlen hnpos hmpos h1 _ _ ht ht'
  have sfL (r : Reg) (h : r∉(loadTuple false).scalarWrites) : U.scalar r=S.scalar r :=
    rl.scalar_eq_of_not_mem r h
  have afL (a : Arr) (h : a∉(loadTuple false).arrayWrites) : U.array a=S.array a :=
    rl.array_eq_of_not_mem a h
  obtain ⟨tr,htr,V,rr,hV,sizeR,tableR,tupleR,lenV⟩ := loadTuple_runs true U B n m k (n^k) j.val
    hU (by rw [sfL _ (by decide),hn]) (by rw [sfL _ (by decide),hm])
    (by rw [sfL _ (by decide),hcut]) (by rw [sfL _ (by decide)]; exact hj)
    (by rw [sfL _ (by decide),hk]) (by rw [sfL _ (by decide),hone]) lenU hnpos hmpos h1 _ _
    (by rw [afL _ (by decide),ht]) (by rw [afL _ (by decide),ht'])
  have sfR (r : Reg) (h : r∉(loadTuple true).scalarWrites) : V.scalar r=U.scalar r :=
    rr.scalar_eq_of_not_mem r h
  have afR (a : Arr) (h : a∉(loadTuple true).arrayWrites) : V.array a=U.array a :=
    rr.array_eq_of_not_mem a h
  have copy := atom_runs hV (.copy (.inl .arity) (.inr .arity)) trivial trivial
  have hW := Atom.apply_bounded hV (.copy (.inl .arity) (.inr .arity)) trivial
  let W := (Atom.copy (Sum.inl GraphInitial.Reg.arity) (Sum.inr IndexedWL.Reg.arity)).apply V
  have sizeLW : W.left.scalar .leftSize=selectBase n m (Decidable.decide (n^k ≤ i.val)) := by
    change W.scalar (.inl .leftSize)=_
    simp only [W,Atom.apply,Store.setScalar,Function.update_apply,Sum.inl.injEq,reduceCtorEq,if_false]
    rw [sfR _ (by decide)]
    exact sizeL
  have sizeRW : W.left.scalar .rightSize=selectBase n m (Decidable.decide (n^k ≤ j.val)) := by
    change W.scalar (.inl .rightSize)=_
    simp only [W,Atom.apply,Store.setScalar,Function.update_apply,Sum.inl.injEq,reduceCtorEq,if_false]
    exact sizeR
  have arityW : W.left.scalar .arity=k := by
    change W.scalar (.inl .arity)=_
    simp only [W,Atom.apply,Store.setScalar_same]
    rw [sfR _ (by decide),sfL _ (by decide),hk]
  have tableLW : W.left.array .leftTable=GraphInitial.tableWord (pointMul mul mul' i) := by
    change V.array (.inl .leftTable)=_
    rw [afR _ (by decide)]
    simpa only [pointMul,selectMul_tableWord] using tableL
  have tableRW : W.left.array .rightTable=GraphInitial.tableWord (pointMul mul mul' j) := by
    simpa only [pointMul,selectMul_tableWord] using tableR
  have tupleLW : W.left.array .leftTuple=GraphInitial.tupleWord (finFunctionFinEquiv.symm (pointCode i)) := by
    change V.array (.inl .leftTuple)=_
    rw [afR _ (by decide),← vectorWord_eq_tupleWord]
    exact tupleL
  have tupleRW : W.left.array .rightTuple=GraphInitial.tupleWord (finFunctionFinEquiv.symm (pointCode j)) := by
    rw [← vectorWord_eq_tupleWord]
    exact tupleR
  have roomSelected (second : Bool) : selectBase n m second*selectBase n m second≤B := by
    cases second
    · exact hroom
    · exact hroom'
  obtain ⟨tc,htc,Z,rc,hZ,resultZ,correctZ⟩ := GraphInitial.compareTuples_runs
    (pointMul mul mul' i) (pointMul mul mul' j)
    (finFunctionFinEquiv.symm (pointCode i)) (finFunctionFinEquiv.symm (pointCode j))
    W.left B hW.left tableLW tableRW tupleLW tupleRW sizeLW sizeRW arityW
    (roomSelected _) (roomSelected _) hcube h1
  have lifted := rc.left_bounded hW
  let T := Z.join W.right
  refine ⟨tl+(tr+(1+(tc+0))),by omega,T,?_,hZ.join hW.right,resultZ,correctZ,?_⟩
  · exact .seq rl (.seq rr (.seq copy (.seq lifted (.skip lifted.end_bound))))
  · exact lenV


end GroupWL.MachinePrograms.GraphMatrixPrograms

