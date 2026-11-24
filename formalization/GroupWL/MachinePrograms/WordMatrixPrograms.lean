import GroupWL.MachinePrograms.LoadTuplePair
import GroupWL.MachinePrograms.WordMatrixSemantics

/-! Concrete loading and complete-word-type comparison for one matrix cell. -/
namespace GroupWL.MachinePrograms.WordMatrixPrograms
open NatArrayLanguage
set_option maxRecDepth 8192
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false

abbrev Reg := InitialMatrixPrograms.Reg ⊕ WordTypeComparator.Reg
abbrev Arr := InitialMatrixPrograms.Arr ⊕ WordTypeComparator.Arr
abbrev State := Store Reg Arr
abbrev Code := NatArrayLanguage.Program Reg Arr

instance : DecidableEq Reg := inferInstance
instance : DecidableEq Arr := inferInstance
instance : Fintype Reg := inferInstance
instance : Fintype Arr := inferInstance

def base (r : GroupInitial.Reg) : Reg := .inl (.inl r)
def wl (r : IndexedWL.Reg) : Reg := .inl (.inr r)
def data (a : GroupInitial.Arr) : Arr := .inl (.inl a)
def array (a : IndexedWL.Arr) : Arr := .inl (.inr a)
def word (r : WordTypeComparator.Reg) : Reg := .inr r

def transfer : List (Atom Reg Arr) := [
  .copy (word (.inl 0)) (base .leftSize),.copy (word (.inl 1)) (base .rightSize),
  .copyArray (.inr (.inl 0)) (data .leftTable),.copyArray (.inr (.inl 1)) (data .rightTable),
  .copyArray (.inr WordTypeComparator.leftTuple) (data .leftTuple),
  .copyArray (.inr WordTypeComparator.rightTuple) (data .rightTuple),
  .const (word (WordTypeComparator.kernel 2)) 0,.const (word (WordTypeComparator.kernel 3)) 0]

def compareLoaded : Code := .seq (atoms transfer)
  (.seq (WordTypeComparator.program.map Sum.inr Sum.inr)
    (.atom (.copy (base .result) (word (WordTypeComparator.kernel 7)))))
def comparePair : Code := .seq (InitialMatrixPrograms.loadPair.map Sum.inl Sum.inl) compareLoaded

variable {G H : Type} [Group G] [Group H] [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H]
variable {n m k : ℕ}

theorem compareLoaded_runs (e : G≃Fin n) (e' : H≃Fin m)
    (f : Fin n→Fin n→Fin n) (g : Fin m→Fin m→Fin m)
    (hf : ∀x y,e.symm (f x y)=e.symm x*e.symm y)
    (hg : ∀x y,e'.symm (g x y)=e'.symm x*e'.symm y)
    (leftZero : (e 1).val=0) (rightZero : (e' 1).val=0)
    (a : Fin k→G) (b : Fin k→H) (S : State) (M : ℕ) (bounded : S.Bounded M)
    (leftOrder : S.scalar (base .leftSize)=n) (rightOrder : S.scalar (base .rightSize)=m)
    (leftTable : S.array (data .leftTable)=GroupInitial.tableWord f)
    (rightTable : S.array (data .rightTable)=GroupInitial.tableWord g)
    (leftData : S.array (data .leftTuple)=List.ofFn (fun i : Fin k=>(e (a i)).val))
    (rightData : S.array (data .rightTuple)=List.ofFn (fun i : Fin k=>(e' (b i)).val))
    (room : (n*m)*(n*m)≤M) :
    ∃t≤10*(n*m)^3+15*(n*m)^2+19*(n*m)+13*k+53,∃T,
      Runs (storageBound Reg Arr M) compareLoaded S t T ∧ T.Bounded M ∧
      T.scalar (base .result)≤1 ∧ (T.scalar (base .result)=1 ↔ FiniteWordTypes.sameWordType a b=true) := by
  obtain ⟨prepare,hV⟩ := atoms_runs bounded transfer (by simp [transfer,ValidAtoms,Atom.Valid,Atom.SmallResult])
  let V := applyAtoms transfer S
  have vn : V.right.scalar (.inl 0)=n := by
    simpa [V,applyAtoms,transfer,Atom.apply,Store.setScalar,Store.setArray,Store.right,word,base,data,
      WordTypeComparator.leftTuple,WordTypeComparator.rightTuple,WordTypeComparator.kernel,PairedTupleCompare.kernel] using leftOrder
  have vm : V.right.scalar (.inl 1)=m := by
    simpa [V,applyAtoms,transfer,Atom.apply,Store.setScalar,Store.setArray,Store.right,word,base,data,
      WordTypeComparator.leftTuple,WordTypeComparator.rightTuple,WordTypeComparator.kernel,PairedTupleCompare.kernel] using rightOrder
  have vl : V.right.array (.inl 0)=GroupInitial.tableWord f := by
    simpa [V,applyAtoms,transfer,Atom.apply,Store.setScalar,Store.setArray,Store.right,word,base,data,
      WordTypeComparator.leftTuple,WordTypeComparator.rightTuple] using leftTable
  have vr : V.right.array (.inl 1)=GroupInitial.tableWord g := by
    simpa [V,applyAtoms,transfer,Atom.apply,Store.setScalar,Store.setArray,Store.right,word,base,data,
      WordTypeComparator.leftTuple,WordTypeComparator.rightTuple] using rightTable
  have va : V.right.array WordTypeComparator.leftTuple=List.ofFn (fun i : Fin k=>(e (a i)).val) := by
    simpa [V,applyAtoms,transfer,Atom.apply,Store.setScalar,Store.setArray,Store.right,word,base,data,
      WordTypeComparator.leftTuple,WordTypeComparator.rightTuple] using leftData
  have vb : V.right.array WordTypeComparator.rightTuple=List.ofFn (fun i : Fin k=>(e' (b i)).val) := by
    simpa [V,applyAtoms,transfer,Atom.apply,Store.setScalar,Store.setArray,Store.right,word,base,data,
      WordTypeComparator.leftTuple,WordTypeComparator.rightTuple] using rightData
  have vi : V.right.scalar (WordTypeComparator.kernel 2)=(e 1).val := by
    simp [V,applyAtoms,transfer,Atom.apply,Store.setScalar,Store.setArray,Store.right,word,base,data,
      WordTypeComparator.kernel,PairedTupleCompare.kernel,leftZero]
  have vj : V.right.scalar (WordTypeComparator.kernel 3)=(e' 1).val := by
    simp [V,applyAtoms,transfer,Atom.apply,Store.setScalar,Store.setArray,Store.right,word,base,data,
      WordTypeComparator.kernel,PairedTupleCompare.kernel,rightZero]
  obtain ⟨t,ht,U,compare,hU,uvalid,result⟩ := WordTypeComparator.program_runs e e' f g hf hg a b V.right M
    hV.right vn vm vl vr va vb vi vj room
  let W := V.left.join U
  have hW : W.Bounded M := hV.left.join hU
  let copy : Atom Reg Arr := .copy (base .result) (word (WordTypeComparator.kernel 7))
  have last := atom_runs hW copy trivial trivial
  refine ⟨8+(t+1),by omega,copy.apply W,.seq prepare (.seq (compare.right_bounded hV) last),
    copy.apply_bounded hW trivial,uvalid,result⟩

end GroupWL.MachinePrograms.WordMatrixPrograms
