import GroupWL.MachinePrograms.PairedTupleCompare
import GroupWL.MachinePrograms.ProductGroupTable

/-! Version-II tuple comparison, including explicit product-table construction. -/
namespace GroupWL.MachinePrograms.WordTypeComparator
open NatArrayLanguage
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false

abbrev Reg := ProductGroupTable.Reg ⊕ PairedTupleCompare.Reg
abbrev Arr := ProductGroupTable.Arr ⊕ PairedTupleCompare.Arr
abbrev State := Store Reg Arr
abbrev Code := NatArrayLanguage.Program Reg Arr

def kernel (x : PairedKernelScan.Reg) : Reg := .inr (PairedTupleCompare.kernel x)
def leftTuple : Arr := .inr (.inl .left)
def rightTuple : Arr := .inr (.inl .right)

def transfer : List (Atom Reg Arr) := [
  .copy (.inr (.inl .cols)) (.inl 1),
  .binary .mul (kernel 0) (.inl 0) (.inl 1),.copy (kernel 1) (.inl 1),
  .copyArray (.inr PairedTupleCompare.table) (.inl 2)]

def program : Code := .seq (ProductGroupTable.generate.map Sum.inl Sum.inl)
  (.seq (atoms transfer) (PairedTupleCompare.program.map Sum.inr Sum.inr))

variable {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H]
variable {n m k : ℕ}

theorem program_runs (e : G≃Fin n) (e' : H≃Fin m)
    (f : Fin n→Fin n→Fin n) (g : Fin m→Fin m→Fin m)
    (hf : ∀x y,e.symm (f x y)=e.symm x*e.symm y)
    (hg : ∀x y,e'.symm (g x y)=e'.symm x*e'.symm y)
    (a : Fin k→G) (b : Fin k→H) (S : State) (M : ℕ) (bounded : S.Bounded M)
    (leftOrder : S.scalar (.inl 0)=n) (rightOrder : S.scalar (.inl 1)=m)
    (leftTable : S.array (.inl 0)=GroupInitial.tableWord f)
    (rightTable : S.array (.inl 1)=GroupInitial.tableWord g)
    (leftData : S.array leftTuple=List.ofFn (fun i : Fin k=>(e (a i)).val))
    (rightData : S.array rightTuple=List.ofFn (fun i : Fin k=>(e' (b i)).val))
    (leftOne : S.scalar (kernel 2)=(e 1).val) (rightOne : S.scalar (kernel 3)=(e' 1).val)
    (room : (n*m)*(n*m)≤M) :
    ∃t≤10*(n*m)^3+15*(n*m)^2+19*(n*m)+13*k+44,∃T,
      Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧
      T.scalar (kernel 7)≤1 ∧ (T.scalar (kernel 7)=1 ↔ FiniteWordTypes.sameWordType a b=true) := by
  have hn : 0<n := by have := (e 1).isLt;omega
  have hm : 0<m := by have := (e' 1).isLt;omega
  have hN := Nat.mul_pos hn hm
  have hNM : n*m≤M := by nlinarith
  obtain ⟨t,ht,U,build,hU,table⟩ := ProductGroupTable.generate_runs f g S.left M bounded.left
    leftOrder rightOrder leftTable rightTable hN room
  have un : U.scalar 0=n := (build.scalar_eq_of_not_mem _ (by decide +kernel)).trans leftOrder
  have um : U.scalar 1=m := (build.scalar_eq_of_not_mem _ (by decide +kernel)).trans rightOrder
  let V := U.join S.right
  have hV : V.Bounded M := hU.join bounded.right
  have vn : V.scalar (.inl 0)=n := un
  have vm : V.scalar (.inl 1)=m := um
  have valid : ValidAtoms M transfer V := by
    simp [transfer,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar,
      kernel,PairedTupleCompare.kernel,vn,vm,hNM]
  obtain ⟨transferRun,hW⟩ := atoms_runs hV transfer valid
  let W := applyAtoms transfer V
  have wm : W.right.scalar (.inl .cols)=m := by
    simp [W,applyAtoms,transfer,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,Store.right,
      kernel,PairedTupleCompare.kernel,vm]
  have wn : W.right.scalar (PairedTupleCompare.kernel 0)=n*m := by
    simp [W,applyAtoms,transfer,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,Store.right,
      kernel,PairedTupleCompare.kernel,vn,vm]
  have wr : W.right.scalar (PairedTupleCompare.kernel 1)=m := by
    simp [W,applyAtoms,transfer,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,Store.right,
      kernel,PairedTupleCompare.kernel,vm]
  have wtable : W.right.array PairedTupleCompare.table=GroupInitial.tableWord (ProductGroupTable.productOp f g) := by
    simpa [W,applyAtoms,transfer,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,Store.right,
      kernel,PairedTupleCompare.kernel,V] using table
  have wleft : W.right.array (.inl .left)=List.ofFn (fun i : Fin k=>(e (a i)).val) := by
    simpa [W,applyAtoms,transfer,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,Store.right,
      kernel,PairedTupleCompare.kernel,V,PairedTupleCompare.table,leftTuple] using leftData
  have wright : W.right.array (.inl .right)=List.ofFn (fun i : Fin k=>(e' (b i)).val) := by
    simpa [W,applyAtoms,transfer,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,Store.right,
      kernel,PairedTupleCompare.kernel,V,PairedTupleCompare.table,rightTuple] using rightData
  obtain ⟨u,hu,X,compare,hX,xvalid,result⟩ := PairedTupleCompare.program_runs e e' f g hf hg a b W.right M hW.right
    wm wleft wright wtable wn wr leftOne rightOne room
  refine ⟨t+(4+u),?_,W.left.join X,.seq (build.left_bounded bounded)
    (.seq transferRun (compare.right_bounded hW)),hW.left.join hX,xvalid,result⟩
  nlinarith

end GroupWL.MachinePrograms.WordTypeComparator
