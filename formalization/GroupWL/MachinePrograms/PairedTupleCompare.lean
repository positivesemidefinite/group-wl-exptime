import GroupWL.MachinePrograms.PairedClosureCheck
import GroupWL.MachinePrograms.PairedGenerators

/-! Compare the complete word types of two encoded tuples by finite loops. -/
namespace GroupWL.MachinePrograms.PairedTupleCompare
open NatArrayLanguage
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false

abbrev Reg := PairedGenerators.Reg ⊕ PairedClosureCheck.Reg
abbrev Arr := PairedGenerators.Arr ⊕ PairedClosureCheck.Arr
abbrev State := Store Reg Arr
abbrev Code := NatArrayLanguage.Program Reg Arr

def seed (x : GeneratorMask.Reg) : Reg := .inr (.inl (.inl x))
def closure (x : GroupSaturation.Reg) : Reg := .inr (.inl (.inr x))
def kernel (x : PairedKernelScan.Reg) : Reg := .inr (.inr x)
def table : Arr := .inr (.inl (.inr .table))
def generators : Arr := .inr (.inl (.inl .generators))

def transfer : List (Atom Reg Arr) := [
  .copy (seed .order) (kernel 0),.copy (closure .order) (kernel 0),
  .binary .mul (seed .identity) (kernel 2) (kernel 1),
  .binary .add (seed .identity) (seed .identity) (kernel 3),
  .copyArray generators (.inl .output)]

def program : Code := .seq (PairedGenerators.build.map Sum.inl Sum.inl)
  (.seq (atoms transfer) (PairedClosureCheck.program.map Sum.inr Sum.inr))

variable {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H]
variable {n m k : ℕ}

theorem program_runs (e : G≃Fin n) (e' : H≃Fin m)
    (f : Fin n→Fin n→Fin n) (g : Fin m→Fin m→Fin m)
    (hf : ∀x y,e.symm (f x y)=e.symm x*e.symm y)
    (hg : ∀x y,e'.symm (g x y)=e'.symm x*e'.symm y)
    (a : Fin k→G) (b : Fin k→H) (S : State) (M : ℕ) (bounded : S.Bounded M)
    (pairCols : S.scalar (.inl .cols)=m)
    (leftTuple : S.array (.inl .left)=List.ofFn (fun i : Fin k=>(e (a i)).val))
    (rightTuple : S.array (.inl .right)=List.ofFn (fun i : Fin k=>(e' (b i)).val))
    (tableEq : S.array table=GroupInitial.tableWord (ProductGroupTable.productOp f g))
    (scanOrder : S.scalar (kernel 0)=n*m) (rightOrder : S.scalar (kernel 1)=m)
    (leftOne : S.scalar (kernel 2)=(e 1).val) (rightOne : S.scalar (kernel 3)=(e' 1).val)
    (room : (n*m)*(n*m)≤M) :
    ∃t≤10*(n*m)^3+19*(n*m)+13*k+32,∃T,
      Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧
      T.scalar (kernel 7)≤1 ∧ (T.scalar (kernel 7)=1 ↔ FiniteWordTypes.sameWordType a b=true) := by
  have hn : 0<n := by have := (e 1).isLt;omega
  have hm : 0<m := by have := (e' 1).isLt;omega
  have hN := Nat.mul_pos hn hm
  have hNM : n*m≤M := by nlinarith
  have hM : 1≤M := by omega
  obtain ⟨t,ht,U,pair,hU,pairs⟩ := PairedGenerators.build_runs (e ∘ a) (e' ∘ b) S.left M
    bounded.left pairCols leftTuple rightTuple hNM hM
  let V := U.join S.right
  have hV : V.Bounded M := hU.join bounded.right
  have identitySmall : (e 1).val*m+(e' 1).val≤M := by
    have hh := (finProdFinEquiv (e 1,e' 1)).isLt
    change (e' 1).val+m*(e 1).val<n*m at hh
    nlinarith
  have valid : ValidAtoms M transfer V := by
    have l : V.scalar (kernel 2)=(e 1).val := leftOne
    have rr : V.scalar (kernel 3)=(e' 1).val := rightOne
    have m' : V.scalar (kernel 1)=m := rightOrder
    simp only [seed,kernel] at l rr m'
    simp [transfer,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,seed,closure,kernel,l,rr,m']
    exact ⟨by nlinarith,identitySmall⟩
  obtain ⟨copyRun,hW⟩ := atoms_runs hV transfer valid
  let W := applyAtoms transfer V
  have hseed : W.right.scalar (.inl (.inl .order))=n*m := by
    simpa [W,applyAtoms,transfer,Atom.apply,Store.setScalar,Store.setArray,Store.right,seed,closure,kernel,generators,V] using scanOrder
  have hid : W.right.scalar (.inl (.inl .identity))=(finProdFinEquiv (e 1,e' 1)).val := by
    have hl : V.scalar (kernel 2)=(e 1).val := leftOne
    have hr : V.scalar (kernel 3)=(e' 1).val := rightOne
    have hm' : V.scalar (kernel 1)=m := rightOrder
    simp only [kernel] at hl hr hm'
    simp [W,applyAtoms,transfer,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,Store.right,
      seed,closure,kernel,generators,hl,hr,hm',finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
  have hgens : W.right.array (.inl (.inl .generators))=
      List.ofFn (fun i : Fin k=>(finProdFinEquiv (e (a i),e' (b i))).val) := by
    simpa [W,applyAtoms,transfer,Atom.apply,Store.setScalar,Store.setArray,Store.right,
      seed,closure,kernel,generators,V,Function.comp_def] using pairs
  have horder : W.right.scalar (.inl (.inr .order))=n*m := by
    simpa [W,applyAtoms,transfer,Atom.apply,Store.setScalar,Store.setArray,Store.right,seed,closure,kernel,generators,V] using scanOrder
  have htable : W.right.array (.inl (.inr .table))=GroupInitial.tableWord (ProductGroupTable.productOp f g) := by
    simpa [W,applyAtoms,transfer,Atom.apply,Store.setScalar,Store.setArray,Store.right,
      seed,closure,kernel,generators,V,table] using tableEq
  obtain ⟨u,hu,X,check,hX,xvalid,result⟩ := PairedClosureCheck.program_runs e e' f g hf hg a b W.right M
    hW.right hseed hid hgens horder htable scanOrder rightOrder leftOne rightOne room
  refine ⟨t+(5+u),by omega,W.left.join X,.seq (pair.left_bounded bounded)
    (.seq copyRun (check.right_bounded hW)),hW.left.join hX,xvalid,result⟩

end GroupWL.MachinePrograms.PairedTupleCompare
