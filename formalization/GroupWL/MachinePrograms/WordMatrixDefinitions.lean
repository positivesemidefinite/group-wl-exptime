import GroupWL.MachinePrograms.WordMatrixPair
import GroupWL.MachinePrograms.ArrayTabulate
import GroupWL.MachinePrograms.NatArrayMapFrames

/-! Materialize the complete Version-II initial relation by actual tuple comparisons. -/
namespace GroupWL.MachinePrograms.WordMatrixPrograms
open NatArrayLanguage
open WordMatrixSemantics
open IndexedRefinement (boolNat matrixWord)
set_option maxRecDepth 8192
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

structure Context {n m k : ℕ} (f : Fin n→Fin n→Fin n) (g : Fin m→Fin m→Fin m) (S : State) : Prop where
  left_eq : S.scalar (wl .leftCount)=n
  right_eq : S.scalar (wl .rightCount)=m
  arity_eq : S.scalar (wl .arity)=k
  cutoff_eq : S.scalar (wl .vectorLimit)=n^k
  total_eq : S.scalar (wl .square)=n^k+m^k
  zero_eq : S.scalar (wl .zero)=0
  vector_length : (S.array (array .vector)).length=k
  left_table : S.array (array .fanouts)=GroupInitial.tableWord f
  right_table : S.array (array .targets)=GroupInitial.tableWord g

theorem Context.scalarUpdate {n m k : ℕ} {f : Fin n→Fin n→Fin n} {g : Fin m→Fin m→Fin m}
    {S : State} (ctx : Context (k:=k) f g S) (r : Reg) (x : ℕ)
    (hr : r∉({wl .leftCount,wl .rightCount,wl .arity,wl .vectorLimit,wl .square,wl .zero} : Finset Reg)) :
    Context (k:=k) f g (S.setScalar r x) := by
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hr
  refine ⟨?_,?_,?_,?_,?_,?_,ctx.vector_length,ctx.left_table,ctx.right_table⟩
  · simpa [Ne.symm hr.1] using ctx.left_eq
  · simpa [Ne.symm hr.2.1] using ctx.right_eq
  · simpa [Ne.symm hr.2.2.1] using ctx.arity_eq
  · simpa [Ne.symm hr.2.2.2.1] using ctx.cutoff_eq
  · simpa [Ne.symm hr.2.2.2.2.1] using ctx.total_eq
  · simpa [Ne.symm hr.2.2.2.2.2] using ctx.zero_eq

theorem Context.matrixUpdate {n m k : ℕ} {f : Fin n→Fin n→Fin n} {g : Fin m→Fin m→Fin m}
    {S : State} (ctx : Context (k:=k) f g S) (xs : List ℕ) :
    Context (k:=k) f g (S.setArray (array .matrix) xs) := by
  refine ⟨ctx.left_eq,ctx.right_eq,ctx.arity_eq,ctx.cutoff_eq,ctx.total_eq,ctx.zero_eq,?_,?_,?_⟩
  · simpa [Store.setArray,array] using ctx.vector_length
  · simpa [Store.setArray,array] using ctx.left_table
  · simpa [Store.setArray,array] using ctx.right_table

def point : Code := .seq (.atom (.divmod (wl .row) (wl .column) (wl .cellIndex) (wl .square))) comparePair

def prepare : List (Atom Reg Arr) := [.const (wl .zero) 0,.const (wl .one) 1,
  .binary .mul (wl .roundTodo) (wl .square) (wl .square),.allocate (array .vector) (wl .arity) (wl .zero)]

def build : Code := .seq (atoms prepare)
  (ArrayTabulate.tabulate (wl .cellIndex) (wl .rowTodo) (wl .roundTodo) (wl .one) (wl .zero)
    (base .result) (array .matrix) point)

variable {G H : Type} [Group G] [Group H] [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H]
variable {n m k : ℕ}

def initialRelation (e : G≃Fin n) (e' : H≃Fin m) : Finset (Fin (n^k+m^k)×Fin (n^k+m^k)) :=
  Finset.univ.filter (fun x=>initialEq e e' x.1 x.2=true)

theorem initialRelation_word (e : G≃Fin n) (e' : H≃Fin m) : matrixWord (initialRelation (k:=k) e e')=
    List.ofFn (fun i : Fin ((n^k+m^k)*(n^k+m^k))=>
      boolNat (initialEq e e' (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)) := by
  simp [matrixWord,initialRelation]


end GroupWL.MachinePrograms.WordMatrixPrograms
