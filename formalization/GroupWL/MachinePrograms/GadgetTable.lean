import GroupWL.MachinePrograms.GadgetAdjacency
import GroupWL.MachinePrograms.GraphInitial
import GroupWL.MachinePrograms.ArrayTabulate
import GroupWL.MachinePrograms.NatArrayComponents

/-! Materialize every edge of the multiplication graph by a counted array loop. -/
namespace GroupWL.MachinePrograms.GadgetTable
open NatArrayLanguage
abbrev Reg := GadgetAdjacency.Reg ⊕ Fin 6
abbrev Arr := Unit ⊕ Unit
abbrev Code := Program Reg Arr
set_option maxRecDepth 4096

def point : Code := .seq (.atom (.divmod (.inl 1) (.inl 2) (.inr 0) (.inr 5)))
  (GadgetAdjacency.evaluate.map Sum.inl Sum.inl)

def fill : Code := ArrayTabulate.tabulate (.inr 0) (.inr 1) (.inr 2) (.inr 3) (.inr 4) (.inl 23) (.inr ()) point

def prelude : List (Atom Reg Arr) := [
  .const (.inr 5) 4,.binary .mul (.inr 5) (.inl 0) (.inr 5),
  .binary .mul (.inr 5) (.inl 0) (.inr 5),.binary .add (.inr 5) (.inl 0) (.inr 5),
  .binary .mul (.inr 2) (.inr 5) (.inr 5),.const (.inr 3) 1,.const (.inr 4) 0]
def generate : Code := .seq (atoms prelude) fill

structure Context {n : ℕ} (f : Fin n → Fin n → Fin n) (S : Store Reg Arr) : Prop where
  order_eq : S.scalar (.inl 0)=n
  size_eq : S.scalar (.inr 5)=IndexedGadget.size n
  table_eq : S.array (.inl ())=GroupInitial.tableWord f

theorem point_runs {n : ℕ} (f : Fin n → Fin n → Fin n) (hnpos : 0<n)
    (i : Fin (IndexedGadget.size n*IndexedGadget.size n)) (S : Store Reg Arr) (B : ℕ)
    (hS : S.Bounded B) (hP : Context f S) (hi : S.scalar (.inr 0)=i.val) (h4 : 4≤B) :
    ∃ t≤201,∃ T,Runs (storageBound Reg Arr B) point S t T ∧ T.Bounded B ∧ Context f T ∧
      (∀ j : Fin 6,T.scalar (.inr j)=S.scalar (.inr j)) ∧ T.array (.inr ())=S.array (.inr ()) ∧
      T.scalar (.inl 23)=IndexedRefinement.boolNat
        (IndexedGadget.numericAdj f (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2) := by
  have hnsize : 0<IndexedGadget.size n := by unfold IndexedGadget.size;omega
  have first := atom_runs hS (.divmod (.inl 1) (.inl 2) (.inr 0) (.inr 5))
    ⟨by decide,by simpa [hP.size_eq] using hnsize⟩ trivial
  let U := (Atom.divmod (.inl 1) (.inl 2) (.inr 0) (.inr 5)).apply S
  have hU : U.Bounded B := Atom.apply_bounded hS _ trivial
  let x := (finProdFinEquiv.symm i).1
  let y := (finProdFinEquiv.symm i).2
  obtain ⟨t,ht,V,last,hV,hout⟩ := GadgetAdjacency.evaluate_runs n hnpos x y U.left B hU.left
    (by simp [U,Atom.apply,Store.left,Store.setScalar,hP.order_eq])
    (by simp [U,Atom.apply,Store.left,Store.setScalar,hi,hP.size_eq];rfl)
    (by simp [U,Atom.apply,Store.left,Store.setScalar,hi,hP.size_eq];rfl)
    (by simp [U,Atom.apply,Store.left,hP.table_eq]) h4
  let T := V.join U.right
  have run := last.left_bounded hU
  have frame0 : V.scalar 0=U.left.scalar 0 := last.scalar_eq_of_not_mem 0 (by
    simp [GadgetAdjacency.evaluate,GadgetAdjacency.prepare,GadgetAdjacency.formula,GadgetAdjacency.attachment,
      BooleanTest.compile,atoms,NatArrayLanguage.sequence,Program.scalarWrites,Atom.scalarWrites])
  have frameArray : V.array ()=U.left.array () := last.array_eq_of_not_mem () (by
    simp [GadgetAdjacency.evaluate,GadgetAdjacency.prepare,GadgetAdjacency.formula,GadgetAdjacency.attachment,
      BooleanTest.compile,atoms,NatArrayLanguage.sequence,Program.arrayWrites,Atom.arrayWrites])
  have hPT : Context f T := by
    refine ⟨?_,?_,?_⟩
    · simpa [T,U,Atom.apply,Store.left,Store.setScalar,hP.order_eq] using frame0
    · exact hP.size_eq
    · simpa [T,U,Atom.apply,Store.left,hP.table_eq] using frameArray
  refine ⟨1+t,by omega,T,Runs.seq first run,hV.join hU.right,hPT,?_,rfl,?_⟩
  · intro j;rfl
  · change V.scalar 23=_
    rw [hout]
    change IndexedRefinement.boolNat (IndexedGadget.test n (S.array (.inl ())) x.val y.val)=_
    rw [hP.table_eq,IndexedGadget.test_numericAdj]

theorem fill_runs {n : ℕ} (f : Fin n → Fin n → Fin n) (hnpos : 0<n)
    (S : Store Reg Arr) (B : ℕ) (hS : S.Bounded B) (hP : Context f S)
    (htotal : S.scalar (.inr 2)=IndexedGadget.size n*IndexedGadget.size n)
    (hone : S.scalar (.inr 3)=1) (hzero : S.scalar (.inr 4)=0) (h4 : 4≤B) :
    ∃ t≤(IndexedGadget.size n*IndexedGadget.size n)*205+4,∃ T,
      Runs (storageBound Reg Arr B) fill S t T ∧ T.Bounded B ∧ Context f T ∧
      T.array (.inr ())=GraphInitial.tableWord (IndexedGadget.numericAdj f) := by
  apply ArrayTabulate.tabulate_runs (.inr 0) (.inr 1) (.inr 2) (.inr 3) (.inr 4) (.inl 23) (.inr ()) point
    (fun i => IndexedRefinement.boolNat (IndexedGadget.numericAdj f (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2))
    (Context f) B 201
  · intro U v hU;exact ⟨by simpa using hU.order_eq,by simpa using hU.size_eq,hU.table_eq⟩
  · intro U v hU;exact ⟨by simpa using hU.order_eq,by simpa using hU.size_eq,hU.table_eq⟩
  · intro U xs hU;exact ⟨hU.order_eq,hU.size_eq,by simpa using hU.table_eq⟩
  · decide
  · decide
  · decide
  · intro i U hp hb hi htodo hone
    obtain ⟨t,ht,V,run,hV,hPV,frames,harray,hvalue⟩ := point_runs f hnpos i U B hb hp hi h4
    exact ⟨t,ht,V,run,hV,hPV,(frames 0).trans hi,(frames 1).trans htodo,(frames 3).trans hone,hvalue,harray⟩
  · exact hS
  · exact hP
  · exact htotal
  · exact hone
  · exact hzero

theorem generate_runs {n : ℕ} (f : Fin n → Fin n → Fin n) (hnpos : 0<n)
    (S : Store Reg Arr) (B : ℕ) (hS : S.Bounded B) (hn : S.scalar (.inl 0)=n)
    (ht : S.array (.inl ())=GroupInitial.tableWord f)
    (hsize : IndexedGadget.size n*IndexedGadget.size n≤B) :
    ∃ t≤(IndexedGadget.size n*IndexedGadget.size n)*205+11,∃ T,
      Runs (storageBound Reg Arr B) generate S t T ∧ T.Bounded B ∧ Context f T ∧
      T.array (.inr ())=GraphInitial.tableWord (IndexedGadget.numericAdj f) := by
  have hN : IndexedGadget.size n≤B := by
    have hp : 0<IndexedGadget.size n := by unfold IndexedGadget.size;omega
    nlinarith
  have h4 : 4≤B := by unfold IndexedGadget.size at hN;nlinarith
  have hfirst : n*4≤B := by unfold IndexedGadget.size at hN;nlinarith
  have hsecond : n*(n*4)≤B := by unfold IndexedGadget.size at hN;omega
  have valid : ValidAtoms B prelude S := by
    simp [prelude,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar,
      hn,h4,hfirst,hsecond,IndexedGadget.size] at hN hsize ⊢
    omega
  obtain ⟨init,hU⟩ := atoms_runs hS prelude valid
  let U := applyAtoms prelude S
  have hP : Context f U := by
    constructor
    · simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar,hn]
    · simp [U,applyAtoms,prelude,Atom.apply,BinaryOp.eval,Store.setScalar,hn,IndexedGadget.size]
    · exact ht
  obtain ⟨t,htt,T,last,hT,hPT,hword⟩ := fill_runs f hnpos U B hU hP
    (by simp [U,applyAtoms,prelude,Atom.apply,BinaryOp.eval,Store.setScalar,hn,IndexedGadget.size])
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar])
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar]) h4
  exact ⟨7+t,by omega,T,Runs.seq init last,hT,hPT,hword⟩
end GroupWL.MachinePrograms.GadgetTable
