import GroupWL.MachinePrograms.ArrayMaterialization

/-! A matrix with one selected coordinate in each row. -/
namespace GroupWL.MachinePrograms.SelectorMatrix
open NatArrayLanguage

inductive Reg where
  | total | index | remaining | one | zero | columns | rows | row | column | selected | result
  deriving DecidableEq,Fintype
inductive Arr where | selectors | output deriving DecidableEq,Fintype
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def registers : Fin 5 ↪ Reg := ⟨![.total,.index,.remaining,.one,.zero],by decide⟩
def cellAtoms : List (Atom Reg Arr) := [
  .divmod .row .column .index .columns,.read .selected .selectors .row,.binary .eq .result .column .selected]
def table : Code := materialize registers .output .result (atoms cellAtoms)
def setup : List (Atom Reg Arr) := [.arrayLength .rows .selectors,.binary .mul .total .rows .columns]
def program : Code := .seq (atoms setup) table

def entry (selectors : List ℕ) (cols i : ℕ) : ℕ := if i%cols=selectors[i/cols]?.getD 0 then 1 else 0
def word (selectors : List ℕ) (cols : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin (selectors.length*cols) => entry selectors cols i.val)
def Ready (selectors : List ℕ) (cols : ℕ) (S : State) : Prop :=
  S.array .selectors=selectors ∧ S.scalar .columns=cols ∧ S.scalar .total=selectors.length*cols

theorem table_runs (selectors : List ℕ) (cols M : ℕ) (hM : 1≤M)
    (S : State) (ready : Ready selectors cols S) (bounded : S.Bounded M) :
    ∃ t≤selectors.length*cols*7+6, ∃ T, Runs (storageBound Reg Arr M) table S t T ∧ T.Bounded M ∧
      Ready selectors cols T ∧ T.array .output=word selectors cols := by
  apply materialize_runs registers .output .result (atoms cellAtoms) (Ready selectors cols)
    (entry selectors cols) M (selectors.length*cols) 3 hM
  · intro V hV i v
    fin_cases i <;> simpa [Ready,registers,Store.setScalar] using hV
  · intro V hV xs
    simpa [Ready,Store.setArray] using hV
  · intro V hV hVB hi
    change V.scalar .index<selectors.length*cols at hi
    rcases hV with ⟨hx,hc,hn⟩
    have hpos : 0<cols := by nlinarith
    have hrow : V.scalar .index/cols<selectors.length := (Nat.div_lt_iff_lt_mul hpos).2 hi
    have valid : ValidAtoms M cellAtoms V := by
      simp [cellAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
        Store.setScalar,hx,hc,hpos,hrow]
      split_ifs <;> omega
    obtain ⟨run,hWB⟩ := atoms_runs hVB cellAtoms valid
    refine ⟨3,le_rfl,applyAtoms cellAtoms V,run,hWB,?_,?_,rfl,?_⟩
    · simpa [Ready,cellAtoms,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar] using And.intro hx (And.intro hc hn)
    · simp [registers,entry,cellAtoms,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,hx,hc]
    · intro i
      fin_cases i <;> simp [registers,cellAtoms,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar]
  · exact bounded
  · exact ready
  · exact ready.2.2

theorem program_runs (selectors : List ℕ) (cols M : ℕ) (hM : 1≤M) (small : selectors.length*cols≤M)
    (S : State) (bounded : S.Bounded M) (hx : S.array .selectors=selectors) (hc : S.scalar .columns=cols) :
    ∃ t≤selectors.length*cols*7+8, ∃ T, Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧
      Ready selectors cols T ∧ T.array .output=word selectors cols := by
  have valid : ValidAtoms M setup S := by
    simp [setup,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar,hx,hc,small]
  obtain ⟨first,hUB⟩ := atoms_runs bounded setup valid
  let U := applyAtoms setup S
  have ready : Ready selectors cols U := by
    simp [Ready,U,setup,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,hx,hc]
  obtain ⟨t,ht,T,run,hT,hR,hout⟩ := table_runs selectors cols M hM U ready hUB
  exact ⟨2+t,by omega,T,first.seq run,hT,hR,hout⟩

end GroupWL.MachinePrograms.SelectorMatrix
