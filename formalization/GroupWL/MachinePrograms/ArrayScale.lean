import GroupWL.MachinePrograms.ArrayMaterialization

/-! Materialized multiplication of an array by a runtime natural factor. -/
namespace GroupWL.MachinePrograms.ArrayScale
open NatArrayLanguage

inductive Reg where | total | index | remaining | one | zero | factor | result deriving DecidableEq,Fintype
inductive Arr where | input | output deriving DecidableEq,Fintype
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr
def registers : Fin 5 ↪ Reg := ⟨![.total,.index,.remaining,.one,.zero],by decide⟩
def cellAtoms : List (Atom Reg Arr) := [.read .result .input .index,.binary .mul .result .result .factor]
def table : Code := materialize registers .output .result (atoms cellAtoms)
def program : Code := .seq (.atom (.arrayLength .total .input)) table

def Ready (xs : List ℕ) (factor : ℕ) (S : State) : Prop :=
  S.array .input=xs ∧ S.scalar .factor=factor ∧ S.scalar .total=xs.length

theorem table_runs (xs : List ℕ) (factor M : ℕ) (hM : 1≤M)
    (small : ∀ i<xs.length,xs[i]?.getD 0*factor≤M)
    (S : State) (ready : Ready xs factor S) (bounded : S.Bounded M) :
    ∃ t≤xs.length*6+6, ∃ T, Runs (storageBound Reg Arr M) table S t T ∧ T.Bounded M ∧
      Ready xs factor T ∧ T.array .output=List.ofFn (fun i : Fin xs.length => xs[i.val]?.getD 0*factor) := by
  apply materialize_runs registers .output .result (atoms cellAtoms) (Ready xs factor)
    (fun i => xs[i]?.getD 0*factor) M xs.length 2 hM
  · intro V hV i v
    fin_cases i <;> simpa [Ready,registers,Store.setScalar] using hV
  · intro V hV ys
    simpa [Ready,Store.setArray] using hV
  · intro V hV hVB hi
    rcases hV with ⟨hx,hf,hn⟩
    change V.scalar .index<xs.length at hi
    have valid : ValidAtoms M cellAtoms V := by
      simp [cellAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar,hx,hf,hi]
      simpa only [List.getElem?_eq_getElem hi,Option.getD_some] using small _ hi
    obtain ⟨run,hWB⟩ := atoms_runs hVB cellAtoms valid
    refine ⟨2,le_rfl,applyAtoms cellAtoms V,run,hWB,?_,?_,rfl,?_⟩
    · simpa [Ready,cellAtoms,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar] using And.intro hx (And.intro hf hn)
    · simp [registers,cellAtoms,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,hx,hf]
    · intro i
      fin_cases i <;> simp [registers,cellAtoms,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar]
  · exact bounded
  · exact ready
  · exact ready.2.2

theorem program_runs (xs : List ℕ) (factor M : ℕ) (hM : 1≤M)
    (small : ∀ i<xs.length,xs[i]?.getD 0*factor≤M)
    (S : State) (bounded : S.Bounded M) (hx : S.array .input=xs) (hf : S.scalar .factor=factor) :
    ∃ t≤xs.length*6+7, ∃ T, Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧
      Ready xs factor T ∧ T.array .output=List.ofFn (fun i : Fin xs.length => xs[i.val]?.getD 0*factor) := by
  let U := (Atom.arrayLength Reg.total Arr.input).apply S
  have hUB := Atom.apply_bounded bounded (Atom.arrayLength Reg.total Arr.input) trivial
  have first := atom_runs bounded (Atom.arrayLength Reg.total Arr.input) trivial trivial
  have ready : Ready xs factor U := by simp [Ready,U,Atom.apply,Store.setScalar,hx,hf]
  obtain ⟨t,ht,T,run,hT,hR,hout⟩ := table_runs xs factor M hM small U ready hUB
  exact ⟨1+t,by omega,T,first.seq run,hT,hR,hout⟩

end GroupWL.MachinePrograms.ArrayScale
