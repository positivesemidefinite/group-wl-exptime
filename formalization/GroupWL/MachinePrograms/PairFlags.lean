import GroupWL.MachinePrograms.ArrayMaterialization

/-! Flags for the ordered pairs a < b among the q² frame pairs. -/
namespace GroupWL.MachinePrograms.PairFlags
open NatArrayLanguage
inductive Reg where
  | total | index | remaining | one | zero | frames | left | right | result
  deriving DecidableEq,Fintype
inductive Arr where | output deriving DecidableEq,Fintype
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr
def registers : Fin 5 ↪ Reg := ⟨![.total,.index,.remaining,.one,.zero],by decide⟩
def cellAtoms : List (Atom Reg Arr) := [
  .divmod .left .right .index .frames,.binary .lt .result .left .right]
def table : Code := materialize registers .output .result (atoms cellAtoms)
def program : Code := .seq (.atom (.binary .mul .total .frames .frames)) table
def entry (q i : ℕ) := if i/q < i%q then 1 else 0
def flags (q : ℕ) := List.ofFn (fun i : Fin (q*q) => entry q i.val)
def Ready (q : ℕ) (S : State) := S.scalar .frames=q ∧ S.scalar .total=q*q

theorem table_runs (q M : ℕ) (hq : 0<q) (hM : 1≤M)
    (S : State) (ready : Ready q S) (bounded : S.Bounded M) :
    ∃ t≤q*q*6+6, ∃ T, Runs (storageBound Reg Arr M) table S t T ∧ T.Bounded M ∧
      Ready q T ∧ T.array .output=flags q := by
  apply materialize_runs registers .output .result (atoms cellAtoms) (Ready q) (entry q) M (q*q) 2 hM
  · intro V hV i v
    fin_cases i <;> simpa [Ready,registers,Store.setScalar] using hV
  · intro V hV xs
    simpa [Ready,Store.setArray] using hV
  · intro V hV hVB hi
    rcases hV with ⟨hf,ht⟩
    have valid : ValidAtoms M cellAtoms V := by
      simp [cellAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
        Store.setScalar,hf,hq]
      split_ifs <;> omega
    obtain ⟨run,hWB⟩ := atoms_runs hVB cellAtoms valid
    refine ⟨2,le_rfl,applyAtoms cellAtoms V,run,hWB,?_,?_,rfl,?_⟩
    · simpa [Ready,cellAtoms,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar] using And.intro hf ht
    · simp [registers,entry,cellAtoms,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,hf]
    · intro i
      fin_cases i <;> simp [registers,cellAtoms,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar]
  · exact bounded
  · exact ready
  · exact ready.2

theorem program_runs (q M : ℕ) (hq : 0<q) (hM : 1≤M) (small : q*q≤M)
    (S : State) (bounded : S.Bounded M) (hf : S.scalar .frames=q) :
    ∃ t≤q*q*6+7, ∃ T, Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧
      Ready q T ∧ T.array .output=flags q := by
  have valid : (Atom.binary .mul Reg.total Reg.frames Reg.frames : Atom Reg Arr).SmallResult M S := by
    simpa [Atom.SmallResult,BinaryOp.eval,hf] using small
  have first := atom_runs bounded (Atom.binary .mul Reg.total Reg.frames Reg.frames) trivial valid
  let U := (Atom.binary .mul Reg.total Reg.frames Reg.frames : Atom Reg Arr).apply S
  have hUB := Atom.apply_bounded bounded (Atom.binary .mul Reg.total Reg.frames Reg.frames) valid
  have ready : Ready q U := by simp [Ready,U,Atom.apply,BinaryOp.eval,Store.setScalar,hf]
  obtain ⟨t,ht,T,run,hT,hR,hout⟩ := table_runs q M hq hM U ready hUB
  exact ⟨1+t,by omega,T,first.seq run,hT,hR,hout⟩

theorem flags_values (q : ℕ) : ∀ x∈flags q,x≤1 := by
  intro x hx
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  unfold entry
  split_ifs <;> omega

end GroupWL.MachinePrograms.PairFlags
