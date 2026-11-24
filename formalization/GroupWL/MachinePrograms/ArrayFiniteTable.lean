import GroupWL.MachinePrograms.NatArrayProofs
import GroupWL.MachinePrograms.NatArrayFrames

/-! Fixed finite arithmetic tables become finite comparison/branch programs.
The table is expanded into syntax; the runtime has no table-evaluation oracle. -/
namespace GroupWL.MachinePrograms.NatArrayLanguage

variable {Reg Arr : Type*} [DecidableEq Reg] [DecidableEq Arr]
  [Fintype Reg] [Fintype Arr]

def tableFrom (input output flag : Reg) : ℕ → List ℕ → Program Reg Arr
  | _,[] => .atom (.const output 0)
  | base,v::vs => .seq (atoms [.const flag base,.binary .eq flag input flag])
      (.branch flag (.atom (.const output v)) (tableFrom input output flag (base+1) vs))

theorem tableFrom_runs (input output flag : Reg) (different : input≠flag)
    (base : ℕ) (values : List ℕ) (S : Store Reg Arr) (M : ℕ)
    (bounded : S.Bounded M) (one : 1≤M) (constants : base+values.length≤M)
    (small : ∀ v∈values,v≤M) (input_ge : base≤S.scalar input) :
    ∃ t≤3*values.length+1,∃ T,
      Runs (storageBound Reg Arr M) (tableFrom input output flag base values) S t T ∧
      T.Bounded M ∧ T.scalar output=(values[S.scalar input-base]?).getD 0 := by
  induction values generalizing base S with
  | nil =>
      refine ⟨1,by simp,S.setScalar output 0,
        atom_runs bounded (.const output 0) trivial (by exact Nat.zero_le _),
        bounded.setScalar output (Nat.zero_le _),?_⟩
      simp
  | cons v vs ih =>
      let instructions : List (Atom Reg Arr) := [.const flag base,.binary .eq flag input flag]
      have valid : ValidAtoms M instructions S := by
        simp only [instructions,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
          Store.setScalar,Function.update_of_ne different,Function.update_self]
        refine ⟨trivial,by simpa only [List.length_cons] using (show base≤M by simp only [List.length_cons] at constants; omega),
          trivial,?_,trivial⟩
        split_ifs <;> omega
      obtain ⟨pre,hU⟩ := atoms_runs bounded instructions valid
      let U := applyAtoms instructions S
      have he : U.scalar input=S.scalar input := by
        simp [U,applyAtoms,instructions,Atom.apply,Store.setScalar,different]
      have hf : U.scalar flag=if S.scalar input=base then 1 else 0 := by
        simp [U,applyAtoms,instructions,Atom.apply,BinaryOp.eval,Store.setScalar,different]
      by_cases h : S.scalar input=base
      · have hv := small v (by simp)
        have last := atom_runs hU (Atom.const output v) trivial hv
        refine ⟨2+(1+1),by simp only [List.length_cons]; omega,U.setScalar output v,
          .seq pre (.branch_nonzero (show U.scalar flag≠0 by rw [hf]; simp [h]) last),hU.setScalar output hv,?_⟩
        simp [h]
      · have hc : base+1+vs.length≤M := by simpa [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using constants
        obtain ⟨t,ht,T,run,hT,ho⟩ := ih (base+1) U hU hc (fun x hx => small x (by simp [hx])) (by rw [he]; omega)
        refine ⟨2+(t+1),by simp only [List.length_cons]; omega,T,
          .seq pre (.branch_zero (show U.scalar flag=0 by rw [hf]; simp [h]) run),hT,?_⟩
        rw [he] at ho
        have hx : S.scalar input-base=(S.scalar input-(base+1))+1 := by omega
        simpa only [hx,List.getElem?_cons_succ] using ho

def finiteTable (input output flag : Reg) (values : List ℕ) : Program Reg Arr :=
  tableFrom input output flag 0 values

theorem finiteTable_runs (input output flag : Reg) (different : input≠flag)
    (values : List ℕ) (S : Store Reg Arr) (M : ℕ) (bounded : S.Bounded M)
    (one : 1≤M) (length : values.length≤M) (small : ∀v∈values,v≤M) :
    ∃ t≤3*values.length+1,∃ T,
      Runs (storageBound Reg Arr M) (finiteTable input output flag values) S t T ∧
      T.Bounded M ∧ T.scalar output=(values[S.scalar input]?).getD 0 := by
  simpa only [Nat.zero_add,Nat.sub_zero] using
    tableFrom_runs input output flag different 0 values S M bounded one (by omega) small (Nat.zero_le _)

theorem tableFrom_not_scalarWrites (input output flag r : Reg) (hout : r≠output) (hflag : r≠flag)
    (values : List ℕ) (base : ℕ) : r∉(tableFrom (Arr:=Arr) input output flag base values).scalarWrites := by
  induction values generalizing base with
  | nil => simp [tableFrom,Program.scalarWrites,Atom.scalarWrites,hout]
  | cons v vs ih =>
      simp [tableFrom,atoms,sequence,Program.scalarWrites,Atom.scalarWrites,hout,hflag,ih]

theorem tableFrom_arrayWrites (input output flag : Reg) (values : List ℕ) (base : ℕ) :
    (tableFrom (Arr:=Arr) input output flag base values).arrayWrites=∅ := by
  induction values generalizing base with
  | nil => rfl
  | cons v vs ih => simp [tableFrom,atoms,sequence,Program.arrayWrites,Atom.arrayWrites,ih]

theorem finiteTable_not_scalarWrites (input output flag r : Reg) (hout : r≠output) (hflag : r≠flag)
    (values : List ℕ) : r∉(finiteTable (Arr:=Arr) input output flag values).scalarWrites :=
  tableFrom_not_scalarWrites input output flag r hout hflag values 0

@[simp] theorem finiteTable_arrayWrites (input output flag : Reg) (values : List ℕ) :
    (finiteTable (Arr:=Arr) input output flag values).arrayWrites=∅ :=
  tableFrom_arrayWrites input output flag values 0

end GroupWL.MachinePrograms.NatArrayLanguage
