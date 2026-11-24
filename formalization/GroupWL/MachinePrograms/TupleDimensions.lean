import GroupWL.MachinePrograms.NatArrayPower

/-! Compute the two tuple counts, their sum, and the common replacement width. -/
namespace GroupWL.MachinePrograms.TupleDimensions
open NatArrayLanguage
abbrev Reg := Fin 13
abbrev Arr := Unit
abbrev Code := Program Reg Arr
abbrev State := Store Reg Arr

def powerRegisters : Fin 5 ↪ Reg := ⟨fun i=>⟨i.val+3,by omega⟩,by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only at this
  omega⟩

def prepare : List (Atom Reg Arr) := [.copy 3 0,.copy 4 2]
def between : List (Atom Reg Arr) := [.copy 8 5,.copy 3 1]
def finish : List (Atom Reg Arr) := [.copy 9 5,.binary .add 10 8 9,.copy 11 0,.binary .lt 12 0 1]
def program : Code := .seq (atoms prepare)
  (.seq (NatArrayPower.program powerRegisters)
    (.seq (atoms between) (.seq (NatArrayPower.program powerRegisters)
      (.seq (atoms finish) (.branch 12 (.atom (.copy 11 1)) .skip)))))

theorem program_runs (S : State) (B n m k : ℕ) (hS : S.Bounded B)
    (hn : 0<n) (hm : 0<m) (left : S.scalar 0=n) (right : S.scalar 1=m)
    (arity : S.scalar 2=k) (room : n^k+m^k≤B) :
    ∃t≤6*k+18,∃T,Runs (storageBound Reg Arr B) program S t T ∧ T.Bounded B ∧
      T.scalar 0=n ∧ T.scalar 1=m ∧ T.scalar 2=k ∧
      T.scalar 8=n^k ∧ T.scalar 9=m^k ∧ T.scalar 10=n^k+m^k ∧ T.scalar 11=max n m := by
  have h1 : 1≤B := (one_le_pow₀ hn).trans (by omega : n^k≤B)
  obtain ⟨pre,hA⟩ := atoms_runs hS prepare (by simp [prepare,ValidAtoms,Atom.Valid,Atom.SmallResult])
  let A := applyAtoms prepare S
  have ab : A.scalar (powerRegisters 0)=n := by simp [A,applyAtoms,prepare,Atom.apply,Store.setScalar,powerRegisters,left]
  have ae : A.scalar (powerRegisters 1)=k := by simp [A,applyAtoms,prepare,Atom.apply,Store.setScalar,powerRegisters,arity]
  obtain ⟨U,t,ht,first,hU,_,uek,ucount,_,_⟩ := NatArrayPower.program_runs powerRegisters A n k B hA ab ae hn (by omega)
  change U.scalar 4=k at uek
  change U.scalar 5=n^k at ucount
  have frame (r : Reg) (hr : r∈({0,1,2,8,9,10,11} : Finset Reg)) : U.scalar r=S.scalar r := by
    exact (Runs.seq pre first).scalar_eq_of_not_mem r
      ((by decide +kernel : ∀r∈({0,1,2,8,9,10,11} : Finset Reg),r∉(Program.seq (atoms prepare) (NatArrayPower.program powerRegisters)).scalarWrites) r hr)
  obtain ⟨middle,hC⟩ := atoms_runs hU between (by simp [between,ValidAtoms,Atom.Valid,Atom.SmallResult])
  let C := applyAtoms between U
  have cb : C.scalar (powerRegisters 0)=m := by
    simp [C,applyAtoms,between,Atom.apply,Store.setScalar,powerRegisters,frame 1 (by decide),right]
  have ce : C.scalar (powerRegisters 1)=k := by simp [C,applyAtoms,between,Atom.apply,Store.setScalar,powerRegisters,uek]
  have saved : C.scalar 8=n^k := by simp [C,applyAtoms,between,Atom.apply,Store.setScalar,ucount]
  obtain ⟨V,u,hu,second,hV,_,_,vcount,_,_⟩ := NatArrayPower.program_runs powerRegisters C m k B hC cb ce hm (by omega)
  change V.scalar 5=m^k at vcount
  have vframe (r : Reg) (hr : r∈({0,1,2} : Finset Reg)) : V.scalar r=S.scalar r := by
    exact (Runs.seq pre (Runs.seq first (Runs.seq middle second))).scalar_eq_of_not_mem r
      ((by decide +kernel : ∀r∈({0,1,2} : Finset Reg),r∉(Program.seq (atoms prepare) (.seq (NatArrayPower.program powerRegisters)
        (.seq (atoms between) (NatArrayPower.program powerRegisters)))).scalarWrites) r hr)
  have vsaved : V.scalar 8=n^k := (second.scalar_eq_of_not_mem 8 (by decide +kernel)).trans saved
  have vl : V.scalar 0=n := (vframe 0 (by decide)).trans left
  have vr : V.scalar 1=m := (vframe 1 (by decide)).trans right
  have vk : V.scalar 2=k := (vframe 2 (by decide)).trans arity
  have valid : ValidAtoms B finish V := by
    simp [finish,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar,vsaved,vcount,room]
    split_ifs <;> omega
  obtain ⟨done,hD⟩ := atoms_runs hV finish valid
  let D := applyAtoms finish V
  have df : D.scalar 12=if n<m then 1 else 0 := by
    simp [D,applyAtoms,finish,Atom.apply,BinaryOp.eval,Store.setScalar,vl,vr]
  have ds : D.scalar 11=n := by simp [D,applyAtoms,finish,Atom.apply,Store.setScalar,vl]
  have dr : D.scalar 1=m := by simp [D,applyAtoms,finish,Atom.apply,Store.setScalar,vr]
  have deq : D.scalar 0=n ∧ D.scalar 1=m ∧ D.scalar 2=k ∧ D.scalar 8=n^k ∧
      D.scalar 9=m^k ∧ D.scalar 10=n^k+m^k := by
    simp [D,applyAtoms,finish,Atom.apply,BinaryOp.eval,Store.setScalar,vl,vr,vk,vsaved,vcount]
  by_cases hlt : n<m
  · have run := atom_runs hD (.copy 11 1) trivial trivial
    have hE := (Atom.copy 11 1 : Atom Reg Arr).apply_bounded hD trivial
    refine ⟨2+(t+(2+(u+(4+2)))),by omega,(Atom.copy 11 1).apply D,
      .seq pre (.seq first (.seq middle (.seq second (.seq done (.branch_nonzero (by change D.scalar 12≠0; simp [df,hlt]) run))))),hE,?_⟩
    simpa [Atom.apply,Store.setScalar,dr,max_eq_right (Nat.le_of_lt hlt)] using deq
  · refine ⟨2+(t+(2+(u+(4+1)))),by omega,D,
      .seq pre (.seq first (.seq middle (.seq second (.seq done (.branch_zero (by change D.scalar 12=0; simp [df,hlt]) (.skip (Store.size_le_of_bounded hD))))))),hD,?_⟩
    exact ⟨deq.1,deq.2.1,deq.2.2.1,deq.2.2.2.1,deq.2.2.2.2.1,deq.2.2.2.2.2,by simpa [max_eq_left (by omega : m≤n)] using ds⟩

end GroupWL.MachinePrograms.TupleDimensions
