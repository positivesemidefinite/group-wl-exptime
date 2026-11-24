import GroupWL.MachinePrograms.KernelStep

/-! Complete bounded execution of the concrete Gaussian kernel program. -/
namespace GroupWL.MachinePrograms.KernelProgram
open NatArrayLanguage
set_option maxHeartbeats 2000000

theorem setup_runs (p n m M : ℕ) (A : List ℕ) (S : State)
    (bounded : S.Bounded M) (ambient : S.scalar (wr .ambient)=n)
    (rows : S.scalar (wr .rows)=m) (modulus : S.scalar (wr .modulus)=p)
    (input : S.array (wa .input)=A) (one : 1≤M) (square : n*n≤M) :
    ∃ t≤6*n+13,∃ T,Runs (storageBound Reg Arr M) setup S t T ∧
      T.Bounded M ∧ Represents p n m A (initial n) T := by
  let pre : List (Atom Reg Arr) := [
    .const (wr .one) 1,.copy (wr .width) (wr .ambient),
    .copy (wr .remaining) (wr .rows),.copy (ir .dimension) (wr .ambient)]
  have preValid : ValidAtoms M pre S := by simp [pre,ValidAtoms,Atom.Valid,Atom.SmallResult,one]
  obtain ⟨preRun,hU⟩ := atoms_runs bounded pre preValid
  let U := applyAtoms pre S
  have un : U.scalar (ir .dimension)=n := by simp [U,pre,applyAtoms,Atom.apply,Store.setScalar,ambient]
  obtain ⟨t,ht,V,run,hV,vleft,vout⟩ := identity_runs U M n hU un one square
  have scalar (r : WorkReg) : V.scalar (wr r)=U.scalar (wr r) := congrArg (fun X => X.scalar r) vleft
  have arrays (a : WorkArr) : V.array (wa a)=U.array (wa a) := congrArg (fun X => X.array a) vleft
  let finish : List (Atom Reg Arr) := [.copyArray (wa .lift) (ia .output),
    .copyArray (wa .lowerTranspose) (ia .output)]
  have finalValid : ValidAtoms M finish V := by simp [finish,ValidAtoms,Atom.Valid,Atom.SmallResult]
  obtain ⟨finalRun,hT⟩ := atoms_runs hV finish finalValid
  let T := applyAtoms finish V
  have hrep : Represents p n m A (initial n) T := by
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
      simp [T,finish,applyAtoms,Atom.apply,Store.setArray,scalar,arrays,U,pre,
        Store.setScalar,ambient,rows,modulus,input,vout,initial]
  exact ⟨4+(t+2),by omega,T,.seq preRun (.seq run finalRun),hT,hrep⟩

theorem while_runs (p : ℕ) [NeZero p] (n m M i : ℕ) (A : List ℕ) (D : Data)
    (S : State) (bounded : S.Bounded M) (rep : Represents p n i A D S)
    (data : D.Valid p n) (positive : 1<p) (small : p*p+p≤M) (square : n*n≤M)
    (inputLength : A.length=m*n) (inputValues : ∀x∈A,x<p) (remaining : i≤m) :
    ∃ t ≤ i*(stepCost n p+1)+1,∃ T,
      Runs (storageBound Reg Arr M) (.while (wr .remaining) (step p)) S t T ∧
      T.Bounded M ∧ Represents p n 0 A (executeRows A p n i D) T := by
  induction i generalizing S D with
  | zero =>
      exact ⟨1,by omega,S,.while_zero rep.remaining (Store.size_le_of_bounded bounded),bounded,rep⟩
  | succ i ih =>
      obtain ⟨ts,hts,U,stepRun,hU,urep⟩ := step_runs p n m i M A D S bounded rep data
        positive small square inputLength inputValues (by omega)
      obtain ⟨t,ht,T,run,hT,hrep⟩ := ih (eliminate p n (equation A n i p D) D) U hU urep
        (eliminate_valid p n _ D (by omega) data) (by omega)
      refine ⟨ts+t+1,?_,T,.while_nonzero (by rw [rep.remaining]; omega) stepRun run,hT,hrep⟩
      nlinarith

def programCost (m n p : ℕ) : ℕ := 6*n+m*(stepCost n p+1)+14

theorem program_runs (p : ℕ) [NeZero p] (n m M : ℕ) (A : List ℕ) (S : State)
    (bounded : S.Bounded M) (ambient : S.scalar (wr .ambient)=n)
    (rows : S.scalar (wr .rows)=m) (modulus : S.scalar (wr .modulus)=p)
    (input : S.array (wa .input)=A) (positive : 1<p) (small : p*p+p≤M) (square : n*n≤M)
    (inputLength : A.length=m*n) (inputValues : ∀x∈A,x<p) :
    ∃ t≤programCost m n p,∃ T,Runs (storageBound Reg Arr M) (program p) S t T ∧
      T.Bounded M ∧ Represents p n 0 A (executeRows A p n m (initial n)) T := by
  obtain ⟨ts,hts,U,setupRun,hU,urep⟩ := setup_runs p n m M A S bounded ambient rows modulus input
    (by omega) square
  obtain ⟨t,ht,T,run,hT,hrep⟩ := while_runs p n m M m A (initial n) U hU urep
    (initial_valid p n positive) positive small square inputLength inputValues le_rfl
  exact ⟨ts+t,by unfold programCost; omega,T,.seq setupRun run,hT,hrep⟩

end GroupWL.MachinePrograms.KernelProgram
