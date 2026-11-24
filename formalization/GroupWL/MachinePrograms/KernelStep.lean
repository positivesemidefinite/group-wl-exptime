import GroupWL.MachinePrograms.KernelUpdate

/-! Each complete row step computes its row equation, scans a pivot, and
executes the corresponding matrix update; zero equations retain the chart. -/
namespace GroupWL.MachinePrograms.KernelProgram
open NatArrayLanguage
set_option maxHeartbeats 4000000

def stepCost (n p : ℕ) : ℕ := updateCost n p+n*(12*n+9)+14*n+32

theorem step_runs (p : ℕ) [NeZero p] (n m i M : ℕ) (A : List ℕ) (D : Data)
    (S : State) (bounded : S.Bounded M) (rep : Represents p n (i+1) A D S)
    (data : D.Valid p n) (positive : 1<p) (small : p*p+p≤M) (square : n*n≤M)
    (inputLength : A.length=m*n) (inputValues : ∀x∈A,x<p) (index : i<m) :
    ∃ t≤stepCost n p,∃ T,Runs (storageBound Reg Arr M) (step p) S t T ∧
      T.Bounded M ∧ Represents p n i A (eliminate p n (equation A n i p D) D) T := by
  have h1 : 1≤M := by omega
  have hroom : m*n≤M := by rw [←inputLength,←rep.input]; exact bounded.2.1 _
  have hbase : i*n≤M := (Nat.mul_le_mul_right n (Nat.le_of_lt index)).trans hroom
  have hrange : i*n+n≤A.length := by
    rw [inputLength]
    simpa [Nat.add_mul] using Nat.mul_le_mul_right n (show i+1≤m by omega)
  let U := applyAtoms rowSetup S
  have preValid : ValidAtoms M rowSetup S := by
    simp [rowSetup,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,rep.remaining,rep.ambient,rep.one]
    exact ⟨by have := bounded.1 (wr .remaining); rw [rep.remaining] at this; omega,hbase⟩
  obtain ⟨preRun,hU⟩ := atoms_runs bounded rowSetup preValid
  have urep : Represents p n i A D U := by
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
      simp [U,rowSetup,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,
        rep.ambient,rep.width,rep.remaining,rep.modulus,rep.one,rep.input,rep.lift,rep.lower]
  have ubase : U.scalar (cr .offset)=i*n := by
    simp [U,rowSetup,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,
      rep.remaining,rep.one,rep.ambient]
  have ulen : U.scalar (cr .length)=n := by
    simp [U,rowSetup,applyAtoms,Atom.apply,Store.setScalar,Store.setArray,rep.ambient]
  have uin : U.array (ca .input)=A := by
    simp [U,rowSetup,applyAtoms,Atom.apply,Store.setScalar,Store.setArray,rep.input]
  obtain ⟨tc,htc,V,sliceRun,hV,vleft,_,_,_,vout⟩ := slice_runs U M (i*n) n A hU ubase ulen uin h1 hrange
  have vrep := urep.of_left_eq vleft
  let xs := List.ofFn (fun j : Fin n => ArraySlice.value A (i*n) j)
  have xslen : xs.length=1*n := by simp [xs]
  have xsvalues : ∀x∈xs,x<p := by
    intro x hx
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
    exact MatrixArithmetic.read_lt inputValues (by omega) _
  let W := applyAtoms rowMultiplySetup V
  have multValid : ValidAtoms M rowMultiplySetup V := by
    simp [rowMultiplySetup,ValidAtoms,Atom.Valid,Atom.SmallResult,h1]
  obtain ⟨multPre,hW⟩ := atoms_runs hV rowMultiplySetup multValid
  have wleft : W.left=V.left := by
    apply Store.ext
    · intro r; cases r <;> simp [W,rowMultiplySetup,applyAtoms,Atom.apply,Store.left,Store.setScalar,Store.setArray]
    · intro a; cases a <;> simp [W,rowMultiplySetup,applyAtoms,Atom.apply,Store.left,Store.setScalar,Store.setArray]
  have wrows : W.scalar (mr .rows)=1 := by simp [W,rowMultiplySetup,applyAtoms,Atom.apply,Store.setScalar,Store.setArray]
  have winner : W.scalar (mr .inner)=n := by simp [W,rowMultiplySetup,applyAtoms,Atom.apply,Store.setScalar,Store.setArray,vrep.ambient]
  have wcols : W.scalar (mr .cols)=D.width := by simp [W,rowMultiplySetup,applyAtoms,Atom.apply,Store.setScalar,Store.setArray,vrep.width]
  have wmod : W.scalar (mr .modulus)=p := by simp [W,rowMultiplySetup,applyAtoms,Atom.apply,Store.setScalar,Store.setArray,vrep.modulus]
  have wA : W.array (ma .left)=xs := by simp [W,rowMultiplySetup,applyAtoms,Atom.apply,Store.setScalar,Store.setArray,vout,xs]
  have wB : W.array (ma .right)=D.lift := by simp [W,rowMultiplySetup,applyAtoms,Atom.apply,Store.setScalar,Store.setArray,vrep.lift]
  have hwM : 1*D.width≤M := by have := bounded.1 (wr .width); rw [rep.width] at this; simpa using this
  obtain ⟨tm,htm,X,multiplyRun,hX,xleft,_,xout,_,_,_,_⟩ := multiply_runs W M 1 n D.width p xs D.lift hW
    wrows winner wcols wmod wA wB (by omega) small hwM xslen data.liftLength xsvalues data.liftValues
  have xrep := vrep.of_left_eq (xleft.trans wleft)
  have xeq : X.array (ma .output)=equation A n i p D := xout
  let copy : Atom Reg Arr := .copyArray (sa .row) (ma .output)
  let Y := copy.apply X
  have copyRun := atom_runs hX copy trivial trivial
  have hY := copy.apply_bounded hX trivial
  have yleft : Y.left=X.left := by
    apply Store.ext
    · intro r; rfl
    · intro a; cases a <;> simp [Y,copy,Atom.apply,Store.left,Store.setArray]
  have yrow : Y.array (sa .row)=equation A n i p D := by simp [Y,copy,Atom.apply,xeq]
  obtain ⟨ts,hts,Z,searchRun,hZ,zleft,_,_,zrow,zfound,zpivot⟩ := search_runs Y M (equation A n i p D) hY yrow h1
  have zrep := xrep.of_left_eq (zleft.trans yleft)
  have branchRun : ∃ t≤updateCost n p+1,∃ T,
      Runs (storageBound Reg Arr M) (.branch (sr .found) (update p) .skip) Z t T ∧
      T.Bounded M ∧ Represents p n i A (eliminate p n (equation A n i p D) D) T := by
    cases found : PivotSearch.first (equation A n i p D) (equation A n i p D).length with
    | none =>
        have zero : Z.scalar (sr .found)=0 := by rw [found] at zfound; simpa [PivotSearch.flag] using zfound
        refine ⟨1,by omega,Z,.branch_zero zero (.skip (Store.size_le_of_bounded hZ)),hZ,?_⟩
        simpa only [eliminate,found] using zrep
    | some j =>
        have nonzero : Z.scalar (sr .found)≠0 := by
          rw [found] at zfound
          simp only [PivotSearch.flag,Option.isSome_some,if_true] at zfound
          omega
        have pj : Z.scalar (sr .pivot)=j := by rw [found] at zpivot; exact zpivot
        obtain ⟨tu,htu,T,run,hT,hrep⟩ := update_runs p n i M j A (equation A n i p D) D Z hZ zrep
          data positive small square zrow pj (equation_length _ _ _ _ _) found (equation_values _ _ _ _ _ (by omega))
        exact ⟨tu+1,by omega,T,.branch_nonzero nonzero run,hT,hrep⟩
  obtain ⟨tb,htb,T,branchRun,hT,hrep⟩ := branchRun
  rw [equation_length] at hts
  have hmult : D.width*(12*n+9)≤n*(12*n+9) := Nat.mul_le_mul_right _ data.width
  refine ⟨4+(tc+(6+(tm+(1+(ts+tb))))),?_,T,
    .seq preRun (.seq sliceRun (.seq multPre (.seq multiplyRun (.seq copyRun (.seq searchRun branchRun))))),hT,hrep⟩
  simp only [Nat.one_mul] at htm
  unfold stepCost
  have := data.width
  omega

end GroupWL.MachinePrograms.KernelProgram
