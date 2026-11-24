import GroupWL.MachinePrograms.KernelData

/-! Operational proof of one nonzero Gaussian pivot and both matrix updates. -/
namespace GroupWL.MachinePrograms.KernelProgram
open NatArrayLanguage
set_option maxHeartbeats 4000000

def updateCost (n p : ℕ) : ℕ := 2*(n*n)*(12*n+9)+17*(n*n)+3*p+42

theorem update_runs (p : ℕ) [NeZero p] (n remaining M j : ℕ) (A h : List ℕ) (D : Data)
    (S : State) (bounded : S.Bounded M) (rep : Represents p n remaining A D S)
    (data : D.Valid p n) (positive : 1<p) (small : p*p+p≤M) (square : n*n≤M)
    (row : S.array (sa .row)=h) (pivotIndex : S.scalar (sr .pivot)=j)
    (length : h.length=D.width) (pivotFound : PivotSearch.first h h.length=some j)
    (values : ∀x∈h,x<p) :
    ∃ t≤updateCost n p,∃ T,Runs (storageBound Reg Arr M) (update p) S t T ∧
      T.Bounded M ∧ Represents p n remaining A (eliminate p n h D) T := by
  have hj : j<D.width := by have := (PivotSearch.first_some h _ j pivotFound).1; omega
  have hw : D.width*(D.width-1)≤M :=
    (Nat.mul_le_mul data.width ((Nat.sub_le _ _).trans data.width)).trans square
  have hn : n*(D.width-1)≤M :=
    (Nat.mul_le_mul_left n ((Nat.sub_le _ _).trans data.width)).trans square
  have h1 : 1≤M := by omega
  let U := applyAtoms pivotSetup S
  have preValid : ValidAtoms M pivotSetup S := by simp [pivotSetup,ValidAtoms,Atom.Valid,Atom.SmallResult]
  obtain ⟨preRun,hU⟩ := atoms_runs bounded pivotSetup preValid
  have uwidth : U.scalar (pr .width)=D.width := by
    simp [U,pivotSetup,applyAtoms,Atom.apply,Store.setScalar,Store.setArray,rep.width]
  have uj : U.scalar (pr .pivot)=j := by
    simp [U,pivotSetup,applyAtoms,Atom.apply,Store.setScalar,Store.setArray,pivotIndex]
  have up : U.scalar (pr .modulus)=p := by
    simp [U,pivotSetup,applyAtoms,Atom.apply,Store.setScalar,Store.setArray,rep.modulus]
  have uh : U.array (pa .row)=h := by
    simp [U,pivotSetup,applyAtoms,Atom.apply,Store.setScalar,Store.setArray,row]
  have uleft : U.left=S.left := by
    apply Store.ext
    · intro r; cases r <;> simp [U,pivotSetup,applyAtoms,Atom.apply,Store.left,Store.setScalar,Store.setArray]
    · intro a; cases a <;> simp [U,pivotSetup,applyAtoms,Atom.apply,Store.left,Store.setScalar,Store.setArray]
  obtain ⟨tp,htp,V,pivotRun,hV,vleft,_,_,_,vlift,vlower⟩ :=
    pivot_runs p U M D.width j h hU uwidth uj up uh length hj small hw values
  have vrep := rep.of_left_eq (vleft.trans uleft)
  let L := List.ofFn (fun i : Fin (D.width*(D.width-1)) =>
    PivotMatrix.liftValue h (D.width-1) j (-((h[j]?.getD 0:ℕ):ZMod p)⁻¹).val p i)
  let R := List.ofFn (fun i : Fin (D.width*(D.width-1)) => PivotMatrix.lowerValue (D.width-1) j i)
  have hL : ∀x∈L,x<p := pivotLift_values _ _ _ _ _ positive
  have hR : ∀x∈R,x<p := pivotLower_values _ _ _ positive
  let W := applyAtoms liftMultiplySetup V
  have multValid : ValidAtoms M liftMultiplySetup V := by
    simp [liftMultiplySetup,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,Store.setArray,vrep.width,vrep.one]
    have := hV.1 (wr .width)
    rw [vrep.width] at this
    omega
  obtain ⟨multPre,hW⟩ := atoms_runs hV liftMultiplySetup multValid
  have wleft : W.left=V.left := by
    apply Store.ext
    · intro r; cases r <;> simp [W,liftMultiplySetup,applyAtoms,Atom.apply,Store.left,Store.setScalar,Store.setArray]
    · intro a; cases a <;> simp [W,liftMultiplySetup,applyAtoms,Atom.apply,Store.left,Store.setScalar,Store.setArray]
  have wrows : W.scalar (mr .rows)=n := by simp [W,liftMultiplySetup,applyAtoms,Atom.apply,Store.setScalar,Store.setArray,vrep.ambient]
  have winner : W.scalar (mr .inner)=D.width := by simp [W,liftMultiplySetup,applyAtoms,Atom.apply,Store.setScalar,Store.setArray,vrep.width]
  have wcols : W.scalar (mr .cols)=D.width-1 := by simp [W,liftMultiplySetup,applyAtoms,Atom.apply,Store.setScalar,Store.setArray,BinaryOp.eval,vrep.width,vrep.one]
  have wmod : W.scalar (mr .modulus)=p := by simp [W,liftMultiplySetup,applyAtoms,Atom.apply,Store.setScalar,Store.setArray,vrep.modulus]
  have wA : W.array (ma .left)=D.lift := by simp [W,liftMultiplySetup,applyAtoms,Atom.apply,Store.setScalar,Store.setArray,vrep.lift]
  have wB : W.array (ma .right)=L := by simp [W,liftMultiplySetup,applyAtoms,Atom.apply,Store.setScalar,Store.setArray,vlift,L]
  have wR : W.array (pa .lowerTranspose)=R := by
    simpa [W,liftMultiplySetup,applyAtoms,Atom.apply,Store.setScalar,Store.setArray,R] using vlower
  obtain ⟨tl,htl,X,liftRun,hX,xleft,xrest,xout,xrows,xinner,xcols,xmod⟩ := multiply_runs W M
    n D.width (D.width-1) p D.lift L hW wrows winner wcols wmod wA wB (by omega) small hn
    data.liftLength (by simp [L]) data.liftValues hL
  have xrep := vrep.of_left_eq (xleft.trans wleft)
  have xR : X.array (pa .lowerTranspose)=R := by
    exact (congrArg (fun T => T.right.left.array PivotMatrix.Arr.lowerTranspose) xrest).trans wR
  let Y := applyAtoms lowerMultiplySetup X
  have lowerValid : ValidAtoms M lowerMultiplySetup X := by simp [lowerMultiplySetup,ValidAtoms,Atom.Valid,Atom.SmallResult]
  obtain ⟨lowerPre,hY⟩ := atoms_runs hX lowerMultiplySetup lowerValid
  have yrows : Y.scalar (mr .rows)=n := by simpa [Y,lowerMultiplySetup,applyAtoms,Atom.apply,Store.setArray] using xrows
  have yinner : Y.scalar (mr .inner)=D.width := by simpa [Y,lowerMultiplySetup,applyAtoms,Atom.apply,Store.setArray] using xinner
  have ycols : Y.scalar (mr .cols)=D.width-1 := by simpa [Y,lowerMultiplySetup,applyAtoms,Atom.apply,Store.setArray] using xcols
  have ymod : Y.scalar (mr .modulus)=p := by simpa [Y,lowerMultiplySetup,applyAtoms,Atom.apply,Store.setArray] using xmod
  have yA : Y.array (ma .left)=D.lowerTranspose := by simp [Y,lowerMultiplySetup,applyAtoms,Atom.apply,Store.setArray,xrep.lower]
  have yB : Y.array (ma .right)=R := by simp [Y,lowerMultiplySetup,applyAtoms,Atom.apply,Store.setArray,xR]
  have ylift : Y.array (wa .lift)=matrixProduct D.lift L n D.width (D.width-1) p := by
    simp [Y,lowerMultiplySetup,applyAtoms,Atom.apply,Store.setArray,xout]
  have yscalar (r : WorkReg) : Y.scalar (wr r)=X.scalar (wr r) := rfl
  have yinput : Y.array (wa .input)=A := by
    simpa [Y,lowerMultiplySetup,applyAtoms,Atom.apply,Store.setArray] using xrep.input
  obtain ⟨tr,htr,Z,lowerRun,hZ,zleft,_,zout,_,_,_,_⟩ := multiply_runs Y M
    n D.width (D.width-1) p D.lowerTranspose R hY yrows yinner ycols ymod yA yB
    (by omega) small hn data.lowerLength (by simp [R]) data.lowerValues hR
  have zscalar (r : WorkReg) : Z.scalar (wr r)=X.scalar (wr r) :=
    (congrArg (fun T => T.scalar r) zleft).trans (yscalar r)
  have zlift : Z.array (wa .lift)=matrixProduct D.lift L n D.width (D.width-1) p :=
    (congrArg (fun T => T.array WorkArr.lift) zleft).trans ylift
  have zinput : Z.array (wa .input)=A := (congrArg (fun T => T.array WorkArr.input) zleft).trans yinput
  let finish : List (Atom Reg Arr) := [.copyArray (wa .lowerTranspose) (ma .output),
    .binary .sub (wr .width) (wr .width) (wr .one)]
  have finalValid : ValidAtoms M finish Z := by
    simp [finish,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setArray,zscalar,xrep.width,xrep.one]
    have := hZ.1 (wr .width)
    rw [zscalar,xrep.width] at this
    omega
  obtain ⟨finalRun,hT⟩ := atoms_runs hZ finish finalValid
  let T := applyAtoms finish Z
  have hrep : Represents p n remaining A (eliminate p n h D) T := by
    simp only [eliminate,pivotFound]
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
      simp [T,finish,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,
        zscalar,zlift,zinput,zout,xrep.ambient,xrep.width,xrep.remaining,xrep.modulus,xrep.one,L,R]
  have hmul : n*(D.width-1)*(12*D.width+9)≤n*n*(12*n+9) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left n ((Nat.sub_le _ _).trans data.width)) (by have := data.width; omega)
  have hpiv : D.width*(D.width-1)≤n*n := Nat.mul_le_mul data.width ((Nat.sub_le _ _).trans data.width)
  refine ⟨4+(tp+(6+(tl+(3+(tr+2))))),?_,T,
    .seq preRun (.seq pivotRun (.seq multPre (.seq liftRun (.seq lowerPre (.seq lowerRun finalRun))))),hT,hrep⟩
  unfold updateCost
  rw [Nat.mul_assoc 2]
  omega

end GroupWL.MachinePrograms.KernelProgram
