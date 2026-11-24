import GroupWL.MachinePrograms.TensorGroupTable

/-! The closed table-generating program, including exponentiation and allocation. -/
namespace GroupWL.MachinePrograms.TensorGroupProgram
open NatArrayLanguage
open TensorGroupCode

def powerRegs : Fin 5 ↪ Reg where
  toFun := ![l .modulus,a .dimension,a .order,a .powerTodo,a .powerOne]
  inj' := by decide +kernel

def materialize (half : ℕ) : Code := .seq (atoms [
    .const (l .one) 1,.const (a .zero) 0,
    .binary .add (a .dimension) (l .inputDimension) (l .outputDimension)])
  (.seq (NatArrayPower.program powerRegs)
    (.seq (atoms [.binary .mul (a .square) (a .order) (a .order),.allocate (.inr ()) (a .square) (a .zero)])
      (tableLoop half)))

def tableCost (p n m : ℕ) : ℕ := (p^(n+m))^2*((n+m)*(14*n^2+9*n+23)+15)+3*(n+m)+12

def tableWord (C : List ℕ) (p n m half : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin ((p^(n+m))^2) =>multiplication C p n m half (i.val/p^(n+m)) (i.val%p^(n+m)))

theorem materialize_runs (S : State) (M half : ℕ) (bounded : S.Bounded M)
    (positive : 0<S.scalar (l .modulus))
    (room : (S.scalar (l .modulus))^3+3*S.scalar (l .modulus)≤M)
    (length : (S.array (.inl .coefficients)).length=
      S.scalar (l .inputDimension)*S.scalar (l .inputDimension)*S.scalar (l .outputDimension))
    (small : ∀x∈S.array (.inl .coefficients),x<S.scalar (l .modulus))
    (halfSmall : half<S.scalar (l .modulus))
    (dimension : S.scalar (l .inputDimension)+S.scalar (l .outputDimension)≤M)
    (power : ((S.scalar (l .modulus))^(S.scalar (l .inputDimension)+S.scalar (l .outputDimension)))^2≤M) :
    ∃t≤tableCost (S.scalar (l .modulus)) (S.scalar (l .inputDimension)) (S.scalar (l .outputDimension)),∃T,
      Runs (storageBound Reg Arr M) (materialize half) S t T ∧ T.Bounded M ∧
      T.scalar (a .order)=(S.scalar (l .modulus))^(S.scalar (l .inputDimension)+S.scalar (l .outputDimension)) ∧
      T.array (.inr ())=tableWord (S.array (.inl .coefficients)) (S.scalar (l .modulus))
        (S.scalar (l .inputDimension)) (S.scalar (l .outputDimension)) half := by
  let as : List (Atom Reg Arr) := [.const (l .one) 1,.const (a .zero) 0,
    .binary .add (a .dimension) (l .inputDimension) (l .outputDimension)]
  let V := applyAtoms as S
  have valid : ValidAtoms M as S := by
    simp [as,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar,a,l]
    exact ⟨by omega,dimension⟩
  obtain ⟨first,hV⟩ := atoms_runs bounded as valid
  have powSmall : (S.scalar (l .modulus))^(S.scalar (l .inputDimension)+S.scalar (l .outputDimension))≤M := by
    have hh : (S.scalar (l .modulus))^(S.scalar (l .inputDimension)+S.scalar (l .outputDimension))≥1 :=
      one_le_pow₀ (by omega)
    nlinarith
  obtain ⟨W,t,ht,powerRun,hW,wmod,wdim,worder,wtodo,wpower⟩ := NatArrayPower.program_runs powerRegs V
    (S.scalar (l .modulus)) (S.scalar (l .inputDimension)+S.scalar (l .outputDimension)) M hV rfl
    (by simp [powerRegs,V,as,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,a,l]) (by omega) powSmall
  change W.scalar (a .order)=_ at worder
  have wframe (r : Reg) (hr : r∈({l .inputDimension,l .outputDimension,l .one,a .zero} : Finset Reg)) :
      W.scalar r=V.scalar r := by
    apply powerRun.scalar_eq_of_not_mem
    have hd : ∀r∈({l .inputDimension,l .outputDimension,l .one,a .zero} : Finset Reg),
      r∉(NatArrayPower.program powerRegs (Arr:=Arr)).scalarWrites := by decide +kernel
    exact hd r hr
  have wn : W.scalar (l .inputDimension)=S.scalar (l .inputDimension) := wframe _ (by simp)
  have wm : W.scalar (l .outputDimension)=S.scalar (l .outputDimension) := wframe _ (by simp)
  have wp : W.scalar (l .modulus)=S.scalar (l .modulus) := wmod
  have wone : W.scalar (l .one)=1 := by rw [wframe _ (by simp)];simp [V,applyAtoms,as,Atom.apply,BinaryOp.eval,Store.setScalar,a,l]
  have wz : W.scalar (a .zero)=0 := by rw [wframe _ (by simp)];simp [V,applyAtoms,as,Atom.apply,BinaryOp.eval,Store.setScalar,a,l]
  have wc : W.array (.inl .coefficients)=S.array (.inl .coefficients) :=
    (powerRun.array_eq_of_not_mem _ (by decide +kernel)).trans rfl
  let bs : List (Atom Reg Arr) := [.binary .mul (a .square) (a .order) (a .order),
    .allocate (.inr ()) (a .square) (a .zero)]
  have valid' : ValidAtoms M bs W := by
    simpa [bs,ValidAtoms,Atom.Valid,Atom.SmallResult,BinaryOp.eval,worder,pow_two] using power
  obtain ⟨allocateRun,hU⟩ := atoms_runs hW bs valid'
  let U := applyAtoms bs W
  have un : U.scalar (l .inputDimension)=S.scalar (l .inputDimension) := wn
  have um : U.scalar (l .outputDimension)=S.scalar (l .outputDimension) := wm
  have up : U.scalar (l .modulus)=S.scalar (l .modulus) := wp
  have uo : U.scalar (a .order)=(S.scalar (l .modulus))^(S.scalar (l .inputDimension)+S.scalar (l .outputDimension)) := by
    simpa [U,applyAtoms,bs,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,a,l] using worder
  have us : U.scalar (a .square)=((S.scalar (l .modulus))^(S.scalar (l .inputDimension)+S.scalar (l .outputDimension)))^2 := by
    simpa [U,applyAtoms,bs,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,a,l,pow_two] using
      congrArg (fun x=>x*x) worder
  have uc : U.array (.inl .coefficients)=S.array (.inl .coefficients) := by
    simpa [U,applyAtoms,bs,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray] using wc
  have uone : U.scalar (l .one)=1 := wone
  have output : U.array (.inr ())=List.replicate (U.scalar (a .square)) 0 := by
    simp only [a] at wz
    simp [U,applyAtoms,bs,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,a,l,wz]
  obtain ⟨u,hu,T,last,hT,result⟩ := tableLoop_runs U M half hU uone (by omega)
    (by simpa only [up] using room) (by simpa only [uc,un,um] using length)
    (by simpa only [uc,up] using small) (by omega) (by omega)
    (by simpa only [up,un,um] using powSmall) (by rw [uo];positivity) output
  have orderFrame : T.scalar (a .order)=U.scalar (a .order) := last.scalar_eq_of_not_mem _ (by
    change a .order∉(tableLoop 0).scalarWrites
    decide +kernel)
  refine ⟨3+(t+(2+u)),?_,T,.seq first (.seq powerRun (.seq allocateRun last)),hT,orderFrame.trans uo,?_⟩
  · rw [us,un,um] at hu
    unfold tableCost
    omega
  · simpa only [tableWord,tableEntry,us,uc,un,um,up,uo] using result

end GroupWL.MachinePrograms.TensorGroupProgram
