import GroupWL.MachinePrograms.DimensionScan

/-! A total operational decoder for the dimension at the end of an input word. -/
namespace GroupWL.MachinePrograms.DimensionParser
open NatArrayLanguage
open NatArrayLowering (bitNat)
variable {Reg Arr : Type*} [DecidableEq Reg] [DecidableEq Arr] [Fintype Reg] [Fintype Arr]

theorem firstBit_runs (r : Fin 9 ↪ Reg) (input : Arr)
    (S : Store Reg Arr) (w : List Bool) (pos M : ℕ) (b : Bool)
    (bounded : S.Bounded M) (room : 1≤M) (position : S.scalar (r 0)=pos)
    (length : S.scalar (r 1)=w.length) (one : S.scalar (r 7)=1) (two : S.scalar (r 8)=2)
    (inputEq : S.array input=w.map bitNat) (index : pos<w.length) (bit : w[pos]=b) :
    ∃T,Runs (storageBound Reg Arr M) (firstBit r input) S 5 T ∧ T.Bounded M ∧
      T.scalar (r 0)=pos+1 ∧ T.scalar (r 1)=w.length ∧
      T.scalar (r 2)=bitNat b ∧ T.scalar (r 3)=bitNat b ∧
      T.scalar (r 4)=(if pos+1<w.length then 1 else 0) ∧
      T.scalar (r 7)=1 ∧ T.scalar (r 8)=2 ∧ T.array input=w.map bitNat := by
  have hlen : w.length≤M := by simpa [length] using bounded.1 (r 1)
  let as : List (Atom Reg Arr) := [.read (r 5) input (r 0),.binary .add (r 0) (r 0) (r 7),
    .copy (r 2) (r 5),.copy (r 3) (r 5),.binary .lt (r 4) (r 0) (r 1)]
  have hv : ValidAtoms M as S := by
    simp [as,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,r.injective.eq_iff,position,length,one,inputEq]
    split_ifs <;> omega
  obtain ⟨run,hT⟩ := atoms_runs bounded as hv
  refine ⟨applyAtoms as S,run,hT,?_⟩
  simp [applyAtoms,as,Atom.apply,BinaryOp.eval,Store.setScalar,r.injective.eq_iff,
    position,length,one,two,inputEq,List.getElem?_eq_getElem index,bit]

theorem program_runs (e : Statement.DimensionEncoding) (r : Fin 9 ↪ Reg) (input : Arr)
    (S : Store Reg Arr) (w : List Bool) (pos M : ℕ)
    (bounded : S.Bounded M) (room : 2≤M) (position : S.scalar (r 0)=pos)
    (length : S.scalar (r 1)=w.length) (inputEq : S.array input=w.map bitNat)
    (posBound : pos≤w.length) (power : 2^(w.length+1)≤M) :
    ∃T t,t≤6*w.length+12 ∧ Runs (storageBound Reg Arr M) (program e r input) S t T ∧
      T.Bounded M ∧ T.scalar (r 0)=w.length ∧ T.scalar (r 1)=w.length ∧
      T.scalar (r 3)≤1 ∧ T.array input=w.map bitNat ∧
      Statement.readDimension e (w.drop pos)=
        if T.scalar (r 3)=0 then none else some (T.scalar (r 2)) := by
  let as : List (Atom Reg Arr) := [.const (r 2) 0,.const (r 3) 0,.const (r 7) 1,.const (r 8) 2,
    .binary .lt (r 4) (r 0) (r 1)]
  let V := applyAtoms as S
  have hv : ValidAtoms M as S := by
    simp [as,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,r.injective.eq_iff,position,length]
    split_ifs <;> omega
  obtain ⟨initRun,hV⟩ := atoms_runs bounded as hv
  have vpos : V.scalar (r 0)=pos := by simp [V,applyAtoms,as,Atom.apply,Store.setScalar,r.injective.eq_iff,position]
  have vlen : V.scalar (r 1)=w.length := by simp [V,applyAtoms,as,Atom.apply,Store.setScalar,r.injective.eq_iff,length]
  have vflag : V.scalar (r 4)=if pos<w.length then 1 else 0 := by
    simp [V,applyAtoms,as,Atom.apply,BinaryOp.eval,Store.setScalar,r.injective.eq_iff,position,length]
  have vone : V.scalar (r 7)=1 := by simp [V,applyAtoms,as,Atom.apply,Store.setScalar,r.injective.eq_iff]
  have vtwo : V.scalar (r 8)=2 := by simp [V,applyAtoms,as,Atom.apply,Store.setScalar,r.injective.eq_iff]
  have vinput : V.array input=w.map bitNat := inputEq
  cases suffix : w.drop pos with
  | nil =>
    have hp : pos=w.length := by
      have hh := congrArg List.length suffix
      simp only [List.length_drop,List.length_nil] at hh
      omega
    have vvalid : V.scalar (r 3)=0 := by simp [V,applyAtoms,as,Atom.apply,Store.setScalar,r.injective.eq_iff]
    have last : Runs (storageBound Reg Arr M) (.branch (r 4) (.seq (firstBit r input) (suffixLoop e r input)) .skip) V 1 V :=
      .branch_zero (by simp [vflag,hp]) (.skip (Store.size_le_of_bounded hV))
    refine ⟨V,6,by omega,.seq initRun last,hV,by omega,vlen,by omega,vinput,?_⟩
    cases e <;> simp [suffix,vvalid,Statement.readDimension]
  | cons b bs =>
    have index : pos<w.length := by
      have hh := congrArg List.length suffix
      simp only [List.length_drop,List.length_cons] at hh
      omega
    have bit : w[pos]=b := by
      have hh := congrArg (fun xs : List Bool=>xs[0]?) suffix
      simpa [List.getElem?_eq_getElem index] using hh
    have tail : w.drop (pos+1)=bs := by
      have hh := congrArg List.tail suffix
      simpa only [List.tail_drop,List.tail_cons] using hh
    have tailLength : bs.length+1≤w.length := by
      have hh := congrArg List.length suffix
      simp only [List.length_drop,List.length_cons] at hh
      omega
    obtain ⟨U,first,hU,upos,ulen,uvalue,uvalid,uscan,uone,utwo,uinput⟩ :=
      firstBit_runs r input V w pos M b hV (by omega) vpos vlen vone vtwo vinput index bit
    have bitSmall : bitNat b≤1 := by cases b <;> decide
    have budget : (bitNat b+1)*2^bs.length≤M+1 := by
      calc
        _ ≤ 2*2^bs.length := Nat.mul_le_mul_right _ (by omega)
        _ = 2^(bs.length+1) := by rw [pow_succ];omega
        _ ≤ 2^(w.length+1) := pow_le_pow_right' (by decide) (by omega)
        _ ≤ M+1 := by omega
    obtain ⟨T,last,hT,tpos,tlen,tvalue,tvalid,tscan,tone,ttwo,tinput⟩ :=
      suffixLoop_runs e r input bs U w (pos+1) (bitNat b) (bitNat b) M hU (by omega)
        upos ulen uvalue uvalid bitSmall uscan uone utwo uinput (by omega) tail budget
    refine ⟨T,5+(5+(6*bs.length+1)+1),by omega,
      .seq initRun (.branch_nonzero (by change V.scalar (r 4)≠0;rw [vflag];simp [index]) (.seq first last)),hT,tpos,tlen,?_,tinput,?_⟩
    · rw [tvalid];exact validFold_bound e bs (bitNat b) bitSmall
    · rw [tvalue,tvalid]
      exact parsed_suffix e b bs

end GroupWL.MachinePrograms.DimensionParser
