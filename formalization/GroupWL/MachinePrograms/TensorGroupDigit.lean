import GroupWL.MachinePrograms.TensorGroupProgram

/-! One base-p digit of the concrete tensor-group product. -/
namespace GroupWL.MachinePrograms.TensorGroupProgram
open NatArrayLanguage
open BilinearEvaluation (digit partialValue)
open TensorGroupCode (multiplicationDigit)

theorem prepareDigits_runs (S : State) (M : ℕ) (bounded : S.Bounded M)
    (positive : 0<S.scalar (l .modulus))
    (room : 2*S.scalar (l .modulus)≤M) :
    Runs (storageBound Reg Arr M) (atoms prepareDigits) S 6 (applyAtoms prepareDigits S) ∧
      (applyAtoms prepareDigits S).Bounded M := by
  have hx := Nat.mod_lt (S.scalar (a .leftRest)) positive
  have hy := Nat.mod_lt (S.scalar (a .rightRest)) positive
  simp only [a,l] at positive room hx hy
  have valid : ValidAtoms M prepareDigits S := by
    simp [prepareDigits,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,a,l]
    exact ⟨positive,by omega,by split <;> omega⟩
  exact atoms_runs bounded prepareDigits valid

theorem finishDigit_runs (S : State) (M : ℕ) (bounded : S.Bounded M)
    (positive : 0<S.scalar (l .modulus))
    (accumulator : S.scalar (a .result)<S.scalar (a .place))
    (room : S.scalar (a .place)*S.scalar (l .modulus)≤M) :
    Runs (storageBound Reg Arr M) (atoms finishDigit) S 4 (applyAtoms finishDigit S) ∧
      (applyAtoms finishDigit S).Bounded M ∧
      (applyAtoms finishDigit S).scalar (a .result)=S.scalar (a .result)+
        (S.scalar (a .term)%S.scalar (l .modulus))*S.scalar (a .place) ∧
      (applyAtoms finishDigit S).scalar (a .place)=S.scalar (a .place)*S.scalar (l .modulus) := by
  have hd := Nat.mod_lt (S.scalar (a .term)) positive
  simp only [a,l] at positive accumulator room hd
  have valid : ValidAtoms M finishDigit S := by
    simp [finishDigit,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,a,l]
    exact ⟨positive,by nlinarith,by nlinarith,room⟩
  obtain ⟨run,hT⟩ := atoms_runs bounded finishDigit valid
  refine ⟨run,hT,?_,?_⟩ <;>
    simp [applyAtoms,finishDigit,Atom.apply,BinaryOp.eval,Store.setScalar,a,l]

theorem step_runs (S : State) (M i : ℕ) (bounded : S.Bounded M)
    (one : S.scalar (l .one)=1) (positive : 0<S.scalar (l .modulus))
    (room : (S.scalar (l .modulus))^3+3*S.scalar (l .modulus)≤M)
    (length : (S.array (.inl .coefficients)).length=
      S.scalar (l .inputDimension)*S.scalar (l .inputDimension)*S.scalar (l .outputDimension))
    (small : ∀x∈S.array (.inl .coefficients),x<S.scalar (l .modulus))
    (half : S.scalar (a .half)<S.scalar (l .modulus))
    (index : S.scalar (a .index)=i)
    (ilimit : i<S.scalar (l .inputDimension)+S.scalar (l .outputDimension))
    (leftRest : S.scalar (a .leftRest)=S.scalar (l .left)/(S.scalar (l .modulus))^i)
    (rightRest : S.scalar (a .rightRest)=S.scalar (l .right)/(S.scalar (l .modulus))^i)
    (accumulator : S.scalar (a .result)<S.scalar (a .place))
    (place : S.scalar (a .place)*S.scalar (l .modulus)≤M) :
    ∃t≤14*(S.scalar (l .inputDimension))^2+9*S.scalar (l .inputDimension)+20,∃T,
      Runs (storageBound Reg Arr M) step S t T ∧ T.Bounded M ∧ T.scalar (l .one)=1 ∧
      T.scalar (a .result)=S.scalar (a .result)+multiplicationDigit
        (S.array (.inl .coefficients)) (S.scalar (l .modulus)) (S.scalar (l .inputDimension))
        (S.scalar (l .outputDimension)) (S.scalar (a .half)) (S.scalar (l .left))
        (S.scalar (l .right)) i*S.scalar (a .place) ∧
      T.scalar (a .place)=S.scalar (a .place)*S.scalar (l .modulus) ∧
      T.scalar (a .leftRest)=S.scalar (a .leftRest)/S.scalar (l .modulus) ∧
      T.scalar (a .rightRest)=S.scalar (a .rightRest)/S.scalar (l .modulus) := by
  let V := applyAtoms prepareDigits S
  obtain ⟨first,hV⟩ := prepareDigits_runs S M bounded positive (by omega)
  have frames : ∀ r, r∉({a .quotient,a .leftDigit,a .leftRest,a .rightDigit,a .rightRest,a .term,a .flag} : Finset Reg) →
      V.scalar r=S.scalar r := by
    intro r hr
    apply first.scalar_eq_of_not_mem r
    simp [prepareDigits,atoms,NatArrayLanguage.sequence,Program.scalarWrites,Atom.scalarWrites] at *
    tauto
  have vinput := frames (l .inputDimension) (by decide)
  have voutput := frames (l .outputDimension) (by decide)
  have vmod := frames (l .modulus) (by decide)
  have vone := (frames (l .one) (by decide)).trans one
  have vhalf := frames (a .half) (by decide)
  have vindex := (frames (a .index) (by decide)).trans index
  have vresult := frames (a .result) (by decide)
  have vplace := frames (a .place) (by decide)
  have vleft := frames (l .left) (by decide)
  have vright := frames (l .right) (by decide)
  have vcoeff : V.array (.inl .coefficients)=S.array (.inl .coefficients) := rfl
  have vterm : V.scalar (a .term)=digit (S.scalar (l .modulus)) (S.scalar (l .left)) i+
      digit (S.scalar (l .modulus)) (S.scalar (l .right)) i := by
    simp [V,applyAtoms,prepareDigits,Atom.apply,BinaryOp.eval,Store.setScalar,a,l,digit]
    exact congrArg₂ (fun x y =>x%S.scalar (.inl .modulus)+y%S.scalar (.inl .modulus)) leftRest rightRest
  have vflag : V.scalar (a .flag)=if i<S.scalar (l .inputDimension) then 1 else 0 := by
    simpa [V,applyAtoms,prepareDigits,Atom.apply,BinaryOp.eval,Store.setScalar,a,l] using
      congrArg (fun x =>if x<S.scalar (.inl .inputDimension) then 1 else 0) index
  have vx := Nat.mod_lt (S.scalar (l .left)/(S.scalar (l .modulus))^i) positive
  have vy := Nat.mod_lt (S.scalar (l .right)/(S.scalar (l .modulus))^i) positive
  have intermediate : ∃t≤14*(S.scalar (l .inputDimension))^2+9*S.scalar (l .inputDimension)+10,∃W,
      Runs (storageBound Reg Arr M) (.branch (a .flag) .skip central) V t W ∧ W.Bounded M ∧
      W.scalar (l .one)=1 ∧
      W.scalar (a .term)%S.scalar (l .modulus)=multiplicationDigit (S.array (.inl .coefficients))
        (S.scalar (l .modulus)) (S.scalar (l .inputDimension)) (S.scalar (l .outputDimension))
        (S.scalar (a .half)) (S.scalar (l .left)) (S.scalar (l .right)) i := by
    by_cases hi : i<S.scalar (l .inputDimension)
    · refine ⟨1,by omega,V,.branch_nonzero (by simpa [vflag,hi]) (.skip (Store.size_le_of_bounded hV)),hV,vone,?_⟩
      simp [vterm,multiplicationDigit,hi]
    · obtain ⟨t,ht,W,run,hW,wone,wterm⟩ := central_runs V M hV
        (by simpa [vmod] using positive) (by simpa [vmod] using room)
        (by rw [vindex,vinput,voutput];omega) (by simpa [vcoeff,vinput,voutput] using length)
        (by simpa [vcoeff,vmod] using small) (by simpa [vhalf,vmod] using half)
        (by rw [vterm,vmod];simp only [digit];omega)
      refine ⟨t+1,by rw [vinput] at ht;omega,W,.branch_zero (by simp [vflag,hi]) run,hW,wone,?_⟩
      rw [wterm,vterm,vhalf,vcoeff,vmod,vinput,voutput,vleft,vright,vindex]
      simp [multiplicationDigit,hi]
  obtain ⟨t,ht,W,middle,hW,wone,wterm⟩ := intermediate
  have wf : ∀r∈({a .result,a .place,l .modulus,a .leftRest,a .rightRest} : Finset Reg),
      W.scalar r=V.scalar r := by
    intro r hr
    apply middle.scalar_eq_of_not_mem
    rcases (by simpa only [Finset.mem_insert,Finset.mem_singleton] using hr) with h|h|h|h|h <;>
      subst r <;>
      decide +kernel
  have wr := (wf (a .result) (by simp)).trans vresult
  have wp := (wf (a .place) (by simp)).trans vplace
  have wm := (wf (l .modulus) (by simp)).trans vmod
  obtain ⟨last,hT,result,places⟩ := finishDigit_runs W M hW (by omega) (by omega) (by simpa [wp,wm] using place)
  refine ⟨6+(t+4),by omega,applyAtoms finishDigit W,.seq first (.seq middle last),hT,?_,?_,?_,?_,?_⟩
  · exact (last.scalar_eq_of_not_mem (l .one) (by decide +kernel)).trans wone
  · rw [result,wr,wp,wm,wterm]
  · rw [places,wp,wm]
  · have hh := (last.scalar_eq_of_not_mem (r:=a .leftRest) (by decide +kernel)).trans
        (wf (a .leftRest) (by simp))
    simpa [V,applyAtoms,prepareDigits,Atom.apply,BinaryOp.eval,Store.setScalar,a,l] using hh
  · have hh := (last.scalar_eq_of_not_mem (r:=a .rightRest) (by decide +kernel)).trans
        (wf (a .rightRest) (by simp))
    simpa [V,applyAtoms,prepareDigits,Atom.apply,BinaryOp.eval,Store.setScalar,a,l] using hh

end GroupWL.MachinePrograms.TensorGroupProgram
