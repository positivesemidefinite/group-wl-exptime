import GroupWL.MachinePrograms.TensorGroupDigit

/-! Counted execution of the full base-p product loop. -/
namespace GroupWL.MachinePrograms.TensorGroupProgram
open NatArrayLanguage
open BilinearEvaluation (digit partialValue)
open TensorGroupCode

def productInputs : Finset Reg :=
  {l .inputDimension,l .outputDimension,l .modulus,l .left,l .right,a .half,a .dimension}

def productDigits (S : State) : ℕ → ℕ := multiplicationDigit (S.array (.inl .coefficients))
  (S.scalar (l .modulus)) (S.scalar (l .inputDimension)) (S.scalar (l .outputDimension))
  (S.scalar (a .half)) (S.scalar (l .left)) (S.scalar (l .right))

structure ProductState (S : State) (M i : ℕ) (T : State) : Prop where
  bounded : T.Bounded M
  inputs : ∀r∈productInputs,T.scalar r=S.scalar r
  one : T.scalar (l .one)=1
  coefficients : T.array (.inl .coefficients)=S.array (.inl .coefficients)
  index : T.scalar (a .index)=i
  remaining : T.scalar (a .remaining)=S.scalar (a .dimension)-i
  leftRest : T.scalar (a .leftRest)=S.scalar (l .left)/(S.scalar (l .modulus))^i
  rightRest : T.scalar (a .rightRest)=S.scalar (l .right)/(S.scalar (l .modulus))^i
  place : T.scalar (a .place)=(S.scalar (l .modulus))^i
  result : T.scalar (a .result)=codePrefix (S.scalar (l .modulus)) (productDigits S) i

def productLoop : Code := countedLoop (a .index) (a .remaining) (a .dimension) (l .one) step

theorem productLoop_runs (S : State) (M : ℕ) (bounded : S.Bounded M)
    (one : S.scalar (l .one)=1) (positive : 0<S.scalar (l .modulus))
    (room : (S.scalar (l .modulus))^3+3*S.scalar (l .modulus)≤M)
    (length : (S.array (.inl .coefficients)).length=
      S.scalar (l .inputDimension)*S.scalar (l .inputDimension)*S.scalar (l .outputDimension))
    (small : ∀x∈S.array (.inl .coefficients),x<S.scalar (l .modulus))
    (half : S.scalar (a .half)<S.scalar (l .modulus))
    (dimension : S.scalar (a .dimension)=S.scalar (l .inputDimension)+S.scalar (l .outputDimension))
    (power : (S.scalar (l .modulus))^(S.scalar (a .dimension))≤M)
    (leftRest : S.scalar (a .leftRest)=S.scalar (l .left))
    (rightRest : S.scalar (a .rightRest)=S.scalar (l .right))
    (place : S.scalar (a .place)=1) (result : S.scalar (a .result)=0) :
    ∃t≤S.scalar (a .dimension)*(14*(S.scalar (l .inputDimension))^2+
        9*S.scalar (l .inputDimension)+23)+3,∃T,
      Runs (storageBound Reg Arr M) productLoop S t T ∧ T.Bounded M ∧
      T.scalar (l .one)=1 ∧ T.scalar (a .result)=multiplication
        (S.array (.inl .coefficients)) (S.scalar (l .modulus)) (S.scalar (l .inputDimension))
        (S.scalar (l .outputDimension)) (S.scalar (a .half)) (S.scalar (l .left)) (S.scalar (l .right)) := by
  let S₀ := S.setScalar (a .remaining) (S.scalar (a .dimension))
  let S₁ := S₀.setScalar (a .index) 0
  have h₀ : S₀.Bounded M := bounded.setScalar _ (bounded.1 (a .dimension))
  have h₁ : S₁.Bounded M := h₀.setScalar _ (by omega)
  have start : ProductState S M 0 S₁ := by
    refine ⟨h₁,?_,?_,rfl,?_,?_,?_,?_,?_,?_⟩
    · intro r hr
      have hd : ∀r∈productInputs,r≠a .remaining ∧ r≠a .index := by decide
      simp [S₁,S₀,Store.setScalar,(hd r hr).1,(hd r hr).2]
    · simpa [S₁,S₀,Store.setScalar,a,l] using one
    · simp [S₁]
    · simp [S₁,S₀,Store.setScalar,a,l]
    · simpa [S₁,S₀,Store.setScalar,a,l] using leftRest
    · simpa [S₁,S₀,Store.setScalar,a,l] using rightRest
    · simpa [S₁,S₀,Store.setScalar,a,l] using place
    · simpa [S₁,S₀,Store.setScalar,a,l] using result
  have control : ∀i≤S.scalar (a .dimension),∀T,ProductState S M i T →
      T.scalar (a .index)=i ∧ T.scalar (a .remaining)=S.scalar (a .dimension)-i ∧
      T.scalar (l .one)=1 ∧ T.size≤storageBound Reg Arr M := by
    intro i hi T hT
    exact ⟨hT.index,hT.remaining,hT.one,Store.size_le_of_bounded hT.bounded⟩
  have body : ∀i<S.scalar (a .dimension),∀T,ProductState S M i T →
      ∃t≤14*(S.scalar (l .inputDimension))^2+9*S.scalar (l .inputDimension)+20,∃U,
        Runs (storageBound Reg Arr M) step T t U ∧ U.scalar (a .index)=i ∧
        U.scalar (a .remaining)=S.scalar (a .dimension)-i ∧ U.scalar (l .one)=1 ∧
        (U.setScalar (a .index) (i+1)).size≤storageBound Reg Arr M ∧
        ProductState S M (i+1) (advance (a .index) (a .remaining) U) := by
    intro i hi T hT
    have hn := hT.inputs (l .inputDimension) (by decide)
    have hm := hT.inputs (l .outputDimension) (by decide)
    have hp := hT.inputs (l .modulus) (by decide)
    have hh := hT.inputs (a .half) (by decide)
    have hx := hT.inputs (l .left) (by decide)
    have hy := hT.inputs (l .right) (by decide)
    have hpnext : (S.scalar (l .modulus))^(i+1)≤M :=
      (pow_le_pow_right' (by omega) (by omega : i+1≤S.scalar (a .dimension))).trans power
    obtain ⟨t,ht,U,run,hU,uone,uresult,uplace,ul,ur⟩ := step_runs T M i hT.bounded hT.one
      (by omega) (by simpa only [hp] using room)
      (by simpa only [hT.coefficients,hn,hm] using length)
      (by simpa only [hT.coefficients,hp] using small) (by omega) hT.index (by omega)
      (by simpa only [hx,hp] using hT.leftRest) (by simpa only [hy,hp] using hT.rightRest)
      (by rw [hT.result,hT.place];exact codePrefix_lt _ _ _ positive (fun _ _ =>Nat.mod_lt _ positive))
      (by simpa only [hT.place,hp,pow_succ] using hpnext)
    have frame (r : Reg) (hr : r∈productInputs ∨ r=a .index ∨ r=a .remaining) : U.scalar r=T.scalar r := by
      apply run.scalar_eq_of_not_mem
      have hd : ∀r∈productInputs,r∉step.scalarWrites := by decide +kernel
      rcases hr with hr|hr|hr
      · exact hd r hr
      · subst r;decide +kernel
      · subst r;decide +kernel
    have ix : U.scalar (a .index)=i := (frame _ (by simp)).trans hT.index
    have rem : U.scalar (a .remaining)=S.scalar (a .dimension)-i := (frame _ (by simp)).trans hT.remaining
    have mid : (U.setScalar (a .index) (i+1)).Bounded M :=
      hU.setScalar _ ((by omega : i+1≤S.scalar (a .dimension)).trans (bounded.1 (a .dimension)))
    have final : (advance (a .index) (a .remaining) U).Bounded M := by
      simpa only [advance,ix] using mid.setScalar (a .remaining)
        ((Nat.sub_le _ _).trans (hU.1 (a .remaining)))
    refine ⟨t,by simpa only [hn] using ht,U,run,ix,rem,uone,Store.size_le_of_bounded mid,final,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · intro r hr
      have hd : ∀r∈productInputs,r≠a .index ∧ r≠a .remaining := by decide
      simpa [advance,Store.setScalar,(hd r hr).1,(hd r hr).2] using
        (frame r (Or.inl hr)).trans (hT.inputs r hr)
    · simpa [advance,Store.setScalar,a,l] using uone
    · exact (run.array_eq_of_not_mem _ (by decide +kernel)).trans hT.coefficients
    · simpa [advance,Store.setScalar,a,l] using ix
    · simpa [advance,Store.setScalar,a,l,Nat.sub_sub] using congrArg (fun n=>n-1) rem
    · change U.scalar (a .leftRest)=_
      rw [ul,hT.leftRest,hp,Nat.div_div_eq_div_mul,pow_succ]
    · change U.scalar (a .rightRest)=_
      rw [ur,hT.rightRest,hp,Nat.div_div_eq_div_mul,pow_succ]
    · change U.scalar (a .place)=_
      rw [uplace,hT.place,hp,pow_succ]
    · change U.scalar (a .result)=_
      rw [uresult,hT.result,hT.coefficients,hp,hn,hm,hh,hx,hy,hT.place,codePrefix_succ]
      rfl
  obtain ⟨t,ht,T,run,hT⟩ := countedLoop_runs (storageBound Reg Arr M)
    (a .index) (a .remaining) (a .dimension) (l .one) step
    (S.scalar (a .dimension)) (14*(S.scalar (l .inputDimension))^2+9*S.scalar (l .inputDimension)+20)
    (ProductState S M) S (Store.size_le_of_bounded bounded) (Store.size_le_of_bounded h₀)
    start control (by decide) (by decide) body
  refine ⟨t,by omega,T,run,hT.bounded,hT.one,?_⟩
  simpa only [dimension,multiplication,productDigits] using hT.result

theorem product_runs (S : State) (M half : ℕ) (bounded : S.Bounded M)
    (positive : 0<S.scalar (l .modulus))
    (room : (S.scalar (l .modulus))^3+3*S.scalar (l .modulus)≤M)
    (length : (S.array (.inl .coefficients)).length=
      S.scalar (l .inputDimension)*S.scalar (l .inputDimension)*S.scalar (l .outputDimension))
    (small : ∀x∈S.array (.inl .coefficients),x<S.scalar (l .modulus))
    (halfSmall : half<S.scalar (l .modulus))
    (dimension : S.scalar (l .inputDimension)+S.scalar (l .outputDimension)≤M)
    (power : (S.scalar (l .modulus))^(S.scalar (l .inputDimension)+S.scalar (l .outputDimension))≤M) :
    ∃t≤(S.scalar (l .inputDimension)+S.scalar (l .outputDimension))*
        (14*(S.scalar (l .inputDimension))^2+9*S.scalar (l .inputDimension)+23)+10,∃T,
      Runs (storageBound Reg Arr M) (product half) S t T ∧ T.Bounded M ∧
      T.scalar (l .one)=1 ∧ T.scalar (a .result)=multiplication
        (S.array (.inl .coefficients)) (S.scalar (l .modulus)) (S.scalar (l .inputDimension))
        (S.scalar (l .outputDimension)) half (S.scalar (l .left)) (S.scalar (l .right)) := by
  let as : List (Atom Reg Arr) := [
    .const (l .one) 1,.const (a .result) 0,.const (a .place) 1,.const (a .half) half,
    .copy (a .leftRest) (l .left),.copy (a .rightRest) (l .right),
    .binary .add (a .dimension) (l .inputDimension) (l .outputDimension)]
  let V := applyAtoms as S
  have valid : ValidAtoms M as S := by
    simp [as,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar,a,l]
    exact ⟨by omega,by omega,dimension⟩
  obtain ⟨first,hV⟩ := atoms_runs bounded as valid
  have hinput : V.scalar (l .inputDimension)=S.scalar (l .inputDimension) := rfl
  have houtput : V.scalar (l .outputDimension)=S.scalar (l .outputDimension) := rfl
  have hmod : V.scalar (l .modulus)=S.scalar (l .modulus) := rfl
  have hdimension : V.scalar (a .dimension)=S.scalar (l .inputDimension)+S.scalar (l .outputDimension) := by
    simp [V,as,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,a,l]
  have halfeq : V.scalar (a .half)=half := by simp [V,as,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,a,l]
  obtain ⟨t,ht,T,last,hT,one,result⟩ := productLoop_runs V M hV
    (by simp [V,as,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,a,l])
    positive room length small (by rw [halfeq,hmod];exact halfSmall)
    (by rw [hdimension,hinput,houtput]) (by rwa [hmod,hdimension])
    (by simp [V,as,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,a,l])
    (by simp [V,as,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,a,l])
    (by simp [V,as,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,a,l])
    (by simp [V,as,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,a,l])
  refine ⟨7+t,by rw [hdimension,hinput] at ht;omega,T,.seq first last,hT,one,?_⟩
  simpa [V,as,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,a,l] using result

end GroupWL.MachinePrograms.TensorGroupProgram
