import GroupWL.MachinePrograms.BilinearEvaluation

/-! The complete nested-loop tensor evaluator. -/
namespace GroupWL.MachinePrograms.BilinearEvaluation

open NatArrayLanguage
open scoped BigOperators
set_option maxHeartbeats 1500000

theorem outerStep_runs (S : State) (M : ℕ) (bounded : S.Bounded M)
    (one : S.scalar .one=1) (positive : 0<S.scalar .modulus)
    (room : (S.scalar .modulus)^3+S.scalar .modulus≤M)
    (dimension : 0<S.scalar .outputDimension)
    (indices : ∀j<S.scalar .inputDimension,
      (S.scalar .outer*S.scalar .inputDimension+j)*S.scalar .outputDimension+
        S.scalar .coordinate<(S.array .coefficients).length)
    (coefficients : ∀x∈S.array .coefficients,x<S.scalar .modulus)
    (totalSmall : S.scalar .total<S.scalar .modulus) :
    ∃t≤14*S.scalar .inputDimension+6,∃T,
      Runs (storageBound Reg Arr M) outerStep S t T ∧ T.Bounded M ∧
      T.scalar .leftRest=S.scalar .leftRest/S.scalar .modulus ∧
      T.scalar .total=rowSum (S.array .coefficients) (S.scalar .modulus)
        (S.scalar .inputDimension) (S.scalar .outputDimension) (S.scalar .outer)
        (S.scalar .coordinate) (S.scalar .leftRest%S.scalar .modulus) (S.scalar .right)
        (S.scalar .total) (S.scalar .inputDimension) := by
  let as : List (Atom Reg Arr) := [.divmod .quotient .leftDigit .leftRest .modulus,.copy .leftRest .quotient]
  let U := applyAtoms as S
  obtain ⟨first,hU⟩ := atoms_runs bounded as
    (by simp [as,ValidAtoms,Atom.Valid,Atom.SmallResult,positive])
  have inputEq (r : Reg) (hr : r≠.leftRest ∧ r≠.leftDigit ∧ r≠.quotient) : U.scalar r=S.scalar r := by
    simp [U,applyAtoms,as,Atom.apply,Store.setScalar,hr.1,hr.2.1,hr.2.2]
  have ur : U.scalar .leftRest=S.scalar .leftRest/S.scalar .modulus := by
    simp [U,applyAtoms,as,Atom.apply,Store.setScalar]
  have ud : U.scalar .leftDigit=S.scalar .leftRest%S.scalar .modulus := by
    simp [U,applyAtoms,as,Atom.apply,Store.setScalar]
  have ua : U.array .coefficients=S.array .coefficients := rfl
  have un := inputEq .inputDimension (by decide)
  have um := inputEq .outputDimension (by decide)
  have uo := inputEq .outer (by decide)
  have uz := inputEq .coordinate (by decide)
  have uy := inputEq .right (by decide)
  have up := inputEq .modulus (by decide)
  have ut := inputEq .total (by decide)
  obtain ⟨t,ht,T,last,hT,acc⟩ := row_runs U M hU
    ((inputEq .one (by decide)).trans one) (by omega) (by rwa [up]) (by omega)
    (by simpa only [un,um,uo,uz,ua] using indices)
    (by simpa only [ua,up] using coefficients)
    (by rw [ud,up]; exact Nat.mod_lt _ positive) (by omega)
  refine ⟨2+t,by omega,T,.seq first last,hT,?_,?_⟩
  · rw [last.scalar_eq_of_not_mem .leftRest]
    · exact ur
    · simp [row,rowStep,atoms,rowStepAtoms,countedLoop,NatArrayLanguage.sequence,Program.scalarWrites,Atom.scalarWrites]
  · simpa only [ua,up,un,um,uo,uz,ud,uy,ut] using acc

def partialValue (C : List ℕ) (p n m x y z i : ℕ) : ℕ :=
  (∑ a ∈ Finset.range i,∑ b ∈ Finset.range n,
    read C ((a*n+b)*m+z)*digit p x a*digit p y b)%p

@[simp] theorem partialValue_zero (C : List ℕ) (p n m x y z : ℕ) :
    partialValue C p n m x y z 0=0 := by simp [partialValue]

theorem partialValue_succ (C : List ℕ) (p n m x y z i : ℕ) :
    partialValue C p n m x y z (i+1)=
      rowSum C p n m i z (digit p x i) y (partialValue C p n m x y z i) n := by
  simp only [partialValue,rowSum,Finset.sum_range_succ]
  exact (Nat.mod_add_mod _ _ _).symm

def evalInputs : Finset Reg := {.inputDimension,.outputDimension,.left,.right,.coordinate,.modulus}

structure EvalState (S : State) (M i : ℕ) (T : State) : Prop where
  bounded : T.Bounded M
  inputs : ∀r∈evalInputs,T.scalar r=S.scalar r
  one : T.scalar .one=1
  coefficients : T.array .coefficients=S.array .coefficients
  index : T.scalar .outer=i
  remaining : T.scalar .outerTodo=S.scalar .inputDimension-i
  leftRest : T.scalar .leftRest=S.scalar .left/(S.scalar .modulus)^i
  accumulator : T.scalar .total=partialValue (S.array .coefficients) (S.scalar .modulus)
    (S.scalar .inputDimension) (S.scalar .outputDimension) (S.scalar .left) (S.scalar .right)
    (S.scalar .coordinate) i

theorem evaluate_runs (S : State) (M : ℕ) (bounded : S.Bounded M)
    (positive : 0<S.scalar .modulus)
    (room : (S.scalar .modulus)^3+S.scalar .modulus≤M)
    (coordinate : S.scalar .coordinate<S.scalar .outputDimension)
    (length : (S.array .coefficients).length=
      S.scalar .inputDimension*S.scalar .inputDimension*S.scalar .outputDimension)
    (coefficients : ∀x∈S.array .coefficients,x<S.scalar .modulus) :
    ∃t≤14*(S.scalar .inputDimension)^2+9*S.scalar .inputDimension+6,∃T,
      Runs (storageBound Reg Arr M) evaluate S t T ∧ T.Bounded M ∧
      T.scalar .total=partialValue (S.array .coefficients) (S.scalar .modulus)
        (S.scalar .inputDimension) (S.scalar .outputDimension) (S.scalar .left) (S.scalar .right)
        (S.scalar .coordinate) (S.scalar .inputDimension) := by
  have hM : 1≤M := by omega
  let as : List (Atom Reg Arr) := [.const .one 1,.const .total 0,.copy .leftRest .left]
  let S₀ := applyAtoms as S
  obtain ⟨first,h₀⟩ := atoms_runs bounded as (by simp [as,ValidAtoms,Atom.Valid,Atom.SmallResult,hM])
  let S₁ := S₀.setScalar .outerTodo (S.scalar .inputDimension)
  let S₂ := S₁.setScalar .outer 0
  have h₁ : S₁.Bounded M := h₀.setScalar _ (bounded.1 .inputDimension)
  have h₂ : S₂.Bounded M := h₁.setScalar _ (by omega)
  have start : EvalState S M 0 S₂ := by
    refine ⟨h₂,?_,?_,rfl,?_,?_,?_,?_⟩
    · intro r hr
      have hd : ∀r∈evalInputs,r≠Reg.outer ∧ r≠Reg.outerTodo ∧ r≠Reg.one ∧ r≠Reg.total ∧ r≠Reg.leftRest := by decide
      obtain ⟨ho,ht,h1,h0,hl⟩ := hd r hr
      simp [S₂,S₁,S₀,applyAtoms,as,Atom.apply,Store.setScalar,ho,ht,h1,h0,hl]
    · simp [S₂,S₁,S₀,applyAtoms,as,Atom.apply,Store.setScalar]
    · simp [S₂]
    · simp [S₂,S₁]
    · simp [S₂,S₁,S₀,applyAtoms,as,Atom.apply,Store.setScalar]
    · simp [S₂,S₁,S₀,applyAtoms,as,Atom.apply,Store.setScalar]
  have control : ∀i≤S.scalar .inputDimension,∀T,EvalState S M i T →
      T.scalar .outer=i ∧ T.scalar .outerTodo=S.scalar .inputDimension-i ∧
      T.scalar .one=1 ∧ T.size≤storageBound Reg Arr M := by
    intro i hi T hT
    exact ⟨hT.index,hT.remaining,hT.one,Store.size_le_of_bounded hT.bounded⟩
  have step : ∀i<S.scalar .inputDimension,∀T,EvalState S M i T →
      ∃t≤14*S.scalar .inputDimension+6,∃U,Runs (storageBound Reg Arr M) outerStep T t U ∧
        U.scalar .outer=i ∧ U.scalar .outerTodo=S.scalar .inputDimension-i ∧ U.scalar .one=1 ∧
        (U.setScalar .outer (i+1)).size≤storageBound Reg Arr M ∧
        EvalState S M (i+1) (advance .outer .outerTodo U) := by
    intro i hi T hT
    have hn := hT.inputs .inputDimension (by decide)
    have hm := hT.inputs .outputDimension (by decide)
    have hx := hT.inputs .left (by decide)
    have hy := hT.inputs .right (by decide)
    have hz := hT.inputs .coordinate (by decide)
    have hp := hT.inputs .modulus (by decide)
    have hindices : ∀j<T.scalar .inputDimension,
        (T.scalar .outer*T.scalar .inputDimension+j)*T.scalar .outputDimension+
          T.scalar .coordinate<(T.array .coefficients).length := by
      intro j hj
      rw [hn] at hj
      rw [hT.index,hn,hm,hz,hT.coefficients,length]
      have hrow : i*S.scalar .inputDimension+j<S.scalar .inputDimension*S.scalar .inputDimension := by nlinarith
      nlinarith
    obtain ⟨t,ht,U,run,bound,hrest,acc⟩ := outerStep_runs T M hT.bounded hT.one (by omega)
      (by rwa [hp]) (by omega) hindices (by simpa only [hT.coefficients,hp] using coefficients)
      (by rw [hT.accumulator,hp]; exact Nat.mod_lt _ positive)
    have frame (r : Reg) (hr : r∈evalInputs ∨ r=.one ∨ r=.outer ∨ r=.outerTodo) : U.scalar r=T.scalar r := by
      apply run.scalar_eq_of_not_mem
      have hdis : ∀r∈evalInputs,r∉outerStep.scalarWrites := by decide
      rcases hr with hr | hr | hr | hr
      · exact hdis r hr
      · subst r; decide
      · subst r; decide
      · subst r; decide
    have hmid : (U.setScalar .outer (i+1)).Bounded M :=
      bound.setScalar _ ((by omega : i+1≤S.scalar .inputDimension).trans (bounded.1 .inputDimension))
    have hix : U.scalar .outer=i := (frame .outer (by simp)).trans hT.index
    have hrem : U.scalar .outerTodo=S.scalar .inputDimension-i := (frame .outerTodo (by simp)).trans hT.remaining
    have hone : U.scalar .one=1 := (frame .one (by simp)).trans hT.one
    have hfinal : (advance .outer .outerTodo U).Bounded M := by
      simpa only [advance,hix] using hmid.setScalar Reg.outerTodo
        ((Nat.sub_le _ _).trans (bound.1 .outerTodo))
    refine ⟨t,by omega,U,run,hix,hrem,hone,Store.size_le_of_bounded hmid,
      hfinal,?_,?_,?_,?_,?_,?_,?_⟩
    · intro r hr
      have hdis : ∀r∈evalInputs,r≠Reg.outer ∧ r≠Reg.outerTodo := by decide
      have he := (frame r (Or.inl hr)).trans (hT.inputs r hr)
      simpa [advance,Store.setScalar,(hdis r hr).1,(hdis r hr).2] using he
    · simpa [advance,Store.setScalar] using hone
    · exact (run.array_eq_of_not_mem .coefficients (by
        simp [outerStep,row,rowStep,atoms,rowStepAtoms,countedLoop,NatArrayLanguage.sequence,
          Program.arrayWrites,Atom.arrayWrites])).trans hT.coefficients
    · simp [advance,Store.setScalar,hix]
    · simp [advance,Store.setScalar,hrem,Nat.sub_sub]
    · change U.scalar .leftRest=_
      rw [hrest,hT.leftRest,hp,Nat.div_div_eq_div_mul,pow_succ]
    · change U.scalar .total=_
      rw [acc,hT.coefficients,hp,hn,hm,hT.index,hz,hT.leftRest,hy,hT.accumulator]
      exact (partialValue_succ _ _ _ _ _ _ _ _).symm
  obtain ⟨t,ht,T,run,hT⟩ := countedLoop_runs (storageBound Reg Arr M)
    Reg.outer Reg.outerTodo Reg.inputDimension Reg.one outerStep (S.scalar .inputDimension)
    (14*S.scalar .inputDimension+6) (EvalState S M) S₀
    (Store.size_le_of_bounded h₀) (Store.size_le_of_bounded h₁) start control (by decide) (by decide) step
  refine ⟨3+t,by nlinarith,T,.seq first run,hT.bounded,hT.accumulator⟩

end GroupWL.MachinePrograms.BilinearEvaluation
