import GroupWL.MachinePrograms.AlternationCheck

/-! Counted validation of all coordinates of one self-product. -/
namespace GroupWL.MachinePrograms.AlternationCheck

open NatArrayLanguage

def coordinateInputs : Finset Reg :=
  {l .inputDimension,l .outputDimension,l .left,l .right,l .modulus,a .zero}

structure CoordinateState (S : State) (M j : ℕ) (T : State) : Prop where
  bounded : T.Bounded M
  inputs : ∀r∈coordinateInputs,T.scalar r=S.scalar r
  one : T.scalar (l .one)=1
  coefficients : T.array (.inl .coefficients)=S.array (.inl .coefficients)
  index : T.scalar (l .coordinate)=j
  remaining : T.scalar (a .coordinateTodo)=S.scalar (l .outputDimension)-j
  validity : T.scalar (a .valid)=S.scalar (a .valid)*coordinateProduct
    (S.array (.inl .coefficients)) (S.scalar (l .modulus)) (S.scalar (l .inputDimension))
    (S.scalar (l .outputDimension)) (S.scalar (l .left)) j

theorem coordinates_runs (S : State) (M : ℕ) (bounded : S.Bounded M)
    (one : S.scalar (l .one)=1) (positive : 0<S.scalar (l .modulus))
    (room : (S.scalar (l .modulus))^3+S.scalar (l .modulus)≤M)
    (length : (S.array (.inl .coefficients)).length=
      S.scalar (l .inputDimension)*S.scalar (l .inputDimension)*S.scalar (l .outputDimension))
    (small : ∀x∈S.array (.inl .coefficients),x<S.scalar (l .modulus))
    (right : S.scalar (l .right)=S.scalar (l .left))
    (valid : S.scalar (a .valid)≤1) (zero : S.scalar (a .zero)=0) :
    ∃t≤S.scalar (l .outputDimension)*(14*(S.scalar (l .inputDimension))^2+
        9*S.scalar (l .inputDimension)+11)+3,∃T,
      Runs (storageBound Reg Arr M) coordinates S t T ∧ T.Bounded M ∧
      T.scalar (l .one)=1 ∧ T.scalar (a .valid)=S.scalar (a .valid)*coordinateProduct
        (S.array (.inl .coefficients)) (S.scalar (l .modulus)) (S.scalar (l .inputDimension))
        (S.scalar (l .outputDimension)) (S.scalar (l .left)) (S.scalar (l .outputDimension)) := by
  let S₀ := S.setScalar (a .coordinateTodo) (S.scalar (l .outputDimension))
  let S₁ := S₀.setScalar (l .coordinate) 0
  have h₀ : S₀.Bounded M := bounded.setScalar _ (bounded.1 (l .outputDimension))
  have h₁ : S₁.Bounded M := h₀.setScalar _ (by omega)
  have start : CoordinateState S M 0 S₁ := by
    refine ⟨h₁,?_,?_,rfl,?_,?_,?_⟩
    · intro r hr
      have hd : ∀r∈coordinateInputs,r≠l .coordinate ∧ r≠a .coordinateTodo := by decide
      simp [S₁,S₀,Store.setScalar,(hd r hr).1,(hd r hr).2]
    · simpa [S₁,S₀,Store.setScalar,a,l] using one
    · simp [S₁]
    · simp [S₁,S₀,Store.setScalar,a,l]
    · simp [S₁,S₀,Store.setScalar,a,l]
  have control : ∀i≤S.scalar (l .outputDimension),∀T,CoordinateState S M i T →
      T.scalar (l .coordinate)=i ∧ T.scalar (a .coordinateTodo)=S.scalar (l .outputDimension)-i ∧
      T.scalar (l .one)=1 ∧ T.size≤storageBound Reg Arr M := by
    intro i hi T hT
    exact ⟨hT.index,hT.remaining,hT.one,Store.size_le_of_bounded hT.bounded⟩
  have step : ∀i<S.scalar (l .outputDimension),∀T,CoordinateState S M i T →
      ∃t≤14*(S.scalar (l .inputDimension))^2+9*S.scalar (l .inputDimension)+8,∃U,
        Runs (storageBound Reg Arr M) coordinateStep T t U ∧
        U.scalar (l .coordinate)=i ∧ U.scalar (a .coordinateTodo)=S.scalar (l .outputDimension)-i ∧
        U.scalar (l .one)=1 ∧ (U.setScalar (l .coordinate) (i+1)).size≤storageBound Reg Arr M ∧
        CoordinateState S M (i+1) (advance (l .coordinate) (a .coordinateTodo) U) := by
    intro i hi T hT
    have hn := hT.inputs (l .inputDimension) (by decide)
    have hm := hT.inputs (l .outputDimension) (by decide)
    have hx := hT.inputs (l .left) (by decide)
    have hy := hT.inputs (l .right) (by decide)
    have hp := hT.inputs (l .modulus) (by decide)
    have hz := hT.inputs (a .zero) (by decide)
    have hv : T.scalar (a .valid)≤1 := by
      rw [hT.validity]
      exact (Nat.mul_le_mul valid (coordinateProduct_le_one _ _ _ _ _ _)).trans (by decide)
    obtain ⟨t,ht,U,run,hU,uone,acc⟩ := coordinateStep_runs T M hT.bounded (by omega)
      (by rwa [hp]) (by rw [hT.index,hm]; exact hi) (by simpa only [hT.coefficients,hn,hm] using length)
      (by simpa only [hT.coefficients,hp] using small) (by omega) hv (by omega)
    have frame (r : Reg) (hr : r∈coordinateInputs ∨ r=l .coordinate ∨ r=a .coordinateTodo) : U.scalar r=T.scalar r := by
      apply run.scalar_eq_of_not_mem
      have hd : ∀r∈coordinateInputs,r∉coordinateStep.scalarWrites := by decide
      rcases hr with hr | hr | hr
      · exact hd r hr
      · subst r; decide
      · subst r; decide
    have ix : U.scalar (l .coordinate)=i := (frame _ (by simp)).trans hT.index
    have rem : U.scalar (a .coordinateTodo)=S.scalar (l .outputDimension)-i := (frame _ (by simp)).trans hT.remaining
    have mid : (U.setScalar (l .coordinate) (i+1)).Bounded M :=
      hU.setScalar _ ((by omega : i+1≤S.scalar (l .outputDimension)).trans (bounded.1 (l .outputDimension)))
    have final : (advance (l .coordinate) (a .coordinateTodo) U).Bounded M := by
      simpa only [advance,ix] using mid.setScalar (a .coordinateTodo)
        ((Nat.sub_le _ _).trans (hU.1 (a .coordinateTodo)))
    refine ⟨t,by simpa only [hn] using ht,U,run,ix,rem,uone,Store.size_le_of_bounded mid,final,?_,?_,?_,?_,?_,?_⟩
    · intro r hr
      have hd : ∀r∈coordinateInputs,r≠l .coordinate ∧ r≠a .coordinateTodo := by decide
      have he := (frame r (Or.inl hr)).trans (hT.inputs r hr)
      simpa [advance,Store.setScalar,(hd r hr).1,(hd r hr).2] using he
    · simpa [advance,Store.setScalar,a,l] using uone
    · exact (run.array_eq_of_not_mem _ (by decide)).trans hT.coefficients
    · simpa [advance,Store.setScalar,a,l] using ix
    · simpa [advance,Store.setScalar,a,l,Nat.sub_sub] using congrArg (fun n => n-1) rem
    · change U.scalar (a .valid)=_
      rw [acc,hT.validity,hT.coefficients,hp,hn,hm,hx,hT.index,coordinateProduct_succ]
      ring
  obtain ⟨t,ht,T,run,hT⟩ := countedLoop_runs (storageBound Reg Arr M)
    (l .coordinate) (a .coordinateTodo) (l .outputDimension) (l .one) coordinateStep
    (S.scalar (l .outputDimension)) (14*(S.scalar (l .inputDimension))^2+9*S.scalar (l .inputDimension)+8)
    (CoordinateState S M) S (Store.size_le_of_bounded bounded) (Store.size_le_of_bounded h₀)
    start control (by decide) (by decide) step
  exact ⟨t,by omega,T,run,hT.bounded,hT.one,hT.validity⟩

end GroupWL.MachinePrograms.AlternationCheck
