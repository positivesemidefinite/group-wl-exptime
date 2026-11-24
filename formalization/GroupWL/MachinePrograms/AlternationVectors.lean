import GroupWL.MachinePrograms.AlternationCoordinates

/-! Enumerating all base-p vector codes in the alternating-form test. -/
namespace GroupWL.MachinePrograms.AlternationCheck

open NatArrayLanguage
open scoped BigOperators

theorem vectorStep_runs (S : State) (M : ℕ) (bounded : S.Bounded M)
    (one : S.scalar (l .one)=1) (positive : 0<S.scalar (l .modulus))
    (room : (S.scalar (l .modulus))^3+S.scalar (l .modulus)≤M)
    (length : (S.array (.inl .coefficients)).length=
      S.scalar (l .inputDimension)*S.scalar (l .inputDimension)*S.scalar (l .outputDimension))
    (small : ∀x∈S.array (.inl .coefficients),x<S.scalar (l .modulus))
    (valid : S.scalar (a .valid)≤1) (zero : S.scalar (a .zero)=0) :
    ∃t≤S.scalar (l .outputDimension)*(14*(S.scalar (l .inputDimension))^2+
        9*S.scalar (l .inputDimension)+11)+4,∃T,
      Runs (storageBound Reg Arr M) vectorStep S t T ∧ T.Bounded M ∧
      T.scalar (l .one)=1 ∧ T.scalar (a .valid)=S.scalar (a .valid)*coordinateProduct
        (S.array (.inl .coefficients)) (S.scalar (l .modulus)) (S.scalar (l .inputDimension))
        (S.scalar (l .outputDimension)) (S.scalar (l .left)) (S.scalar (l .outputDimension)) := by
  let U := S.setScalar (l .right) (S.scalar (l .left))
  have first : Runs (storageBound Reg Arr M) (.atom (.copy (l .right) (l .left))) S 1 U :=
    atom_runs bounded _ trivial trivial
  have hU : U.Bounded M := bounded.setScalar _ (bounded.1 (l .left))
  obtain ⟨t,ht,T,last,hT,hone,hvalid⟩ := coordinates_runs U M hU
    (by simpa [U,Store.setScalar,l] using one)
    (by simpa [U,Store.setScalar,l] using positive)
    (by simpa [U,Store.setScalar,l] using room)
    (by simpa [U,Store.setScalar,l] using length)
    (by simpa [U,Store.setScalar,l] using small)
    (by simp [U,Store.setScalar,l])
    (by simpa [U,Store.setScalar,l,a] using valid)
    (by simpa [U,Store.setScalar,l,a] using zero)
  refine ⟨1+t,?_,T,.seq first last,hT,hone,?_⟩
  · have hh : t≤S.scalar (l .outputDimension)*(14*(S.scalar (l .inputDimension))^2+
        9*S.scalar (l .inputDimension)+11)+3 := by simpa [U,Store.setScalar,l] using ht
    omega
  · simpa [U,Store.setScalar,l,a] using hvalid

def vectorProduct (C : List ℕ) (p n m q : ℕ) : ℕ :=
  ∏x ∈ Finset.range q,coordinateProduct C p n m x m

@[simp] theorem vectorProduct_zero (C : List ℕ) (p n m : ℕ) : vectorProduct C p n m 0=1 := by
  simp [vectorProduct]

theorem vectorProduct_succ (C : List ℕ) (p n m q : ℕ) :
    vectorProduct C p n m (q+1)=vectorProduct C p n m q*coordinateProduct C p n m q m := by
  simp [vectorProduct,Finset.prod_range_succ]

theorem vectorProduct_le_one (C : List ℕ) (p n m q : ℕ) : vectorProduct C p n m q≤1 := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [vectorProduct_succ]
    exact (Nat.mul_le_mul ih (coordinateProduct_le_one _ _ _ _ _ _)).trans (by decide)

def vectorInputs : Finset Reg := {l .inputDimension,l .outputDimension,l .modulus,a .zero,a .order}

structure VectorState (S : State) (M i : ℕ) (T : State) : Prop where
  bounded : T.Bounded M
  inputs : ∀r∈vectorInputs,T.scalar r=S.scalar r
  one : T.scalar (l .one)=1
  coefficients : T.array (.inl .coefficients)=S.array (.inl .coefficients)
  index : T.scalar (l .left)=i
  remaining : T.scalar (a .vectorTodo)=S.scalar (a .order)-i
  validity : T.scalar (a .valid)=S.scalar (a .valid)*vectorProduct
    (S.array (.inl .coefficients)) (S.scalar (l .modulus)) (S.scalar (l .inputDimension))
    (S.scalar (l .outputDimension)) i

def vectors : Code := countedLoop (l .left) (a .vectorTodo) (a .order) (l .one) vectorStep

theorem vectors_runs (S : State) (M : ℕ) (bounded : S.Bounded M)
    (one : S.scalar (l .one)=1) (positive : 0<S.scalar (l .modulus))
    (room : (S.scalar (l .modulus))^3+S.scalar (l .modulus)≤M)
    (length : (S.array (.inl .coefficients)).length=
      S.scalar (l .inputDimension)*S.scalar (l .inputDimension)*S.scalar (l .outputDimension))
    (small : ∀x∈S.array (.inl .coefficients),x<S.scalar (l .modulus))
    (valid : S.scalar (a .valid)≤1) (zero : S.scalar (a .zero)=0) :
    ∃t≤S.scalar (a .order)*(S.scalar (l .outputDimension)*(14*(S.scalar (l .inputDimension))^2+
        9*S.scalar (l .inputDimension)+11)+7)+3,∃T,
      Runs (storageBound Reg Arr M) vectors S t T ∧ T.Bounded M ∧
      T.scalar (l .one)=1 ∧ T.scalar (a .valid)=S.scalar (a .valid)*vectorProduct
        (S.array (.inl .coefficients)) (S.scalar (l .modulus)) (S.scalar (l .inputDimension))
        (S.scalar (l .outputDimension)) (S.scalar (a .order)) := by
  let S₀ := S.setScalar (a .vectorTodo) (S.scalar (a .order))
  let S₁ := S₀.setScalar (l .left) 0
  have h₀ : S₀.Bounded M := bounded.setScalar _ (bounded.1 (a .order))
  have h₁ : S₁.Bounded M := h₀.setScalar _ (by omega)
  have start : VectorState S M 0 S₁ := by
    refine ⟨h₁,?_,?_,rfl,?_,?_,?_⟩
    · intro r hr
      have hd : ∀r∈vectorInputs,r≠l .left ∧ r≠a .vectorTodo := by decide
      simp [S₁,S₀,Store.setScalar,(hd r hr).1,(hd r hr).2]
    · simpa [S₁,S₀,Store.setScalar,a,l] using one
    · simp [S₁]
    · simp [S₁,S₀,Store.setScalar,a,l]
    · simp [S₁,S₀,Store.setScalar,a,l]
  have control : ∀i≤S.scalar (a .order),∀T,VectorState S M i T →
      T.scalar (l .left)=i ∧ T.scalar (a .vectorTodo)=S.scalar (a .order)-i ∧
      T.scalar (l .one)=1 ∧ T.size≤storageBound Reg Arr M := by
    intro i hi T hT
    exact ⟨hT.index,hT.remaining,hT.one,Store.size_le_of_bounded hT.bounded⟩
  have step : ∀i<S.scalar (a .order),∀T,VectorState S M i T →
      ∃t≤S.scalar (l .outputDimension)*(14*(S.scalar (l .inputDimension))^2+9*S.scalar (l .inputDimension)+11)+4,
      ∃U,Runs (storageBound Reg Arr M) vectorStep T t U ∧
        U.scalar (l .left)=i ∧ U.scalar (a .vectorTodo)=S.scalar (a .order)-i ∧
        U.scalar (l .one)=1 ∧ (U.setScalar (l .left) (i+1)).size≤storageBound Reg Arr M ∧
        VectorState S M (i+1) (advance (l .left) (a .vectorTodo) U) := by
    intro i hi T hT
    have hn := hT.inputs (l .inputDimension) (by decide)
    have hm := hT.inputs (l .outputDimension) (by decide)
    have hp := hT.inputs (l .modulus) (by decide)
    have hz := hT.inputs (a .zero) (by decide)
    have hv : T.scalar (a .valid)≤1 := by
      rw [hT.validity]
      exact (Nat.mul_le_mul valid (vectorProduct_le_one _ _ _ _ _)).trans (by decide)
    obtain ⟨t,ht,U,run,hU,uone,acc⟩ := vectorStep_runs T M hT.bounded hT.one (by omega)
      (by rwa [hp]) (by simpa only [hT.coefficients,hn,hm] using length)
      (by simpa only [hT.coefficients,hp] using small) hv (by omega)
    have frame (r : Reg) (hr : r∈vectorInputs ∨ r=l .left ∨ r=a .vectorTodo) : U.scalar r=T.scalar r := by
      apply run.scalar_eq_of_not_mem
      have hd : ∀r∈vectorInputs,r∉vectorStep.scalarWrites := by decide
      rcases hr with hr | hr | hr
      · exact hd r hr
      · subst r; decide
      · subst r; decide
    have ix : U.scalar (l .left)=i := (frame _ (by simp)).trans hT.index
    have rem : U.scalar (a .vectorTodo)=S.scalar (a .order)-i := (frame _ (by simp)).trans hT.remaining
    have mid : (U.setScalar (l .left) (i+1)).Bounded M :=
      hU.setScalar _ ((by omega : i+1≤S.scalar (a .order)).trans (bounded.1 (a .order)))
    have final : (advance (l .left) (a .vectorTodo) U).Bounded M := by
      simpa only [advance,ix] using mid.setScalar (a .vectorTodo)
        ((Nat.sub_le _ _).trans (hU.1 (a .vectorTodo)))
    refine ⟨t,by simpa only [hn,hm] using ht,U,run,ix,rem,uone,Store.size_le_of_bounded mid,final,?_,?_,?_,?_,?_,?_⟩
    · intro r hr
      have hd : ∀r∈vectorInputs,r≠l .left ∧ r≠a .vectorTodo := by decide
      have he := (frame r (Or.inl hr)).trans (hT.inputs r hr)
      simpa [advance,Store.setScalar,(hd r hr).1,(hd r hr).2] using he
    · simpa [advance,Store.setScalar,a,l] using uone
    · exact (run.array_eq_of_not_mem _ (by decide)).trans hT.coefficients
    · simpa [advance,Store.setScalar,a,l] using ix
    · simpa [advance,Store.setScalar,a,l,Nat.sub_sub] using congrArg (fun n => n-1) rem
    · change U.scalar (a .valid)=_
      rw [acc,hT.validity,hT.coefficients,hp,hn,hm,hT.index,vectorProduct_succ]
      ring
  obtain ⟨t,ht,T,run,hT⟩ := countedLoop_runs (storageBound Reg Arr M)
    (l .left) (a .vectorTodo) (a .order) (l .one) vectorStep
    (S.scalar (a .order))
    (S.scalar (l .outputDimension)*(14*(S.scalar (l .inputDimension))^2+9*S.scalar (l .inputDimension)+11)+4)
    (VectorState S M) S (Store.size_le_of_bounded bounded) (Store.size_le_of_bounded h₀)
    start control (by decide) (by decide) step
  exact ⟨t,by omega,T,run,hT.bounded,hT.one,hT.validity⟩

end GroupWL.MachinePrograms.AlternationCheck
