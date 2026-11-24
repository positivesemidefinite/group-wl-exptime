import GroupWL.MachinePrograms.MatrixArithmetic
import GroupWL.IndexedRefinement

/-! Computing tensor values from materialized coefficients and base-p
coordinate codes, by finite arithmetic and array loops. -/
namespace GroupWL.MachinePrograms.BilinearEvaluation

open NatArrayLanguage
open scoped BigOperators
set_option maxHeartbeats 1500000

inductive Reg where
  | inputDimension | outputDimension | left | right | coordinate | modulus | one
  | outer | outerTodo | inner | innerTodo | leftRest | rightRest | leftDigit | rightDigit
  | quotient | index | term | total
  deriving DecidableEq, Fintype

inductive Arr where
  | coefficients
  deriving DecidableEq, Fintype

abbrev State := Store Reg Arr
abbrev Code := NatArrayLanguage.Program Reg Arr

def read (xs : List ℕ) (i : ℕ) : ℕ := xs[i]?.getD 0
def digit (p value i : ℕ) : ℕ := value/p^i%p

def rowStepAtoms : List (Atom Reg Arr) := [
  .divmod .quotient .rightDigit .rightRest .modulus,
  .copy .rightRest .quotient,
  .binary .mul .index .outer .inputDimension,
  .binary .add .index .index .inner,
  .binary .mul .index .index .outputDimension,
  .binary .add .index .index .coordinate,
  .read .term .coefficients .index,
  .binary .mul .term .term .leftDigit,
  .binary .mul .term .term .rightDigit,
  .binary .add .term .total .term,
  .divmod .quotient .total .term .modulus]

def rowStep : Code := atoms rowStepAtoms

def row : Code := .seq (.atom (.copy .rightRest .right))
  (countedLoop .inner .innerTodo .inputDimension .one rowStep)

def outerStep : Code := .seq (atoms [
  .divmod .quotient .leftDigit .leftRest .modulus,
  .copy .leftRest .quotient]) row

def evaluate : Code := .seq (atoms [.const .one 1,.const .total 0,.copy .leftRest .left])
  (countedLoop .outer .outerTodo .inputDimension .one outerStep)

def rowSum (C : List ℕ) (p n m i z dx y initial j : ℕ) : ℕ :=
  (initial+∑ k ∈ Finset.range j,read C ((i*n+k)*m+z)*dx*digit p y k)%p

@[simp] theorem rowSum_zero (C : List ℕ) (p n m i z dx y initial : ℕ) :
    rowSum C p n m i z dx y initial 0=initial%p := by simp [rowSum]

theorem rowSum_succ (C : List ℕ) (p n m i z dx y initial j : ℕ) :
    rowSum C p n m i z dx y initial (j+1)=
      (rowSum C p n m i z dx y initial j+read C ((i*n+j)*m+z)*dx*digit p y j)%p := by
  simp only [rowSum,Finset.sum_range_succ,← Nat.add_assoc]
  exact (Nat.mod_add_mod _ _ _).symm

theorem rowStep_runs (S : State) (M : ℕ) (bounded : S.Bounded M)
    (positive : 0<S.scalar .modulus)
    (room : (S.scalar .modulus)^3+S.scalar .modulus≤M)
    (dimension : 0<S.scalar .outputDimension)
    (index : (S.scalar .outer*S.scalar .inputDimension+S.scalar .inner)*S.scalar .outputDimension+
      S.scalar .coordinate<(S.array .coefficients).length)
    (coefficients : ∀x∈S.array .coefficients,x<S.scalar .modulus)
    (leftSmall : S.scalar .leftDigit<S.scalar .modulus)
    (totalSmall : S.scalar .total<S.scalar .modulus) :
    Runs (storageBound Reg Arr M) rowStep S 11 (applyAtoms rowStepAtoms S) ∧
      (applyAtoms rowStepAtoms S).Bounded M ∧
      (applyAtoms rowStepAtoms S).scalar .rightRest=S.scalar .rightRest/S.scalar .modulus ∧
      (applyAtoms rowStepAtoms S).scalar .total=
        (S.scalar .total+read (S.array .coefficients)
          ((S.scalar .outer*S.scalar .inputDimension+S.scalar .inner)*S.scalar .outputDimension+
            S.scalar .coordinate)*S.scalar .leftDigit*(S.scalar .rightRest%S.scalar .modulus))%
          S.scalar .modulus := by
  have hlength := bounded.2.1 Arr.coefficients
  have hc : read (S.array .coefficients)
      ((S.scalar .outer*S.scalar .inputDimension+S.scalar .inner)*S.scalar .outputDimension+
        S.scalar .coordinate)<S.scalar .modulus := MatrixArithmetic.read_lt coefficients positive _
  have hd : S.scalar .rightRest%S.scalar .modulus<S.scalar .modulus := Nat.mod_lt _ positive
  have hprod : read (S.array .coefficients)
      ((S.scalar .outer*S.scalar .inputDimension+S.scalar .inner)*S.scalar .outputDimension+
        S.scalar .coordinate)*S.scalar .leftDigit≤(S.scalar .modulus)^2 := by nlinarith
  have hprod' : read (S.array .coefficients)
      ((S.scalar .outer*S.scalar .inputDimension+S.scalar .inner)*S.scalar .outputDimension+
        S.scalar .coordinate)*S.scalar .leftDigit*(S.scalar .rightRest%S.scalar .modulus)≤
        (S.scalar .modulus)^3 := by
    calc
      _ ≤ (S.scalar .modulus)^2*S.scalar .modulus := Nat.mul_le_mul hprod (Nat.le_of_lt hd)
      _ = _ := by ring
  have hsq : (S.scalar .modulus)^2≤(S.scalar .modulus)^3 :=
    pow_le_pow_right' (by omega) (by decide)
  have hvalid : ValidAtoms M rowStepAtoms S := by
    simp [rowStepAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,Function.update_apply]
    simp only [read] at hprod hprod'
    refine ⟨positive,?_,?_,?_,?_,index,?_,?_,?_,positive⟩ <;> nlinarith
  obtain ⟨hr,hb⟩ := atoms_runs bounded rowStepAtoms hvalid
  refine ⟨hr,hb,?_,?_⟩ <;>
    simp [applyAtoms,rowStepAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,read]

def rowInputs : Finset Reg :=
  {.inputDimension,.outputDimension,.outer,.coordinate,.leftDigit,.right,.modulus,.one}

structure RowState (S : State) (M j : ℕ) (T : State) : Prop where
  bounded : T.Bounded M
  inputs : ∀r∈rowInputs,T.scalar r=S.scalar r
  coefficients : T.array .coefficients=S.array .coefficients
  index : T.scalar .inner=j
  remaining : T.scalar .innerTodo=S.scalar .inputDimension-j
  rightRest : T.scalar .rightRest=S.scalar .right/(S.scalar .modulus)^j
  accumulator : T.scalar .total=rowSum (S.array .coefficients) (S.scalar .modulus)
    (S.scalar .inputDimension) (S.scalar .outputDimension) (S.scalar .outer)
    (S.scalar .coordinate) (S.scalar .leftDigit) (S.scalar .right) (S.scalar .total) j

theorem row_runs (S : State) (M : ℕ) (bounded : S.Bounded M)
    (one : S.scalar .one=1) (positive : 0<S.scalar .modulus)
    (room : (S.scalar .modulus)^3+S.scalar .modulus≤M)
    (dimension : 0<S.scalar .outputDimension)
    (indices : ∀j<S.scalar .inputDimension,
      (S.scalar .outer*S.scalar .inputDimension+j)*S.scalar .outputDimension+
        S.scalar .coordinate<(S.array .coefficients).length)
    (coefficients : ∀x∈S.array .coefficients,x<S.scalar .modulus)
    (leftSmall : S.scalar .leftDigit<S.scalar .modulus)
    (totalSmall : S.scalar .total<S.scalar .modulus) :
    ∃t≤14*S.scalar .inputDimension+4,∃T,
      Runs (storageBound Reg Arr M) row S t T ∧ T.Bounded M ∧
      T.scalar .total=rowSum (S.array .coefficients) (S.scalar .modulus)
        (S.scalar .inputDimension) (S.scalar .outputDimension) (S.scalar .outer)
        (S.scalar .coordinate) (S.scalar .leftDigit) (S.scalar .right) (S.scalar .total)
        (S.scalar .inputDimension) := by
  let S₀ := S.setScalar .rightRest (S.scalar .right)
  let S₁ := S₀.setScalar .innerTodo (S.scalar .inputDimension)
  let S₂ := S₁.setScalar .inner 0
  have h₀ : S₀.Bounded M := bounded.setScalar _ (bounded.1 .right)
  have h₁ : S₁.Bounded M := h₀.setScalar _ (bounded.1 .inputDimension)
  have h₂ : S₂.Bounded M := h₁.setScalar _ (by omega)
  have start : RowState S M 0 S₂ := by
    refine ⟨h₂,?_,rfl,?_,?_,?_,?_⟩
    · intro r hr
      have hd : ∀r∈rowInputs,r≠Reg.rightRest ∧ r≠Reg.innerTodo ∧ r≠Reg.inner := by decide
      obtain ⟨h₀,h₁,h₂⟩ := hd r hr
      simp [S₂,S₁,S₀,Store.setScalar,h₀,h₁,h₂]
    · simp [S₂]
    · simp [S₂,S₁]
    · simp [S₂,S₁,S₀,Store.setScalar]
    · simp [S₂,S₁,S₀,Store.setScalar,Nat.mod_eq_of_lt totalSmall]
  have control : ∀i≤S.scalar .inputDimension,∀T,RowState S M i T →
      T.scalar .inner=i ∧ T.scalar .innerTodo=S.scalar .inputDimension-i ∧
      T.scalar .one=1 ∧ T.size≤storageBound Reg Arr M := by
    intro i hi T hT
    exact ⟨hT.index,hT.remaining,(hT.inputs .one (by decide)).trans one,Store.size_le_of_bounded hT.bounded⟩
  have step : ∀i<S.scalar .inputDimension,∀T,RowState S M i T →
      ∃t≤11,∃U,Runs (storageBound Reg Arr M) rowStep T t U ∧
        U.scalar .inner=i ∧ U.scalar .innerTodo=S.scalar .inputDimension-i ∧ U.scalar .one=1 ∧
        (U.setScalar .inner (i+1)).size≤storageBound Reg Arr M ∧
        RowState S M (i+1) (advance .inner .innerTodo U) := by
    intro i hi T hT
    have hn := hT.inputs .inputDimension (by decide)
    have hm := hT.inputs .outputDimension (by decide)
    have ho := hT.inputs .outer (by decide)
    have hz := hT.inputs .coordinate (by decide)
    have hd := hT.inputs .leftDigit (by decide)
    have hp := hT.inputs .modulus (by decide)
    obtain ⟨run,bound,hrest,acc⟩ := rowStep_runs T M hT.bounded (by omega)
      (by rwa [hp]) (by omega)
      (by simpa only [hn,hm,ho,hz,hT.index,hT.coefficients] using indices i hi)
      (by simpa only [hT.coefficients,hp] using coefficients)
      (by omega) (by rw [hT.accumulator,hp]; exact Nat.mod_lt _ positive)
    let U := applyAtoms rowStepAtoms T
    have frame (r : Reg) (hr : r∈rowInputs ∨ r=.inner ∨ r=.innerTodo) : U.scalar r=T.scalar r := by
      apply run.scalar_eq_of_not_mem
      have hdis : ∀r∈rowInputs,r∉rowStep.scalarWrites := by decide
      rcases hr with hr | hr | hr
      · exact hdis r hr
      · subst r; decide
      · subst r; decide
    have hmid : (U.setScalar .inner (i+1)).Bounded M :=
      bound.setScalar _ ((by omega : i+1≤S.scalar .inputDimension).trans (bounded.1 .inputDimension))
    have hix : U.scalar .inner=i := (frame .inner (by simp)).trans hT.index
    have hrem : U.scalar .innerTodo=S.scalar .inputDimension-i := (frame .innerTodo (by simp)).trans hT.remaining
    have hone : U.scalar .one=1 := (frame .one (by decide)).trans ((hT.inputs .one (by decide)).trans one)
    have hfinal : (advance .inner .innerTodo U).Bounded M := by
      simpa only [advance,hix] using hmid.setScalar Reg.innerTodo
        ((Nat.sub_le _ _).trans (bound.1 .innerTodo))
    refine ⟨11,le_rfl,U,run,hix,hrem,hone,Store.size_le_of_bounded hmid,
      hfinal,?_,?_,?_,?_,?_,?_⟩
    · intro r hr
      have hdis : ∀r∈rowInputs,r≠Reg.inner ∧ r≠Reg.innerTodo := by decide
      have he := (frame r (Or.inl hr)).trans (hT.inputs r hr)
      simpa [advance,Store.setScalar,(hdis r hr).1,(hdis r hr).2] using he
    · exact (run.array_eq_of_not_mem .coefficients (by
        simp [rowStep,atoms,rowStepAtoms,NatArrayLanguage.sequence,Program.arrayWrites,Atom.arrayWrites])).trans
          hT.coefficients
    · simp [advance,Store.setScalar,hix]
    · simp [advance,Store.setScalar,hrem,Nat.sub_sub]
    · change U.scalar .rightRest=_
      rw [hrest,hT.rightRest,hp,Nat.div_div_eq_div_mul,pow_succ]
    · change U.scalar .total=_
      rw [acc,hT.accumulator,hT.coefficients,hn,hm,ho,hz,hd,hp,hT.index,hT.rightRest]
      exact (rowSum_succ _ _ _ _ _ _ _ _ _ _).symm
  obtain ⟨t,ht,T,run,hT⟩ := countedLoop_runs (storageBound Reg Arr M)
    Reg.inner Reg.innerTodo Reg.inputDimension Reg.one rowStep (S.scalar .inputDimension) 11
    (RowState S M) S₀ (Store.size_le_of_bounded h₀) (Store.size_le_of_bounded h₁)
    start control (by decide) (by decide) step
  refine ⟨1+t,by omega,T,?_,hT.bounded,hT.accumulator⟩
  exact .seq (atom_runs bounded (.copy .rightRest .right) trivial trivial) run

end GroupWL.MachinePrograms.BilinearEvaluation
