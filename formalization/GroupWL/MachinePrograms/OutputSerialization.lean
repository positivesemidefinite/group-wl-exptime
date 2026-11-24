import GroupWL.MachinePrograms.DimensionSerialization
import GroupWL.MachinePrograms.TensorSerialization
import GroupWL.InputParsing

/-! Concrete final serializers for the two target problems. -/
namespace GroupWL.MachinePrograms.OutputSerialization
open Structured NatArrayLowering Statement

inductive Reg where | input₁ | output₁ | input₂ | output₂ | dimension
  deriving DecidableEq, Fintype
inductive Arr where | coefficients₁ | coefficients₂
  deriving DecidableEq, Fintype
abbrev K := StackIndex Reg Arr
abbrev State := NatArrayLanguage.Store Reg Arr

def dimensionRegisters : Fin 12 ↪ K where
  toFun i := if i=3 then scalarSlot Reg.dimension else scratchSlot ⟨i.val,by omega⟩
  inj' := by
    intro i j h
    by_cases hi : i=3 <;> by_cases hj : j=3
    · exact hi.trans hj.symm
    · simp [hi,hj,scalarSlot,scratchSlot] at h
    · simp [hi,hj,scalarSlot,scratchSlot] at h
    · simp only [hi,hj,ite_false,scratchSlot,Sum.inr.injEq,Fin.mk.injEq] at h
      exact Fin.ext h

def first : Structured.Program K :=
  TensorSerialization.encodedProgram Reg.input₁ Reg.output₁ Arr.coefficients₁

def second : Structured.Program K :=
  TensorSerialization.encodedProgram Reg.input₂ Reg.output₂ Arr.coefficients₂

def dimension (e : DimensionEncoding) : Structured.Program K :=
  DimensionSerialization.program e dimensionRegisters

def identification (e : DimensionEncoding) : Structured.Program K := .seq first (dimension e)
def equivalence (e : DimensionEncoding) : Structured.Program K :=
  .seq first (.seq second (dimension e))

/-- State after consuming one dense tensor, retaining every other input register. -/
def consume (S : Structured.Store K) (n m : Reg) (c : Arr) (w : List Bool) : Structured.Store K :=
  Function.update (Function.update (Function.update (Function.update S (scalarSlot n) [])
    (scalarSlot m) []) (arraySlot c) []) (scratchSlot 0) (w.reverse++S (scratchSlot 0))

theorem dense_runs (p : ℕ) [Fact p.Prime] (n m : Reg) (c : Arr) (hne : n≠m)
    (S : Structured.Store K) (T : TensorDescription p)
    (hn : S (scalarSlot n)=Structured.unary T.inputDimension)
    (hm : S (scalarSlot m)=Structured.unary T.outputDimension)
    (hc : S (arraySlot c)=Structured.arrayWord (TensorSerialization.coefficientList (T.coefficient p))) :
    ∃t≤3*(T.denseWord p).length+5,
      Runs (TensorSerialization.encodedProgram n m c) S t (consume S n m c (T.denseWord p)) := by
  rw [TensorSerialization.coefficientList_word] at hc
  have h := TensorSerialization.program_runs (scalarSlot n) (scalarSlot m) (arraySlot c)
    (scratchSlot 0) (by simpa using hne) (by simp) (by simp) (by simp) (by simp) (by simp)
    S T.inputDimension T.outputDimension (coefficientsWord p (T.coefficient p)) hn hm hc
  refine ⟨3*(T.inputDimension+T.outputDimension+(coefficientsWord p (T.coefficient p)).length)+5,?_,?_⟩
  · simp only [denseWord_eq_coefficients,List.length_append,Statement.unary,
      List.length_replicate,List.length_singleton]
    omega
  · simpa only [consume,denseWord_eq_coefficients] using h

theorem dimension_runs (e : DimensionEncoding) (S : Structured.Store K) (k : ℕ)
    (hk : S (scalarSlot Reg.dimension)=Structured.unary k)
    (hempty : ∀i : Fin 16,i=2 ∨ (4 ≤ i.val ∧ i.val≤10) → S (scratchSlot i)=[]) :
    ∃t≤110*(k+1)^2,∃U,Runs (dimension e) S t U ∧
      U (scratchSlot 0)=(dimensionWord e k).reverse++S (scratchSlot 0) := by
  obtain ⟨t,ht,U,hr,ho⟩ := DimensionSerialization.program_runs e dimensionRegisters S k
    (by simpa [dimensionRegisters] using hk) (by
      intro i hi
      have hne : i≠(3 : Fin 12) := by intro he; subst i; rcases hi with hi|⟨hi,_⟩ <;> omega
      simpa [dimensionRegisters,hne] using hempty ⟨i.val,by omega⟩ (by
        rcases hi with hi|⟨hi,hj⟩
        · left; subst i; rfl
        · exact Or.inr ⟨hi,hj⟩))
  exact ⟨t,ht,U,hr,by simpa [dimensionRegisters] using ho⟩

theorem identification_runs (p : ℕ) [Fact p.Prime] (e : DimensionEncoding)
    (S : State) (T : TensorDescription p) (k : ℕ)
    (hn : S.scalar .input₁=T.inputDimension) (hm : S.scalar .output₁=T.outputDimension)
    (hc : S.array .coefficients₁=TensorSerialization.coefficientList (T.coefficient p))
    (hk : S.scalar .dimension=k) :
    ∃t≤3*(T.denseWord p).length+5+110*(k+1)^2,∃U,
      Runs (identification e) (encodeStore S) t U ∧
      (U (scratchSlot 0)).reverse=identificationWord p e T k := by
  obtain ⟨t,ht,hr⟩ := dense_runs p Reg.input₁ Reg.output₁ Arr.coefficients₁ (by decide)
    (encodeStore S) T (by simp [hn,Structured.unary]) (by simp [hm,Structured.unary]) (by simp [hc])
  let A := consume (encodeStore S) Reg.input₁ Reg.output₁ Arr.coefficients₁ (T.denseWord p)
  obtain ⟨u,hu,U,hru,ho⟩ := dimension_runs e A k (by simp [A,consume,hk,Structured.unary]) (by
    intro i hi
    have hne : i≠0 := by intro he; subst i; rcases hi with hi|⟨hi,_⟩ <;> omega
    simp [A,consume,hne])
  refine ⟨t+u,by omega,U,.seq hr hru,?_⟩
  rw [ho]
  simp [A,consume,identificationWord,List.reverse_append]

theorem equivalence_runs (p : ℕ) [Fact p.Prime] (e : DimensionEncoding)
    (S : State) (T U : TensorDescription p) (k : ℕ)
    (hn : S.scalar .input₁=T.inputDimension) (hm : S.scalar .output₁=T.outputDimension)
    (hc : S.array .coefficients₁=TensorSerialization.coefficientList (T.coefficient p))
    (hn' : S.scalar .input₂=U.inputDimension) (hm' : S.scalar .output₂=U.outputDimension)
    (hc' : S.array .coefficients₂=TensorSerialization.coefficientList (U.coefficient p))
    (hk : S.scalar .dimension=k) :
    ∃t≤3*((T.denseWord p).length+(U.denseWord p).length)+10+110*(k+1)^2,∃W,
      Runs (equivalence e) (encodeStore S) t W ∧
      (W (scratchSlot 0)).reverse=equivalenceWord p e T U k := by
  obtain ⟨t,ht,hr⟩ := dense_runs p Reg.input₁ Reg.output₁ Arr.coefficients₁ (by decide)
    (encodeStore S) T (by simp [hn,Structured.unary]) (by simp [hm,Structured.unary]) (by simp [hc])
  let A := consume (encodeStore S) Reg.input₁ Reg.output₁ Arr.coefficients₁ (T.denseWord p)
  obtain ⟨u,hu,hru⟩ := dense_runs p Reg.input₂ Reg.output₂ Arr.coefficients₂ (by decide) A U
    (by simp [A,consume,hn',Structured.unary]) (by simp [A,consume,hm',Structured.unary])
    (by simp [A,consume,hc'])
  let B := consume A Reg.input₂ Reg.output₂ Arr.coefficients₂ (U.denseWord p)
  obtain ⟨v,hv,W,hrv,ho⟩ := dimension_runs e B k (by simp [B,A,consume,hk,Structured.unary]) (by
    intro i hi
    have hne : i≠0 := by intro he; subst i; rcases hi with hi|⟨hi,_⟩ <;> omega
    simp [B,A,consume,hne])
  refine ⟨t+(u+v),by omega,W,.seq hr (.seq hru hrv),?_⟩
  rw [ho]
  simp [B,A,consume,equivalenceWord,List.reverse_append,List.append_assoc]

end GroupWL.MachinePrograms.OutputSerialization
