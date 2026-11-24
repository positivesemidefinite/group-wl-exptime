import GroupWL.WedgeOperatorEncoding

/-! A callable concrete obstruction-to-operator client in canonical coordinates. -/
namespace GroupWL.ConstructiveIncidence
open IncidenceTensor ConstructiveCoordinates MachinePrograms NatArrayLanguage NatArrayExpressions
set_option synthInstance.maxSize 4096
set_option maxRecDepth 8192
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [FiniteCode I] [FiniteCode J]
variable (p : ℕ) [Fact p.Prime]
variable {V : J → Type} [∀j,AddCommGroup (V j)] [∀j,Module (ZMod p) (V j)]
variable (A : AffineSystem (ZMod p) I J V) (R : ∀j,Coordinates (ZMod p) (ReadoutRadical A j)) (q : ℕ)

theorem wedgeDescriptors_valid : (wedgeDescriptors p A R q).Valid
    (FiniteCode.size (OldOutputIndex A R q)) (FiniteCode.size (FormIndex A R q)) := by
  refine ⟨List.length_ofFn,List.length_ofFn,List.length_ofFn,List.length_ofFn,List.length_ofFn,?_,?_,?_,?_⟩
  all_goals
    intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact (FiniteCode.equiv _).isLt

theorem wedgeOperator_runs (hq : 0<q) (M : ℕ)
    (hpM : p*p+2*p≤M)
    (hnino : FiniteCode.size (InputIndex A R q)*FiniteCode.size (OutputIndex A R q)≤M)
    (square : (FiniteCode.size (InputIndex A R q)*FiniteCode.size (OutputIndex A R q))^2≤M)
    (S : WedgeKernel.State) (bounded : S.Bounded M)
    (ready : WedgeConstraints.Ready (wedgeDescriptors p A R q) (formMatrix p A R q)
      (chosenFormMatrix p A R q hq) p (FiniteCode.size (OldInputIndex A R q))
      (FiniteCode.size (OldOutputIndex A R q)) (chosenCoordinates A R q hq).dimension
      (FiniteCode.size (InputIndex A R q)) (FiniteCode.size (OutputIndex A R q)) (inputs S.left))
    (length : S.left.scalar (.inl .total)=(chosenCoordinates A R q hq).dimension*
      FiniteCode.size (InputIndex A R q)*FiniteCode.size (OutputIndex A R q)) :
    ∃t≤((chosenCoordinates A R q hq).dimension*FiniteCode.size (InputIndex A R q)*
        FiniteCode.size (OutputIndex A R q))*(WedgeConstraints.expression.cost+4)+10+
        220*((chosenCoordinates A R q hq).dimension+FiniteCode.size (InputIndex A R q)*
          FiniteCode.size (OutputIndex A R q)+p+1)^4,∃T,
      Runs (storageBound WedgeKernel.Reg WedgeKernel.Arr M) (WedgeKernel.program p) S t T ∧ T.Bounded M ∧
      KernelProgram.Represents p (FiniteCode.size (InputIndex A R q)*FiniteCode.size (OutputIndex A R q))
        0 (wedgeWord p A R q hq)
        (KernelProgramCorrectness.encode (GeneratedCoordinateEntries.operatorChart (chosenCoordinates A R q hq)
          (ConstructiveTensor.obstructionMap A R q hq))) T.right := by
  have hp := (Fact.out : p.Prime).one_lt
  obtain ⟨t,ht,T,run,hTB,hrep⟩ := WedgeKernel.program_runs (wedgeDescriptors p A R q)
    (formMatrix p A R q) (chosenFormMatrix p A R q hq) p
    (FiniteCode.size (OldInputIndex A R q)) (FiniteCode.size (OldOutputIndex A R q))
    (chosenCoordinates A R q hq).dimension (FiniteCode.size (InputIndex A R q))
    (FiniteCode.size (OutputIndex A R q)) (FiniteCode.size (FormIndex A R q)) M hp (by omega)
    hpM hnino (by simpa only [pow_two] using square) (MatrixEncoding.word_length _)
    (MatrixEncoding.word_length _) (MatrixEncoding.word_values_lt _) (MatrixEncoding.word_values_lt _)
    (wedgeDescriptors_valid p A R q) S bounded ready length
  rw [wedgeKernel_data p A R q hq] at hrep
  exact ⟨t,ht,T,run,hTB,hrep⟩

end GroupWL.ConstructiveIncidence
