import GroupWL.KernelProgramCorrectness
import GroupWL.MachinePrograms.KernelCost

/-! Bounded execution returns the actual proved kernel basis and retraction. -/
namespace GroupWL.KernelExecution
open CoordinateElimination CachedElimination PivotKernelEncoding KernelProgramCorrectness
open MachinePrograms NatArrayLanguage KernelProgram PivotMatrixCorrectness
variable {p m n : ℕ} [Fact p.Prime]

theorem program_chart_runs (f : (Fin n → ZMod p) →ₗ[ZMod p] (Fin m → ZMod p))
    (S : State) (M : ℕ) (bounded : S.Bounded M)
    (ambient : S.scalar (wr .ambient)=n) (rows : S.scalar (wr .rows)=m)
    (modulus : S.scalar (wr .modulus)=p)
    (input : S.array (wa .input)=MatrixEncoding.word (ofLinear f))
    (small : p*p+p≤M) (square : n*n≤M) :
    ∃t≤programCost m n p,∃T,
      Runs (storageBound Reg Arr M) (program p) S t T ∧ T.Bounded M ∧
      Represents p n 0 (MatrixEncoding.word (ofLinear f)) (encode (PivotElimination.kernelChart m n f)) T := by
  obtain ⟨t,ht,T,run,hT,rep⟩ := KernelProgram.program_runs p n m M
    (MatrixEncoding.word (ofLinear f)) S bounded ambient rows modulus input
    (Fact.out : p.Prime).one_lt small square (MatrixEncoding.word_length _) (MatrixEncoding.word_values_lt _)
  rw [executeRows_encode] at rep
  exact ⟨t,ht,T,run,hT,rep⟩

theorem program_matrix_runs (A : MatrixData (F:=ZMod p) m n)
    (S : State) (M : ℕ) (bounded : S.Bounded M)
    (ambient : S.scalar (wr .ambient)=n) (rows : S.scalar (wr .rows)=m)
    (modulus : S.scalar (wr .modulus)=p) (input : S.array (wa .input)=MatrixEncoding.word A)
    (small : p*p+p≤M) (square : n*n≤M) :
    ∃t≤programCost m n p,∃T,
      Runs (storageBound Reg Arr M) (program p) S t T ∧ T.Bounded M ∧
      Represents p n 0 (MatrixEncoding.word A) (encode (PivotElimination.matrixKernelChart A)) T := by
  simpa only [ofLinear_toLinear] using program_chart_runs (toLinear A) S M bounded ambient rows modulus
    (by simpa only [ofLinear_toLinear] using input) small square

theorem program_chart_polynomial (f : (Fin n → ZMod p) →ₗ[ZMod p] (Fin m → ZMod p))
    (S : State) (M : ℕ) (bounded : S.Bounded M)
    (ambient : S.scalar (wr .ambient)=n) (rows : S.scalar (wr .rows)=m)
    (modulus : S.scalar (wr .modulus)=p)
    (input : S.array (wa .input)=MatrixEncoding.word (ofLinear f))
    (small : p*p+p≤M) (square : n*n≤M) :
    ∃t≤220*(m+n+p+1)^4,∃T,
      Runs (150*(M+1)^2) (program p) S t T ∧ T.Bounded M ∧
      Represents p n 0 (MatrixEncoding.word (ofLinear f)) (encode (PivotElimination.kernelChart m n f)) T := by
  obtain ⟨t,ht,T,run,hT,rep⟩ := program_chart_runs f S M bounded ambient rows modulus input small square
  exact ⟨t,ht.trans (programCost_le m n p),T,run.mono (KernelProgram.storageBound_le M),hT,rep⟩

end GroupWL.KernelExecution
