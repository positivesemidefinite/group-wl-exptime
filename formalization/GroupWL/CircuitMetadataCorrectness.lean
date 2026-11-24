import GroupWL.CircuitComparisonCoefficients

/-! The complete numeric metadata table is the canonical comparison table. -/
namespace GroupWL.CircuitMetadataValues
open CircuitComparisons CircuitComparisonCodes
open MachinePrograms.EvaluationAssembly
set_option maxHeartbeats 3000000

private theorem ofFn_codes {α β : Type} [FiniteCode α] {n : ℕ}
    (hn : n=FiniteCode.size α) (f : ℕ→β) (g : α→β)
    (h : ∀a, f (FiniteCode.equiv a).val=g a) :
    List.ofFn (fun i : Fin n=>f i)=
      List.ofFn (fun i : Fin (FiniteCode.size α)=>g (FiniteCode.equiv.symm i)) := by
  subst n
  apply congrArg List.ofFn
  funext i
  simpa using h (FiniteCode.equiv.symm i)

variable {T : Type} [FiniteCode T] {r : ℕ} (C : AddressedCircuit.Circuit T r)
  (p : ℕ) [Fact p.Prime]

theorem table_correct : (ofCircuit C).table=
    ComparisonMetadata.ofComparison p (comparisons C (ZMod p)) := by
  have ht : (ofCircuit C).realTypes=FiniteCode.size (RealType C) := by
    rw [size_realType]
    rfl
  have he : (ofCircuit C).comparisons=FiniteCode.size (Comparison C) := by
    rw [size_comparison]
    rfl
  unfold Data.table ComparisonMetadata.ofComparison
  congr 1
  · exact ofFn_codes ht _ _ (real_dimension C)
  · exact ofFn_codes he _ _ (comparison_source C)
  · exact ofFn_codes he _ _ (comparison_target C)
  · apply congrArg List.flatten
    rw [he]
    apply congrArg List.ofFn
    funext e
    apply congrArg List.ofFn
    funext k
    simpa only [Equiv.apply_symm_apply] using comparison_sourceForm C p ((FiniteCode.equiv (α:=Comparison C)).symm e) k
  · apply congrArg List.flatten
    rw [he]
    apply congrArg List.ofFn
    funext e
    apply congrArg List.ofFn
    funext k
    simpa only [Equiv.apply_symm_apply] using comparison_targetForm C p ((FiniteCode.equiv (α:=Comparison C)).symm e) k
  · unfold ComparisonMetadata.domain
    rw [entries3_nested,entries3_nested]
    apply congrArg List.flatten
    rw [he]
    apply congrArg List.ofFn
    funext e
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext i
    apply congrArg List.ofFn
    funext a
    simpa only [Equiv.apply_symm_apply] using comparison_domain C ((FiniteCode.equiv (α:=Comparison C)).symm e) i a
  · apply congrArg List.flatten
    rw [he]
    apply congrArg List.ofFn
    funext e
    apply congrArg List.ofFn
    funext i
    simpa only [Equiv.apply_symm_apply] using comparison_permutation C ((FiniteCode.equiv (α:=Comparison C)).symm e) i

end GroupWL.CircuitMetadataValues
