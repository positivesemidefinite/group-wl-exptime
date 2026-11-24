import GroupWL.MachinePrograms.LayoutIncidenceBounds
import GroupWL.LayoutMetadataArrays

/-! The executable incidence stage produces the exact typed source records. -/
namespace GroupWL.MachinePrograms.LayoutIncidencePrograms
open NatArrayLanguage SourceLayout
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 16384
set_option maxRecDepth 8192
variable {T E : Type} [FiniteCode T] [FiniteCode E] {r : ℕ}
  (p : ℕ) [Fact p.Prime] (C : ComparisonData (ZMod p) T E r) (L : ℕ)

theorem comparison_valid : Valid (ComparisonMetadata.ofComparison p C) := by
  refine ⟨?_,LayoutMetadata.domain_binary p C,ComparisonMetadata.source_length p C,
    ComparisonMetadata.target_length p C,?_,?_,ComparisonMetadata.permutation_length p C⟩
  · change (ComparisonMetadata.domain p C).length=2*(FiniteCode.size E*r)
    rw [ComparisonMetadata.domain_length]
    omega
  · intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact (FiniteCode.equiv (C.source (FiniteCode.equiv.symm i))).isLt
  · intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact (FiniteCode.equiv (C.target (FiniteCode.equiv.symm i))).isLt

def endpoint : SourceIncidence.Arr→SquareIndices.Endpoint
  | .left => .left
  | .right => .right
  | .before => .before
  | .after => .after

theorem endpoint_word (a : SourceIncidence.Arr) :
    SquareSelected.word (ComparisonMetadata.ofComparison p C) L (endpoint a)=
      SourceTableEncoding.incidenceData p C L a := by
  cases a with
  | left => exact LayoutMetadata.selected_left p C L
  | right => exact LayoutMetadata.selected_right p C L
  | before => exact LayoutMetadata.selected_before p C L
  | after => exact LayoutMetadata.selected_after p C L

theorem program_runs_correct (S : State)
    (bounded : S.Bounded (budget (ComparisonMetadata.ofComparison p C) L))
    (input : Input (ComparisonMetadata.ofComparison p C) L S) (positive : 0<L) :
    ∃t≤4000*(magnitude (ComparisonMetadata.ofComparison p C) L)^3,∃U,
      Runs (storageBound Reg Arr (budget (ComparisonMetadata.ofComparison p C) L)) program S t U ∧
      U.Bounded (budget (ComparisonMetadata.ofComparison p C) L) ∧
      Output (ComparisonMetadata.ofComparison p C) L U ∧
      ∀a,U.right.array (.inr (endpoint a))=SourceTableEncoding.incidenceData p C L a := by
  obtain ⟨t,ht,U,run,hU,hout⟩ := program_runs_polynomial (ComparisonMetadata.ofComparison p C) L S
    bounded input (comparison_valid p C) positive
  exact ⟨t,ht,U,run,hU,hout,fun a => (hout.endpoints _).trans (endpoint_word p C L a)⟩

end GroupWL.MachinePrograms.LayoutIncidencePrograms
