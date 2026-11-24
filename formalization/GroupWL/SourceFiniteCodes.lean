import GroupWL.FiniteCodeConstructions
import GroupWL.SourceSize

/-! Computable numeric codes for every finite source-layout index. They use
the displayed constructor equivalences, never a chosen enumeration. -/
namespace GroupWL.FiniteCode

open SourceLayout CircuitComparisons

instance linkCode {E : Type} [FiniteCode E] (L : ℕ) : FiniteCode (Link E L) := by
  letI := fintype E
  exact ⟨size ((E ⊕ (E × Fin L)) ⊕ E),
    (SourceSize.linkEquiv (E := E) L).trans (equiv (α := (E ⊕ (E × Fin L)) ⊕ E))⟩

instance primaryCode {T : Type} [FiniteCode T] : FiniteCode (Primary T) := by
  letI := fintype T
  exact ⟨size (T ⊕ Bool), (SourceSize.primaryEquiv (G := T)).trans
    (equiv (α := T ⊕ Bool))⟩

instance connectionCode {T : Type} [FiniteCode T] {r : ℕ} (C : AddressedCircuit.Circuit T r) :
    FiniteCode (Connection C) := by
  letI := fintype T
  let U := Fin C.edges ⊕ (Fin C.testCount ⊕ (Fin r ⊕
    ((Σ t, Fin (gateDim C t)) ⊕ ((Σ t, Fin (gateDim C t)) ⊕ Bool))))
  exact ⟨size U,(SourceSize.connectionEquiv C).trans (equiv (α := U))⟩

instance comparisonCode {T : Type} [FiniteCode T] {r : ℕ} (C : AddressedCircuit.Circuit T r) :
    FiniteCode (Comparison C) := by
  letI := fintype T
  let U := Fin C.seedCount ⊕ (Connection C × Option Bool)
  exact ⟨size U,(SourceSize.comparisonEquiv C).trans (equiv (α := U))⟩

section Layout
variable {F T E : Type} [Field F] [FiniteCode T] [FiniteCode E] {r : ℕ}
  (C : ComparisonData F T E r) (L : ℕ)

-- These named definitions also check that all dependent product-domain
-- filters have computable decision procedures and numeric enumerations.
abbrev cornerCode : FiniteCode (C.Corner L) := inferInstance
abbrev horizontalCode : FiniteCode (C.Horizontal L) := inferInstance
abbrev verticalCode : FiniteCode (C.Vertical L) := inferInstance
abbrev squareCode : FiniteCode (C.Square L) := inferInstance
abbrev readoutCode : FiniteCode (C.Readout L) := inferInstance
abbrev blockCode : FiniteCode (C.Block L) := inferInstance

end Layout

end GroupWL.FiniteCode
