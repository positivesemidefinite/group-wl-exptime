import GroupWL.CircuitAcceptanceRows
import GroupWL.SourceIdentification

/-! The accepting source lemma for the actual circuit comparison system. -/
namespace GroupWL.CircuitComparisons

open AddressedCircuit SourceLayout SourceLayout.ComparisonData

variable {T F : Type*} {n L : ℕ} [Field F] [Fintype T]
  (C : Circuit T (n+3))

/-- Arbitrary accepting scalar-image data and zero site charges give a genuine
global solution of the concrete site-and-square affine system. -/
theorem accepting_solvable (hacc : C.Accepts)
    (β : (comparisons C F).Block L → F) (Q : (comparisons C F).ImageSets)
    (hsite : ∀ h : (comparisons C F).Horizontal L, β (.inl h) = 0)
    (hQ : (comparisons C F).ScalarImages β Q) :
    β ∈ LinearMap.range ((comparisons C F).affineSystem (L := L)).linearMap :=
  (comparisons C F).exists_global_solution β (acceptingRows C β) hsite
    (acceptingRows_comparison C β Q hQ hacc)

/-- Discharge exactly the affine acceptance premise used by arbitrary-group
identification. No recognition or structural assumptions on comparison groups
are added here. -/
theorem accepting_scalarImageSolvability {p : ℕ} [Fact p.Prime]
    {T : Type} [Fintype T] {n : ℕ} (C : Circuit T (n+3)) (L : ℕ)
    (hacc : C.Accepts) :
    SourceIdentification.ScalarImageSolvability (comparisons C (ZMod p)) L := by
  intro β Q hsite hQ
  exact accepting_solvable C hacc β Q hsite hQ

end GroupWL.CircuitComparisons
