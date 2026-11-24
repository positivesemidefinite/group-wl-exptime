import GroupWL.SourceLayout.System

namespace GroupWL.SourceLayout.ComparisonData
variable {F T E : Type*} [Field F] {r L : ℕ}
  (C : ComparisonData F T E r)

/-- A horizontal readout is owned by its site. A vertical readout is owned
by any square having it as its lower boundary. -/
noncomputable def readoutOwner : C.Readout L → C.Block L
  | .inl h => .inl h
  | .inr v => .inr ⟨v.1, v.2.1, v.2.2,
      ⟨(C.domain_nonempty v.1.comparison (finRotate r v.2.1)).choose,
        (C.domain_nonempty v.1.comparison (finRotate r v.2.1)).choose_spec⟩⟩

theorem readout_mem_owner_scope (j : C.Readout L) : j ∈ C.scope L (C.readoutOwner j) := by
  classical
  cases j with
  | inl h => simp [readoutOwner]
  | inr v => simp [readoutOwner, scope, squareBefore]

theorem readout_mem_affine_owner_scope [Fintype T] [Fintype E] (j : C.Readout L) :
    j ∈ (C.affineSystem (L := L)).scope (C.readoutOwner j) := C.readout_mem_owner_scope j

end GroupWL.SourceLayout.ComparisonData
