import GroupWL.TensorVersionCaps

/-! Isomorphism invariance for the actual three group-WL relations and
identification among arbitrary finite comparison groups. -/
namespace GroupWL.Refinement

universe u v w
variable {G : Type u} {H : Type v} {K : Type w}
  [Group G] [Group H] [Group K] [Fintype G] [Fintype H] [Fintype K]
  {version : Version} {k : ℕ}

theorem GroupEquivalent.symm (h : GroupEquivalent version k G H) :
    GroupEquivalent version k H G := by
  cases version with
  | one => exact fun r => (h r).symm
  | two => exact fun r => (h r).symm
  | three =>
      change EquivalentIII k G H at h
      change EquivalentIII k H G
      unfold EquivalentIII at h ⊢
      by_cases hk : k = 1
      · simp only [if_pos hk] at h ⊢
        exact fun r => (h r).symm
      · simp only [if_neg hk] at h ⊢
        exact fun r => (h r).symm

theorem GroupEquivalent.trans (h : GroupEquivalent version k G H)
    (h' : GroupEquivalent version k H K) : GroupEquivalent version k G K := by
  cases version with
  | one => exact fun r => (h r).trans (h' r)
  | two => exact fun r => (h r).trans (h' r)
  | three =>
      change EquivalentIII k G H at h
      change EquivalentIII k H K at h'
      change EquivalentIII k G K
      unfold EquivalentIII at h h' ⊢
      by_cases hk : k = 1
      · simp only [if_pos hk] at h h' ⊢
        exact fun r => (h r).trans (h' r)
      · simp only [if_neg hk] at h h' ⊢
        exact fun r => (h r).trans (h' r)

/-- The reduction dimensions are always greater than one, so the concrete
isomorphism comparison for joint-vector colors applies in every version. -/
theorem groupEquivalent_transport_left (e : G ≃* H) (hk : k ≠ 1) :
    GroupEquivalent version k G K ↔ GroupEquivalent version k H K := by
  have he := TensorVersionCaps.groupEquivalent_of_isomorphic e version hk
  exact ⟨fun h => he.symm.trans h, fun h => he.trans h⟩

theorem groupEquivalent_transport_right (e : H ≃* K) (hk : k ≠ 1) :
    GroupEquivalent version k G H ↔ GroupEquivalent version k G K := by
  have he := TensorVersionCaps.groupEquivalent_of_isomorphic e version hk
  exact ⟨fun h => h.trans he, fun h => h.trans he.symm⟩

theorem identifies_transport (e : G ≃* H) (hk : k ≠ 1) :
    Identifies version k G ↔ Identifies version k H := by
  constructor
  · intro hi J hj
    obtain ⟨f⟩ := hi J ((groupEquivalent_transport_left e hk).mpr hj)
    exact ⟨e.symm.trans f⟩
  · intro hi J hj
    obtain ⟨f⟩ := hi J ((groupEquivalent_transport_left e hk).mp hj)
    exact ⟨e.trans f⟩

end GroupWL.Refinement
