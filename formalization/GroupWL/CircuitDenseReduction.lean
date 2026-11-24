import GroupWL.CircuitGroupReduction

/-! Actual dense tensor outputs for the circuit-to-group construction.
These semantic descriptions use chosen finite bases. Constructive basis
selection and operational construction costs are separate obligations. -/
namespace GroupWL.CircuitGroupReduction

open AddressedCircuit CircuitComparisons IncidenceTensor DenseTensorEncoding Refinement

variable (p : ℕ) [Fact p.Prime] [NeZero (2 : ZMod p)]
variable {T : Type} [Fintype T] {n : ℕ} (C : Circuit T (n+3))

noncomputable def baseDescription : Statement.TensorDescription p :=
  incidenceDescription p (system p C) (Parameters.frameWidth (n+3))
    (lt_of_lt_of_le (by decide) (frameWidth_ge_two (n+3))) AlternatingBilinearMap.zero

noncomputable def mateDescription : Statement.TensorDescription p :=
  incidenceDescription p (system p C) (Parameters.frameWidth (n+3))
    (lt_of_lt_of_le (by decide) (frameWidth_ge_two (n+3)))
    (epsilonCharge (system p C) (Parameters.frameWidth (n+3))
      (frameWidth_ge_two (n+3)) (charge p C))

noncomputable def baseDescriptionEquiv : Base p C ≃* (baseDescription p C).Carrier :=
  incidenceDescriptionMulEquiv p (system p C) (Parameters.frameWidth (n+3))
    (lt_of_lt_of_le (by decide) (frameWidth_ge_two (n+3))) AlternatingBilinearMap.zero

noncomputable def mateDescriptionEquiv : Mate p C ≃* (mateDescription p C).Carrier :=
  incidenceDescriptionMulEquiv p (system p C) (Parameters.frameWidth (n+3))
    (lt_of_lt_of_le (by decide) (frameWidth_ge_two (n+3)))
    (epsilonCharge (system p C) (Parameters.frameWidth (n+3))
      (frameWidth_ge_two (n+3)) (charge p C))

theorem baseDescription_hardGroup : Statement.HardGroup p (baseDescription p C) := by
  letI := block_nonempty p C
  exact incidenceDescription_hardGroup p (system p C) (Parameters.frameWidth (n+3))
    (frameWidth_ge_three (n+3)) AlternatingBilinearMap.zero

theorem mateDescription_hardGroup : Statement.HardGroup p (mateDescription p C) := by
  letI := block_nonempty p C
  exact incidenceDescription_hardGroup p (system p C) (Parameters.frameWidth (n+3))
    (frameWidth_ge_three (n+3))
    (epsilonCharge (system p C) (Parameters.frameWidth (n+3))
      (frameWidth_ge_two (n+3)) (charge p C))

/-- Every dense output pair is nonisomorphic, without an acceptance premise. -/
theorem descriptions_nonisomorphic :
    ¬ Nonempty ((baseDescription p C).Carrier ≃* (mateDescription p C).Carrier) := by
  rintro ⟨e⟩
  exact nonisomorphic p C
    ⟨(baseDescriptionEquiv p C).trans (e.trans (mateDescriptionEquiv p C).symm)⟩

theorem descriptions_equivalent_iff (version : Version) :
    GroupEquivalent version (dimension version (n+3))
        (baseDescription p C).Carrier (mateDescription p C).Carrier ↔
      GroupEquivalent version (dimension version (n+3)) (Base p C) (Mate p C) := by
  have hk : dimension version (n+3) ≠ 1 := by
    have := dimension_gt_one version (n+3)
    omega
  exact ((groupEquivalent_transport_left (baseDescriptionEquiv p C) hk).trans
    (groupEquivalent_transport_right (mateDescriptionEquiv p C) hk)).symm

theorem baseDescription_identifies_iff (version : Version) :
    Refinement.Identifies version (dimension version (n+3)) (baseDescription p C).Carrier ↔
      Refinement.Identifies version (dimension version (n+3)) (Base p C) := by
  apply (identifies_transport (baseDescriptionEquiv p C) _).symm
  have := dimension_gt_one version (n+3)
  omega

theorem rejection_descriptions_equivalent (hreject : ¬ C.Accepts) (version : Version) :
    GroupEquivalent version (dimension version (n+3))
      (baseDescription p C).Carrier (mateDescription p C).Carrier :=
  (descriptions_equivalent_iff p C version).mpr (rejection_equivalent p C hreject version)

theorem rejection_baseDescription_not_identified (hreject : ¬ C.Accepts) (version : Version) :
    ¬ Refinement.Identifies version (dimension version (n+3)) (baseDescription p C).Carrier :=
  fun h => rejection_not_identified p C hreject version
    ((baseDescription_identifies_iff p C version).mp h)

end GroupWL.CircuitGroupReduction

namespace GroupWL.Statement

open scoped commutatorElement
variable {p : ℕ} [Fact p.Prime] {T U : TensorDescription p}

/-- The output restriction is invariant under any proved change of dense
coordinates, including a separately implemented constructive basis choice. -/
theorem HardGroup.transport (e : T.Carrier ≃* U.Carrier) (h : HardGroup p T) :
    HardGroup p U := by
  refine ⟨fun g => TensorGroup.pow_char_eq_one p g,
    fun g h x => TensorGroup.commutator_central g h x, ?_,
    DenseTensorEncoding.center_eq_derived_transport e h.2.2.2⟩
  obtain ⟨g,h',hne⟩ := h.2.2.1
  refine ⟨e g,e h',?_⟩
  intro he
  apply hne
  change g*h'=h'*g
  apply e.injective
  simpa only [map_mul] using he.eq

end GroupWL.Statement
