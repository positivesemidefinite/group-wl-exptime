import GroupWL.CircuitDenseReduction
import GroupWL.CircuitSolvability

/-! Complete semantic correctness of the actual addressed-circuit reduction.
The accepting affine, reconstruction and ring-transfer hypotheses have all
been discharged. Operational construction time is handled separately. -/
namespace GroupWL.CircuitGroupReduction

open AddressedCircuit CircuitComparisons Refinement

variable (p : ℕ) [Fact p.Prime] [NeZero (2 : ZMod p)]
variable {T : Type} [Fintype T] {n : ℕ} (C : Circuit T (n+3))

/-- Acceptance identifies the constructed group among all finite groups. -/
theorem acceptance_identifies (hodd : Odd p) (haccept : C.Accepts) (version : Version) :
    Refinement.Identifies version (dimension version (n+3)) (Base p C) :=
  identifies_of_scalarImageSolvability p C
    (accepting_scalarImageSolvability C (wireLength n) haccept) hodd version

theorem identifies_iff_accepts (hodd : Odd p) (version : Version) :
    Refinement.Identifies version (dimension version (n+3)) (Base p C) ↔ C.Accepts := by
  constructor
  · intro hi
    by_contra hn
    exact rejection_not_identified p C hn version hi
  · exact fun h => acceptance_identifies p C hodd h version

/-- The fixed nonisomorphic pair is equivalent precisely on rejecting inputs. -/
theorem equivalent_iff_rejects (hodd : Odd p) (version : Version) :
    GroupEquivalent version (dimension version (n+3)) (Base p C) (Mate p C) ↔
      ¬ C.Accepts := by
  constructor
  · intro he ha
    exact nonisomorphic p C
      (acceptance_identifies p C hodd ha version ⟨Mate p C,inferInstance,inferInstance⟩ he)
  · exact fun h => rejection_equivalent p C h version

/-- The actual dense tensor description satisfies exactly the identification
predicate used in the computational target. -/
theorem baseDescription_identifies_iff_accepts (hodd : Odd p) (version : Version) :
    Refinement.Identifies version (dimension version (n+3)) (baseDescription p C).Carrier ↔
      C.Accepts :=
  (baseDescription_identifies_iff p C version).trans (identifies_iff_accepts p C hodd version)

/-- Dense output pairs have precisely the rejecting equivalence behavior. -/
theorem descriptions_equivalent_iff_rejects (hodd : Odd p) (version : Version) :
    GroupEquivalent version (dimension version (n+3))
      (baseDescription p C).Carrier (mateDescription p C).Carrier ↔ ¬ C.Accepts :=
  (descriptions_equivalent_iff p C version).trans (equivalent_iff_rejects p C hodd version)

/-- Both correctness directions and every group-output restriction hold for
each circuit, independently of how a machine is compiled into that circuit. -/
theorem circuit_reduction_correct (hodd : Odd p) (version : Version) :
    (Refinement.Identifies version (dimension version (n+3)) (baseDescription p C).Carrier ↔
      C.Accepts) ∧
    (GroupEquivalent version (dimension version (n+3))
      (baseDescription p C).Carrier (mateDescription p C).Carrier ↔ ¬ C.Accepts) ∧
    Statement.HardGroup p (baseDescription p C) ∧
    Statement.HardGroup p (mateDescription p C) ∧
    ¬ Nonempty ((baseDescription p C).Carrier ≃* (mateDescription p C).Carrier) :=
  ⟨baseDescription_identifies_iff_accepts p C hodd version,
    descriptions_equivalent_iff_rejects p C hodd version,
    baseDescription_hardGroup p C, mateDescription_hardGroup p C,
    descriptions_nonisomorphic p C⟩

end GroupWL.CircuitGroupReduction
