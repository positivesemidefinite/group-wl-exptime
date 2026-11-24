import GroupWL.ComputableCircuitReduction
import GroupWL.ConstructiveGroupBridge
import GroupWL.CircuitReductionWords
import GroupWL.IncidenceGroupCongruence

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

/-! Correctness of the executable dense outputs, obtained by an actual group
isomorphism to the construction whose game bounds have already been proved. -/
namespace GroupWL.ConstructiveSourceTensor

open SourceLayout IncidenceTensor FrameResponses

variable {T E : Type} [FiniteCode T] [FiniteCode E] [Fintype T] [Fintype E]
  {r : ℕ} (p : ℕ) [Fact p.Prime] (D : ComparisonData (ZMod p) T E r) (L q : ℕ)

noncomputable def zeroDescriptionEquiv (hq : 2 ≤ q) :
    ZeroGroup (D.affineSystem (L := L)) q hq ≃*
      (zeroDescription L p D q (by omega)).Carrier := by
  have hs : system D L = D.affineSystem (L := L) := by
    unfold system
    exact ComputableSource.affineSystem_eq D
  letI : Fintype (D.Block L) := FiniteCode.fintype _
  letI : Fintype (D.Readout L) := FiniteCode.fintype _
  letI : DecidableEq (D.Block L) := (FiniteCode.equiv (α := D.Block L)).decidableEq
  letI : DecidableEq (D.Readout L) := (FiniteCode.equiv (α := D.Readout L)).decidableEq
  let e := (ConstructiveGroupBridge.zeroGroupEquiv (system D L) (radicalCoordinates D L) q hq).trans
    (ConstructiveTensor.descriptionMulEquiv q p (system D L) (radicalCoordinates D L)
      (by omega) AlternatingBilinearMap.zero)
  exact (IncidenceGroupCongruence.zero D.blockFintype (instFintypeBlock D L)
    D.readoutFintype (instFintypeReadout D L) D.readoutDecidableEq (instDecidableEqReadout D L)
    D.affineSystem (system D L) hs.symm q hq).trans e

noncomputable def chargedDescriptionEquiv (hq : 2 ≤ q) (β : D.Block L → ZMod p) :
    ChargedGroup (D.affineSystem (L := L)) q hq β ≃*
      (chargedDescription L p D q hq β).Carrier := by
  have hs : system D L = D.affineSystem (L := L) := by
    unfold system
    exact ComputableSource.affineSystem_eq D
  letI : Fintype (D.Block L) := FiniteCode.fintype _
  letI : Fintype (D.Readout L) := FiniteCode.fintype _
  letI : DecidableEq (D.Block L) := (FiniteCode.equiv (α := D.Block L)).decidableEq
  letI : DecidableEq (D.Readout L) := (FiniteCode.equiv (α := D.Readout L)).decidableEq
  let e := (ConstructiveGroupBridge.chargedGroupEquiv (system D L) (radicalCoordinates D L) q hq β).trans
    (ConstructiveTensor.descriptionMulEquiv q p (system D L) (radicalCoordinates D L)
      (by omega) (epsilonCharge (system D L) q hq β))
  exact (IncidenceGroupCongruence.charged D.blockFintype (instFintypeBlock D L)
    D.readoutFintype (instFintypeReadout D L) D.blockDecidableEq (instDecidableEqBlock D L)
    D.readoutDecidableEq (instDecidableEqReadout D L)
    D.affineSystem (system D L) hs.symm q hq β).trans e

end GroupWL.ConstructiveSourceTensor

namespace GroupWL.ComputableCircuitReduction

open AddressedCircuit CircuitComparisons Refinement Statement
open CircuitGroupReduction (Base Mate dimension dimension_gt_one wireLength frameWidth_ge_two)

variable (p : ℕ) [Fact p.Prime] [NeZero (2 : ZMod p)]
variable {T : Type} [FiniteCode T] [Fintype T] {n : ℕ} (C : Circuit T (n+3))

noncomputable def baseDescriptionEquiv : Base p C ≃* (baseDescription p C).Carrier :=
  ConstructiveSourceTensor.zeroDescriptionEquiv p (comparisons C (ZMod p))
    (wireLength n) (Parameters.frameWidth (n+3)) (frameWidth_ge_two (n+3))

noncomputable def mateDescriptionEquiv : Mate p C ≃* (mateDescription p C).Carrier :=
  ConstructiveSourceTensor.chargedDescriptionEquiv p (comparisons C (ZMod p))
    (wireLength n) (Parameters.frameWidth (n+3)) (frameWidth_ge_two (n+3))
    (CircuitGroupReduction.charge p C)

theorem baseDescription_hardGroup : HardGroup p (baseDescription p C) :=
  HardGroup.transport
    ((CircuitGroupReduction.baseDescriptionEquiv p C).symm.trans (baseDescriptionEquiv p C))
    (CircuitGroupReduction.baseDescription_hardGroup p C)

theorem mateDescription_hardGroup : HardGroup p (mateDescription p C) :=
  HardGroup.transport
    ((CircuitGroupReduction.mateDescriptionEquiv p C).symm.trans (mateDescriptionEquiv p C))
    (CircuitGroupReduction.mateDescription_hardGroup p C)

theorem descriptions_nonisomorphic :
    ¬ Nonempty ((baseDescription p C).Carrier ≃* (mateDescription p C).Carrier) := by
  rintro ⟨e⟩
  exact CircuitGroupReduction.nonisomorphic p C
    ⟨(baseDescriptionEquiv p C).trans (e.trans (mateDescriptionEquiv p C).symm)⟩

theorem baseDescription_identifies_iff_accepts (hodd : Odd p) (version : Version) :
    Refinement.Identifies version (dimension version (n+3)) (baseDescription p C).Carrier ↔ C.Accepts := by
  have hk : dimension version (n+3) ≠ 1 := by have := dimension_gt_one version (n+3); omega
  exact (identifies_transport (baseDescriptionEquiv p C) hk).symm.trans
    (CircuitGroupReduction.identifies_iff_accepts p C hodd version)

theorem descriptions_equivalent_iff_rejects (hodd : Odd p) (version : Version) :
    GroupEquivalent version (dimension version (n+3))
      (baseDescription p C).Carrier (mateDescription p C).Carrier ↔ ¬ C.Accepts := by
  have hk : dimension version (n+3) ≠ 1 := by have := dimension_gt_one version (n+3); omega
  exact ((groupEquivalent_transport_left (baseDescriptionEquiv p C) hk).trans
    (groupEquivalent_transport_right (mateDescriptionEquiv p C) hk)).symm.trans
      (CircuitGroupReduction.equivalent_iff_rejects p C hodd version)

theorem identificationOutput_mem_iff (hodd : Odd p) (version : Version)
    (encoding : DimensionEncoding) :
    identificationOutput p C version encoding ∈ identificationLanguage p version encoding ↔
      C.Accepts :=
  (identificationWord_mem_iff p version encoding (baseDescription p C)
    (dimension version (n+3)) (lt_trans (by decide) (dimension_gt_one version (n+3)))).trans
    (baseDescription_identifies_iff_accepts p C hodd version)

theorem equivalenceOutput_mem_iff (hodd : Odd p) (version : Version)
    (encoding : DimensionEncoding) :
    equivalenceOutput p C version encoding ∈ equivalenceLanguage p version encoding ↔
      ¬ C.Accepts :=
  (equivalenceWord_mem_iff p version encoding (baseDescription p C) (mateDescription p C)
    (dimension version (n+3)) (lt_trans (by decide) (dimension_gt_one version (n+3)))).trans
    (descriptions_equivalent_iff_rejects p C hodd version)

theorem identificationOutput_hard (version : Version) (encoding : DimensionEncoding) :
    identificationOutput p C version encoding ∈ hardIdentificationInputs p encoding :=
  identificationWord_hard p encoding (baseDescription p C) (dimension version (n+3))
    (lt_trans (by decide) (dimension_gt_one version (n+3))) (baseDescription_hardGroup p C)

theorem equivalenceOutput_nonisomorphic (version : Version) (encoding : DimensionEncoding) :
    equivalenceOutput p C version encoding ∈ nonisomorphicPairInputs p encoding :=
  equivalenceWord_nonisomorphic p encoding (baseDescription p C) (mateDescription p C)
    (dimension version (n+3)) (lt_trans (by decide) (dimension_gt_one version (n+3)))
    (descriptions_nonisomorphic p C)

end GroupWL.ComputableCircuitReduction
