import GroupWL.CircuitReductionCorrectness
import GroupWL.InputParsing

/-! Correctness of the actual bit-string outputs for both encodings. -/
namespace GroupWL.CircuitGroupReduction

open AddressedCircuit Refinement Statement

theorem dimension_le_quadratic (version : Version) (r : ℕ) :
    dimension version r ≤ 146*(r+1)^2 := by
  have h : dimension version r ≤ Parameters.ringBudget r+46 := by
    cases version <;>
      simp only [dimension, Parameters.dimensionI, Parameters.dimensionII,
        Parameters.dimensionIII] <;> omega
  apply h.trans
  unfold Parameters.ringBudget Parameters.frameWidth Parameters.blockBudget
  nlinarith

theorem dimensionWord_length_le_quadratic (version : Version)
    (encoding : DimensionEncoding) (r : ℕ) :
    (dimensionWord encoding (dimension version r)).length ≤ 146*(r+1)^2 :=
  (dimensionWord_length_le encoding _).trans (dimension_le_quadratic version r)

variable (p : ℕ) [Fact p.Prime] [NeZero (2 : ZMod p)]
variable {T : Type} [Fintype T] {n : ℕ} (C : Circuit T (n+3))

noncomputable def identificationOutput (version : Version) (encoding : DimensionEncoding) :
    Complexity.BitString :=
  identificationWord p encoding (baseDescription p C) (dimension version (n+3))

noncomputable def equivalenceOutput (version : Version) (encoding : DimensionEncoding) :
    Complexity.BitString :=
  equivalenceWord p encoding (baseDescription p C) (mateDescription p C)
    (dimension version (n+3))

/-- Exact target-language membership, for either unary or canonical binary k. -/
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

end GroupWL.CircuitGroupReduction
