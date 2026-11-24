import GroupWL.EquivalenceMembership
import GroupWL.MachinePrograms.IdentificationMembership

/-! Completed identification membership under the original manuscript hypotheses. -/
namespace GroupWL.Statement

theorem identification_one_two_inEXPTIME (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    letI : Fact p.Prime := ⟨hp⟩
    ∀ encoding, Complexity.InEXPTIME (identificationLanguage p .one encoding) ∧
      Complexity.InEXPTIME (identificationLanguage p .two encoding) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero (2 : ZMod p) := ⟨two_ne_zero_of_prime_ne_two p hp hodd⟩
  intro encoding
  exact ⟨MachinePrograms.RawIdentification.versionI_inEXPTIME p encoding,
    MachinePrograms.RawIdentification.versionII_inEXPTIME p encoding⟩

end GroupWL.Statement
