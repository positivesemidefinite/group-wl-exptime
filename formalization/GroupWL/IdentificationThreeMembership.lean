import GroupWL.IdentificationMembership
import GroupWL.MachinePrograms.IdentificationThree

/-! Identification in each group-WL version, in both dimension encodings. -/
namespace GroupWL.Statement

theorem identification_all_inEXPTIME (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    letI : Fact p.Prime := ⟨hp⟩
    ∀ version encoding, Complexity.InEXPTIME (identificationLanguage p version encoding) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero (2 : ZMod p) := ⟨two_ne_zero_of_prime_ne_two p hp hodd⟩
  intro version encoding
  cases version with
  | one => exact MachinePrograms.RawIdentification.versionI_inEXPTIME p encoding
  | two => exact MachinePrograms.RawIdentification.versionII_inEXPTIME p encoding
  | three => exact MachinePrograms.IdentificationThree.inEXPTIME p encoding

end GroupWL.Statement
