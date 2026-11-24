import GroupWL.MachinePrograms.RawTableMembership

/-! Completed membership assertions under exactly the manuscript's prime hypotheses.
The all-version completeness theorem remains a separate proof obligation. -/
namespace GroupWL.Statement

theorem two_ne_zero_of_prime_ne_two (p : ℕ) (hp : p.Prime) (hodd : p≠2) :
    (2 : ZMod p)≠0 := by
  intro h
  have hd : p∣2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h)
  exact hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)

theorem equivalence_one_two_inEXPTIME (p : ℕ) (hp : p.Prime) (hodd : p≠2) :
    letI : Fact p.Prime := ⟨hp⟩
    ∀ encoding, Complexity.InEXPTIME (equivalenceLanguage p .one encoding) ∧
      Complexity.InEXPTIME (equivalenceLanguage p .two encoding) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero (2 : ZMod p) := ⟨two_ne_zero_of_prime_ne_two p hp hodd⟩
  intro encoding
  exact ⟨MachinePrograms.RawTableEquivalence.versionI_inEXPTIME p encoding,
    MachinePrograms.RawTableEquivalence.versionII_inEXPTIME p encoding⟩

end GroupWL.Statement
