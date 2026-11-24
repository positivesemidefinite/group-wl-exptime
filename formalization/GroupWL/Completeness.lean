import GroupWL.IdentificationThreeMembership
import GroupWL.MachinePrograms.VersionThreeEquivalence
import GroupWL.MachinePrograms.CircuitWriterReduction

namespace GroupWL.Statement
open Complexity Refinement MachinePrograms.CircuitWriterReduction

theorem equivalence_all_inEXPTIME (p : ℕ) (hp : p.Prime) (odd : p ≠ 2) :
    letI : Fact p.Prime := ⟨hp⟩
    ∀ version encoding, InEXPTIME (equivalenceLanguage p version encoding) := by
  letI : Fact p.Prime := ⟨hp⟩
  intro version encoding
  cases version with
  | one => exact (equivalence_one_two_inEXPTIME p hp odd encoding).1
  | two => exact (equivalence_one_two_inEXPTIME p hp odd encoding).2
  | three => exact equivalence_three_inEXPTIME p hp odd encoding

theorem HardWithOutputs.hard {L U : Language} (h : HardWithOutputs L U) : EXPTIMEHard L := by
  intro S hS
  obtain ⟨M,f,c,d,run,yes,_⟩ := h S hS
  exact ⟨M,f,c,d,run,yes⟩

theorem fullClaim_of_writers (p : ℕ) (hp : p.Prime) (odd : p ≠ 2) :
    letI : Fact p.Prime := ⟨hp⟩
    (∀ v enc, Nonempty (Writer p .identification v enc) ∧ Nonempty (Writer p .equivalence v enc)) →
    FullClaim p := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero (2 : ZMod p) := ⟨two_ne_zero_of_prime_ne_two p hp odd⟩
  intro writers v enc
  obtain ⟨⟨wi⟩,⟨we⟩⟩ := writers v enc
  have odd' : Odd p := hp.odd_of_ne_two odd
  have hi := identification_hard odd' v enc wi
  have he := equivalence_hard odd' v enc we
  exact ⟨⟨identification_all_inEXPTIME p hp odd v enc,hi.hard⟩,
    ⟨equivalence_all_inEXPTIME p hp odd v enc,he.hard⟩,hi,he⟩
end GroupWL.Statement
