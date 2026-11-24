import GroupWL.MachinePrograms.SourceCoefficientTable

namespace GroupWL.MachinePrograms.SourceCoefficients

theorem coefficient_lt (S : State) (hp : 0<S.scalar .modulus) :
    coefficient S<S.scalar .modulus := by
  unfold coefficient
  split
  · exact hp
  · exact Nat.mod_lt _ hp

end GroupWL.MachinePrograms.SourceCoefficients
