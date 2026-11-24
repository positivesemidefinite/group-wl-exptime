import GroupWL.SourceFiniteCodes
import GroupWL.MachinePrograms.CircuitParserCost
import GroupWL.MachinePrograms.FilterRanksSemantics

/-! Numeric constructor offsets for circuit comparison metadata. -/
namespace GroupWL.CircuitComparisonCodes
open CircuitComparisons AddressedCircuit
open scoped BigOperators
variable {T : Type} [FiniteCode T] {r : ℕ} (C : Circuit T r)

abbrev gatePorts := Σt,Fin (gateDim C t)
def portCount : ℕ := FiniteCode.size (gatePorts C)
def connectionCount : ℕ := C.edges+C.testCount+r+portCount C+portCount C+2

theorem size_primary : FiniteCode.size (Primary T)=FiniteCode.size T+2 := rfl
theorem size_connection : FiniteCode.size (Connection C)=connectionCount C := by
  change C.edges+(C.testCount+(r+(portCount C+(portCount C+2))))=_
  unfold connectionCount; omega

theorem size_realType : FiniteCode.size (RealType C)=FiniteCode.size T+2+connectionCount C := by
  change FiniteCode.size (Primary T)+FiniteCode.size (Connection C)=_
  rw [size_primary,size_connection]
theorem size_comparison : FiniteCode.size (Comparison C)=C.seedCount+connectionCount C*3 := by
  change C.seedCount+FiniteCode.size (Connection C)*3=_
  rw [size_connection]

theorem primary_gate (t : T) : (FiniteCode.equiv (Primary.gate t)).val=(FiniteCode.equiv t).val := rfl
theorem primary_broadcast : (FiniteCode.equiv (Primary.broadcast : Primary T)).val=FiniteCode.size T := by rfl
theorem primary_dummy : (FiniteCode.equiv (Primary.dummy : Primary T)).val=FiniteCode.size T+1 := by rfl

theorem connection_circuit (e : Fin C.edges) :
    (FiniteCode.equiv (Connection.circuit e)).val=e.val := rfl
theorem connection_test (k : Fin C.testCount) :
    (FiniteCode.equiv (Connection.test k)).val=C.edges+k.val := rfl
theorem connection_flip (i : Fin r) :
    (FiniteCode.equiv (Connection.flip (C:=C) i)).val=C.edges+C.testCount+i.val := by
  change C.edges+(C.testCount+i.val)=_; omega
theorem connection_broadcast (t : T) (k : Fin (gateDim C t)) :
    (FiniteCode.equiv (Connection.broadcast t k)).val=C.edges+C.testCount+r+
      (FiniteCode.equiv (⟨t,k⟩ : gatePorts C)).val := by
  change C.edges+(C.testCount+(r+(FiniteCode.equiv (⟨t,k⟩ : gatePorts C)).val))=_; omega
theorem connection_identity (t : T) (k : Fin (gateDim C t)) :
    (FiniteCode.equiv (Connection.identity t k)).val=C.edges+C.testCount+r+portCount C+
      (FiniteCode.equiv (⟨t,k⟩ : gatePorts C)).val := by
  change C.edges+(C.testCount+(r+(portCount C+(FiniteCode.equiv (⟨t,k⟩ : gatePorts C)).val)))=_; omega
theorem connection_broadcastIdentity (b : Bool) :
    (FiniteCode.equiv (Connection.broadcastIdentity (C:=C) b)).val=
      C.edges+C.testCount+r+portCount C+portCount C+(if b then 1 else 0) := by
  cases b with
  | false => change C.edges+(C.testCount+(r+(portCount C+(portCount C+0))))=_; simp; omega
  | true => change C.edges+(C.testCount+(r+(portCount C+(portCount C+1))))=_; simp; omega

theorem real_primary (t : Primary T) :
    (FiniteCode.equiv (Sum.inl t : RealType C)).val=(FiniteCode.equiv t).val := rfl
theorem real_buffer (e : Connection C) :
    (FiniteCode.equiv (Sum.inr e : RealType C)).val=FiniteCode.size T+2+(FiniteCode.equiv e).val := rfl

theorem comparison_seed (k : Fin C.seedCount) :
    (FiniteCode.equiv (Comparison.seed k)).val=k.val := rfl
theorem comparison_sum (e : Connection C) :
    (FiniteCode.equiv (Comparison.sum e)).val=C.seedCount+(FiniteCode.equiv e).val*3 := by
  change C.seedCount+(0+3*(FiniteCode.equiv e).val)=_; omega
theorem comparison_copy (e : Connection C) (b : Bool) :
    (FiniteCode.equiv (Comparison.copy e b)).val=C.seedCount+(FiniteCode.equiv e).val*3+
      (if b then 2 else 1) := by
  cases b with
  | false => change C.seedCount+(1+3*(FiniteCode.equiv e).val)=_; simp; omega
  | true => change C.seedCount+(2+3*(FiniteCode.equiv e).val)=_; simp; omega

end GroupWL.CircuitComparisonCodes
