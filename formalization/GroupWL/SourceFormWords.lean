import GroupWL.SourceFormEncoding
import GroupWL.WedgeConstraintEncoding

/-! The raw form-matrix table is the canonical residue matrix word. -/
namespace GroupWL.MachinePrograms.SourceRadicalTables

theorem collect_values (p : ℕ) (scope coefficients dimensions : List ℕ) (b r i : ℕ)
    (hp : 1<p) : ∀x∈collect p scope coefficients dimensions b r i,x<p := by
  induction i with
  | zero => simp only [collect,List.mem_replicate]; intro x hx; omega
  | succ i ih =>
    unfold collect update SourceRadicalColumn.update
    exact MatrixScatter.scatter_values _ _ _ _ _ _ _ p (by omega)
      (SourceRadicalClient.data_valid p scope coefficients b r i (dimensions[i]?.getD 0) hp).liftValues ih

end GroupWL.MachinePrograms.SourceRadicalTables

namespace GroupWL.ConstructiveIncidence
open IncidenceTensor ConstructiveCoordinates MachinePrograms
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [FiniteCode I] [FiniteCode J]
variable (p : ℕ) [Fact p.Prime]
variable {V : J → Type} [∀j,AddCommGroup (V j)] [∀j,Module (ZMod p) (V j)]
variable (A : AffineSystem (ZMod p) I J V) (R : ∀j,Coordinates (ZMod p) (ReadoutRadical A j)) (q : ℕ)

theorem formValue_lt (D : IncidenceFormMatrix.Data) (values : ∀x∈D.radicals,x<p) (i : ℕ) :
    IncidenceFormMatrix.value D i<p := by
  unfold IncidenceFormMatrix.value
  dsimp only
  split_ifs <;> first | exact (Fact.out : p.Prime).pos | exact (Fact.out : p.Prime).one_lt |
    exact MatrixArithmetic.read_lt values (Fact.out : p.Prime).pos _

theorem formData_forms (radicals : List ℕ) : IncidenceFormMatrix.forms (formData p A R q radicals)=
    FiniteCode.size (FormIndex A R q) := by
  change _+FiniteCode.size (Incidence A)*q*2=_+FiniteCode.size (Incidence A)*(q*2)
  dsimp only [formData]
  ring

theorem formData_word (radicals : List ℕ) (spec : RadicalTableSpec p A R radicals)
    (values : ∀x∈radicals,x<p) :
    List.ofFn (fun i : Fin (IncidenceFormMatrix.forms (formData p A R q radicals)*
        FiniteCode.size (OldInputIndex A R q)) => IncidenceFormMatrix.value (formData p A R q radicals) i.val)=
      formMatrix p A R q := by
  simp only [formData_forms]
  apply MatrixEncoding.ofFn_eq_word
  intro f i
  erw [CachedElimination.ofLinear_entry]
  have h := congrArg ZMod.val (formData_value p A R q radicals spec
    ((FiniteCode.equiv (α:=FormIndex A R q)).symm f) i)
  simp only [Equiv.apply_symm_apply] at h
  simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt
    (formValue_lt p (formData p A R q radicals) values _)] using h

end GroupWL.ConstructiveIncidence
