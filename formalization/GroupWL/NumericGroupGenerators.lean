import GroupWL.MachinePrograms.GeneratorSearch
import GroupWL.PGroupCandidates

/-! The exact first numeric generating tuple selected by the operational
search, using the same least-significant-coordinate-first enumeration. -/
namespace GroupWL.NumericGroupGenerators
open Refinement MachinePrograms
variable {p D : ℕ} [Fact p.Prime]

def identity (t : Group (Fin (p^D))) : Fin (p^D) := @One.one _ t.toOne
def operation (t : Group (Fin (p^D))) : Fin (p^D) → Fin (p^D) → Fin (p^D) := @Mul.mul _ t.toMul

def predicate (t : Group (Fin (p^D))) : ℕ → Prop := by
  letI := t
  exact GeneratorSearch.Accepts (k:=D) (identity t) (operation t)
instance predicateDecidable (t : Group (Fin (p^D))) : DecidablePred (predicate t) := by
  letI := t
  unfold predicate
  infer_instance

theorem first_exists (t : Group (Fin (p^D))) :
    ∃i,i<(p^D)^D ∧ NatArrayPredicateSearch.hit (predicate t) ((p^D)^D)=some i ∧ predicate t i := by
  letI := t
  have hex : ∃i<(p^D)^D,predicate t i := by
    obtain ⟨a,ha⟩ := PGroupDecomposition.exists_generating_tuple (p:=p) (D:=D) (G:=Fin (p^D))
      (by simp [Nat.card_eq_fintype_card])
    let i := finFunctionFinEquiv a
    refine ⟨i.val,i.isLt,?_⟩
    apply (GeneratorSearch.accepts_iff (Equiv.refl (Fin (p^D))) (operation t) (fun _ _ => rfl) i).mpr
    simpa [i,Function.comp_def] using ha
  exact NatArrayPredicateSearch.hit_exists _ _ hex

def index (t : Group (Fin (p^D))) : Fin ((p^D)^D) :=
  ⟨(NatArrayPredicateSearch.hit (predicate t) ((p^D)^D)).getD 0,by
    obtain ⟨i,hi,hh,_⟩ := first_exists t
    simpa [hh] using hi⟩

def generators (t : Group (Fin (p^D))) : Fin D → Fin (p^D) := finFunctionFinEquiv.symm (index t)

theorem generators_generate (t : Group (Fin (p^D))) :
    letI := t
    Generates (generators t) := by
  letI := t
  obtain ⟨i,hi,hh,hgood⟩ := first_exists t
  have idx : (index t).val=i := by simp [index,hh]
  have good : predicate t (index t).val := by rw [idx]; exact hgood
  have hg := (GeneratorSearch.accepts_iff (Equiv.refl (Fin (p^D))) (operation t) (fun _ _ => rfl) (index t)).mp good
  simpa [generators,Function.comp_def] using hg

end GroupWL.NumericGroupGenerators
