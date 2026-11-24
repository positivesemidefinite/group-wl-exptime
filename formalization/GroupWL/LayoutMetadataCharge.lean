import GroupWL.LayoutMetadataForms
import GroupWL.CircuitComparisonCodes

/-! The numeric charge selects the last-coordinate seam of precisely the
canonical rejecting comparison. -/
namespace GroupWL.LayoutMetadata
open SourceLayout
variable {T E : Type} [FiniteCode T] [FiniteCode E] {r : ℕ}
  (p : ℕ) [Fact p.Prime] (C : ComparisonData (ZMod p) T E r) (L : ℕ)

theorem squareCharge_correct (chargedComparison : ℕ) (s : C.Square L) :
    squareCharge (ComparisonMetadata.ofComparison p C) L chargedComparison (squareKey p C L s)=
      (C.sourceShift (L:=L) (fun e => if (FiniteCode.equiv e).val=chargedComparison then 1 else 0) (.inr s)).val := by
  letI : Fact (1<p) := ⟨(Fact.out : p.Prime).one_lt⟩
  have hs := squareKey_parts p C L s
  simp only [squareCharge,ComparisonMetadata.ofComparison,hs.1,hs.2.1]
  rcases s with ⟨l,i,a,b⟩
  cases l with
  | first e =>
      have hn : (FiniteCode.equiv e).val≠FiniteCode.size E+FiniteCode.size E*L+chargedComparison := by
        have := (FiniteCode.equiv e).isLt
        omega
      simp [link_first_val,hn,ComparisonData.sourceShift,ComparisonData.rowMarker,ComparisonData.linkConstant]
  | middle e j =>
      have hn : FiniteCode.size E+(FiniteCode.equiv e).val*L+j.val≠
          FiniteCode.size E+FiniteCode.size E*L+chargedComparison := by
        have := (middle_bounds L e j).2
        omega
      simp [link_middle_val,hn,ComparisonData.sourceShift,ComparisonData.rowMarker,ComparisonData.linkConstant]
  | last e =>
      simp only [link_last_val,Nat.add_left_cancel_iff,ComparisonData.sourceShift,ComparisonData.rowMarker,ComparisonData.linkConstant]
      by_cases hrow : i.val+1=r <;> by_cases he : (FiniteCode.equiv e).val=chargedComparison <;>
        simp [hrow,he,ZMod.val_one]

end GroupWL.LayoutMetadata

namespace GroupWL.CircuitComparisonCodes
open CircuitComparisons AddressedCircuit
variable {T : Type} [FiniteCode T] {r : ℕ} (C : Circuit T r)

theorem rejecting_comparison_code :
    (FiniteCode.equiv (Comparison.sum (Connection.broadcastIdentity (C:=C) true))).val=
      FiniteCode.size (Comparison C)-3 := by
  rw [comparison_sum,connection_broadcastIdentity,size_comparison]
  simp only [ite_true]
  unfold connectionCount
  omega

theorem rejectingConstant_eq_code {F : Type*} [Field F] (e : Comparison C) :
    rejectingConstant C F e=(if (FiniteCode.equiv e).val=FiniteCode.size (Comparison C)-3 then 1 else 0 : F) := by
  have he : (FiniteCode.equiv e).val=FiniteCode.size (Comparison C)-3 ↔
      e=Comparison.sum (Connection.broadcastIdentity (C:=C) true) := by
    rw [←rejecting_comparison_code C,←Fin.ext_iff]
    exact FiniteCode.equiv.injective.eq_iff
  by_cases hc : (FiniteCode.equiv e).val=FiniteCode.size (Comparison C)-3
  · have heq := he.mp hc
    subst e
    simp [rejectingConstant,hc]
  have hn := mt he.mpr hc
  simp only [if_neg hc]
  cases e with
  | seed k => simp [rejectingConstant]
  | copy e b => simp [rejectingConstant]
  | sum e =>
      cases e with
      | circuit e => simp [rejectingConstant]
      | test e => simp [rejectingConstant]
      | flip i => simp [rejectingConstant]
      | broadcast t k => simp [rejectingConstant]
      | identity t k => simp [rejectingConstant]
      | broadcastIdentity b => cases b <;> simp_all [rejectingConstant]

end GroupWL.CircuitComparisonCodes
