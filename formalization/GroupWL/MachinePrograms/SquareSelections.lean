import GroupWL.MachinePrograms.SquareSelected

/-! All four compact endpoint arrays, retained simultaneously. -/
namespace GroupWL.MachinePrograms.SquareSelections
open NatArrayLanguage
set_option maxHeartbeats 2000000
abbrev Endpoint := SquareIndices.Endpoint
abbrev Reg := SquareSelected.Reg⊕Unit
abbrev Arr := SquareSelected.Arr⊕Endpoint
abbrev State := Store Reg Arr
abbrev Code := NatArrayLanguage.Program Reg Arr

def save (which : Endpoint) : Atom Reg Arr := .copyArray (.inr which) (.inl (.inr .output))
def one (which : Endpoint) : Code := .seq ((SquareSelected.program which).map Sum.inl Sum.inl)
  (.atom (save which))
def program : Code := .seq (one .left) (.seq (one .right) (.seq (one .before) (one .after)))

theorem one_runs (which : Endpoint) (C : ComparisonMetadata.Table) (L M : ℕ) (S : State)
    (bounded : S.Bounded M) (input : SquareSelected.Input C L S.left)
    (valid : SquareIndices.Data.Valid (SquareIndices.layoutData C L) M) (binary : ∀x∈C.domain,x≤1) :
    ∃t≤49*(LayoutMetadata.linkCount C L*C.coordinates*4)+14,∃T,
      Runs (storageBound Reg Arr M) (one which) S t T ∧ T.Bounded M ∧
      SquareSelected.Input C L T.left ∧ T.array (.inr which)=SquareSelected.word C L which ∧
      ∀other,other≠which→T.array (.inr other)=S.array (.inr other) := by
  obtain ⟨t,ht,U,run,hU,hu,hout⟩ := SquareSelected.program_runs which C L M S.left bounded.left input valid binary
  let V := U.join S.right
  have hV : V.Bounded M := hU.join bounded.right
  have copy := atom_runs hV (save which) trivial trivial
  refine ⟨t+1,by omega,(save which).apply V,(run.left_bounded bounded).seq copy,
    (save which).apply_bounded hV trivial,?_,?_,?_⟩
  · exact hu
  · simpa [save,Atom.apply,Store.setArray,V] using hout
  · intro other hne
    simp [save,Atom.apply,Store.setArray,hne,V,Store.right]

theorem program_runs (C : ComparisonMetadata.Table) (L M : ℕ) (S : State)
    (bounded : S.Bounded M) (input : SquareSelected.Input C L S.left)
    (valid : SquareIndices.Data.Valid (SquareIndices.layoutData C L) M) (binary : ∀x∈C.domain,x≤1) :
    ∃t≤196*(LayoutMetadata.linkCount C L*C.coordinates*4)+56,∃T,
      Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧
      SquareSelected.Input C L T.left ∧ ∀which,T.array (.inr which)=SquareSelected.word C L which := by
  obtain ⟨a,ha,A,ra,hA,pa,oa,fa⟩ := one_runs .left C L M S bounded input valid binary
  obtain ⟨b,hb,B,rb,hB,pb,ob,fb⟩ := one_runs .right C L M A hA pa valid binary
  obtain ⟨c,hc,D,rc,hD,pd,od,fd⟩ := one_runs .before C L M B hB pb valid binary
  obtain ⟨e,he,T,re,hT,pt,ot,ft⟩ := one_runs .after C L M D hD pd valid binary
  refine ⟨a+(b+(c+e)),by omega,T,ra.seq (rb.seq (rc.seq re)),hT,pt,?_⟩
  intro which
  cases which with
  | left => rw [ft _ (by decide),fd _ (by decide),fb _ (by decide)];exact oa
  | right => rw [ft _ (by decide),fd _ (by decide)];exact ob
  | before => rw [ft _ (by decide)];exact od
  | after => exact ot

end GroupWL.MachinePrograms.SquareSelections
