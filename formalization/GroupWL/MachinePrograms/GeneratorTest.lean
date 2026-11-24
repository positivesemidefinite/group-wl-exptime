import GroupWL.MachinePrograms.SeededSaturation
import GroupWL.MachinePrograms.MaskAll

/-! An executable generating-tuple test: mark the tuple, saturate under the
actual table, and scan the complete characteristic array. -/
namespace GroupWL.MachinePrograms.GeneratorTest
open NatArrayLanguage FiniteSetArrays Refinement
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

abbrev Reg := SeededSaturation.Reg ⊕ MaskAll.Reg
abbrev Arr := SeededSaturation.Arr ⊕ MaskAll.Arr
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def test : Code := sequence [
  SeededSaturation.saturate.map Sum.inl Sum.inl,
  .atom (.copyArray (.inr .input) (.inl (.inr .current))),
  MaskAll.check.map Sum.inr Sum.inr]

theorem test_runs (S : State) (n M : ℕ) (e : Fin n) (gs : List (Fin n))
    (op : Fin n → Fin n → Fin n)
    (hb : S.Bounded M) (hn : S.scalar (.inl (.inl .order))=n)
    (he : S.scalar (.inl (.inl .identity))=e.val)
    (hgens : S.array (.inl (.inl .generators))=gs.map Fin.val)
    (hn' : S.scalar (.inl (.inr .order))=n)
    (hlen : (S.array (.inl (.inr .table))).length=n*n)
    (hread : ∀ i : Fin (n*n),(S.array (.inl (.inr .table)))[i.val]?.getD 0=
      (op (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2).val)
    (hroom : n*n≤M) :
    ∃t≤10*n^3+13*n+5*gs.length+21,∃T,Runs (storageBound Reg Arr M) test S t T ∧
      T.Bounded M ∧ (T.scalar (.inr .result)=1 ↔
        GroupSaturation.closureSet op (insert e gs.toFinset) n=Finset.univ) := by
  obtain ⟨t,ht,U,close,hU,ho⟩ := SeededSaturation.saturate_runs S.left n M e gs op
    hb.left hn he hgens hn' hlen hread hroom
  let V := U.join S.right
  have hV : V.Bounded M := hU.join hb.right
  let W := (Atom.copyArray (Sum.inr MaskAll.Arr.input)
    (Sum.inl (Sum.inr GroupSaturation.Arr.current))).apply V
  have hW : W.Bounded M := Atom.apply_bounded hV _ trivial
  have copy := atom_runs hV (.copyArray (.inr .input) (.inl (.inr .current))) trivial trivial
  have hcurrent : W.right.array .input=word (GroupSaturation.closureSet op (insert e gs.toFinset) n) := by
    simpa [W,Atom.apply,Store.right,V] using ho
  have hM : 1≤M := by have := e.isLt; nlinarith
  obtain ⟨u,hu,X,scan,hX,hout⟩ := MaskAll.check_runs W.right M _ hW.right hcurrent hM
  have checked := scan.right_bounded hW
  refine ⟨t+(1+(u+0)),by omega,W.left.join X,
    .seq (close.left_bounded hb) (.seq copy (.seq checked (.skip checked.end_bound))),hW.left.join hX,?_⟩
  exact hout

variable {n k : ℕ} {G : Type*} [Group G] [Fintype G] [DecidableEq G]

theorem closure_full_iff (e : Fin n ≃ G) (op : Fin n → Fin n → Fin n)
    (he : ∀ x y,e (op x y)=e x*e y) (a : Fin k → Fin n) :
    GroupSaturation.closureSet op (insert (e.symm 1) (Finset.univ.image a)) n=Finset.univ ↔
      Generates (e ∘ a) := by
  let ep : Fin n ≃ G×PUnit.{1} := {
    toFun := fun x => (e x,PUnit.unit)
    invFun := fun x => e.symm x.1
    left_inv := fun x => e.symm_apply_apply x
    right_inv := fun x => Prod.ext (e.apply_symm_apply x.1) (Subsingleton.elim _ _) }
  have hep : ∀ x y,ep (op x y)=ep x*ep y := fun x y =>
    Prod.ext (he x y) (Subsingleton.elim _ _)
  let C := insert (e.symm 1) (Finset.univ.image a)
  have hC : C.image ep=insert 1 (Finset.univ.image (fun i => ((e ∘ a) i,(1:PUnit.{1})))) := by
    simp [C,Finset.image_insert,Finset.image_image,ep,Function.comp_def]
    rfl
  have hmem := GroupSaturation.mask_closure_mem op C ep hep (e ∘ a) (fun _ => (1:PUnit.{1})) hC
  constructor
  · intro h x
    have hj : e.symm x∈GroupSaturation.closureSet op C n := by rw [h]; exact Finset.mem_univ _
    obtain ⟨w,hw⟩ := FiniteWordTypes.explore_sound (e ∘ a) (fun _ => (1:PUnit.{1})) _
      (ep (e.symm x)) ((hmem _).mp hj)
    refine ⟨w,?_⟩
    simpa [ep] using congrArg Prod.fst hw
  · intro h
    apply Finset.eq_univ_of_forall
    intro j
    apply (hmem j).mpr
    obtain ⟨w,hw⟩ := h (e j)
    have hm := FiniteWordTypes.eval_mem_explore (e ∘ a) (fun _ => (1:PUnit.{1})) w
    have hp : (w.eval (e ∘ a),w.eval (fun _ => (1:PUnit.{1})))=ep j :=
      Prod.ext hw (Subsingleton.elim _ _)
    exact hp ▸ hm

end GroupWL.MachinePrograms.GeneratorTest
