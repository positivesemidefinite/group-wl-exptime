import GroupWL.MachinePrograms.GeneratorMask
import GroupWL.MachinePrograms.GroupSaturationSemantics
import GroupWL.MachinePrograms.NatArrayComponents

/-! Seed-mask construction composed with the concrete multiplication closure. -/
namespace GroupWL.MachinePrograms.SeededSaturation
open NatArrayLanguage FiniteSetArrays
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

abbrev Reg := GeneratorMask.Reg ⊕ GroupSaturation.Reg
abbrev Arr := GeneratorMask.Arr ⊕ GroupSaturation.Arr
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def saturate : Code := sequence [
  GeneratorMask.build.map Sum.inl Sum.inl,
  .atom (.copyArray (.inr .current) (.inl .output)),
  GroupSaturation.saturate.map Sum.inr Sum.inr]

theorem saturate_runs (S : State) (n M : ℕ) (e : Fin n) (gs : List (Fin n))
    (op : Fin n → Fin n → Fin n)
    (hb : S.Bounded M) (hn : S.scalar (.inl .order)=n)
    (he : S.scalar (.inl .identity)=e.val) (hgens : S.array (.inl .generators)=gs.map Fin.val)
    (hn' : S.scalar (.inr .order)=n) (hlen : (S.array (.inr .table)).length=n*n)
    (hread : ∀ i : Fin (n*n),(S.array (.inr .table))[i.val]?.getD 0=
      (op (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2).val)
    (hroom : n*n≤M) :
    ∃ t≤10*n^3+8*n+5*gs.length+14,∃ T,Runs (storageBound Reg Arr M) saturate S t T ∧
      T.Bounded M ∧ T.array (.inr .current)=
        word (GroupSaturation.closureSet op (insert e gs.toFinset) n) := by
  obtain ⟨t,ht,U,seed,hU,ho⟩ := GeneratorMask.build_runs S.left M e gs hb.left hn he hgens
  let V := U.join S.right
  have hV : V.Bounded M := hU.join hb.right
  let W := (Atom.copyArray (Sum.inr GroupSaturation.Arr.current) (Sum.inl GeneratorMask.Arr.output)).apply V
  have hW : W.Bounded M := Atom.apply_bounded hV _ trivial
  have copy := atom_runs hV (.copyArray (.inr .current) (.inl .output)) trivial trivial
  have hcurrent : W.right.array .current=word (insert e gs.toFinset) := by
    simpa [W,Atom.apply,Store.right,V] using ho
  obtain ⟨u,hu,X,close,hX,hout⟩ := GroupSaturation.saturate_runs W.right n M
    (insert e gs.toFinset) op hW.right
    (by simpa [W,Atom.apply,Store.right,V] using hn') hcurrent
    (by simpa [W,Atom.apply,Store.right,V] using hlen)
    (by simpa [W,Atom.apply,Store.right,V] using hread) (by have := e.isLt; omega) hroom
  have closed := close.right_bounded hW
  refine ⟨t+(1+(u+0)),by omega,W.left.join X,
    .seq (seed.left_bounded hb) (.seq copy (.seq closed (.skip closed.end_bound))),hW.left.join hX,?_⟩
  exact hout

theorem scalarFrame {B S T t} (h : Runs B saturate S t T) :
    T.scalar (.inr .order)=S.scalar (.inr .order) := h.scalar_eq_of_not_mem _ (by decide)
theorem tableFrame {B S T t} (h : Runs B saturate S t T) :
    T.array (.inr .table)=S.array (.inr .table) := h.array_eq_of_not_mem _ (by decide)
theorem generatorsFrame {B S T t} (h : Runs B saturate S t T) :
    T.array (.inl .generators)=S.array (.inl .generators) := h.array_eq_of_not_mem _ (by decide)

end GroupWL.MachinePrograms.SeededSaturation
