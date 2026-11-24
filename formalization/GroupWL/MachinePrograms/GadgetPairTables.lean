import GroupWL.MachinePrograms.GadgetTable

/-! Build both multiplication-gadget adjacency tables, including their numeric orders. -/
namespace GroupWL.MachinePrograms.GadgetPairTables
open NatArrayLanguage
abbrev Reg := GadgetTable.Reg ⊕ GadgetTable.Reg
abbrev Arr := GadgetTable.Arr ⊕ GadgetTable.Arr
abbrev State := Store Reg Arr
abbrev Code := NatArrayLanguage.Program Reg Arr

def generate : Code := .seq (GadgetTable.generate.map Sum.inl Sum.inl) (GadgetTable.generate.map Sum.inr Sum.inr)

theorem generate_runs {n m : ℕ} (f : Fin n→Fin n→Fin n) (g : Fin m→Fin m→Fin m)
    (hn : 0<n) (hm : 0<m) (S : State) (B : ℕ) (bounded : S.Bounded B)
    (left : S.left.scalar (.inl 0)=n) (right : S.right.scalar (.inl 0)=m)
    (leftTable : S.left.array (.inl ())=GroupInitial.tableWord f)
    (rightTable : S.right.array (.inl ())=GroupInitial.tableWord g)
    (leftRoom : (IndexedGadget.size n)^2≤B) (rightRoom : (IndexedGadget.size m)^2≤B) :
    ∃t≤410*B+22,∃T,Runs (storageBound Reg Arr B) generate S t T ∧ T.Bounded B ∧
      GadgetTable.Context f T.left ∧ GadgetTable.Context g T.right ∧
      T.left.array (.inr ())=GraphInitial.tableWord (IndexedGadget.numericAdj f) ∧
      T.right.array (.inr ())=GraphInitial.tableWord (IndexedGadget.numericAdj g) := by
  obtain ⟨t,ht,U,first,hU,ctxU,outU⟩ := GadgetTable.generate_runs f hn S.left B bounded.left left leftTable
    (by simpa only [pow_two] using leftRoom)
  let V := U.join S.right
  have hV : V.Bounded B := hU.join bounded.right
  obtain ⟨u,hu,W,last,hW,ctxW,outW⟩ := GadgetTable.generate_runs g hm V.right B hV.right right rightTable
    (by simpa only [pow_two] using rightRoom)
  refine ⟨t+u,?_,V.left.join W,.seq (first.left_bounded bounded) (last.right_bounded hV),hV.left.join hW,ctxU,ctxW,outU,outW⟩
  simp only [pow_two] at leftRoom rightRoom
  omega

end GroupWL.MachinePrograms.GadgetPairTables
