import GroupWL.IndexedGadget
import GroupWL.MachinePrograms.GraphInitial

/-! The numeric graph table and tuple signatures are those of the original multiplication gadget. -/
namespace GroupWL.IndexedGadget
open Refinement
variable {G H : Type*} [Group G] [Group H] [DecidableEq G] [DecidableEq H] {n m k : ℕ}

def vertexEquiv (e : G ≃ Fin n) : GadgetVertex G ≃ Vertex n :=
  Equiv.sumCongr e (Equiv.prodCongr e (Equiv.prodCongr e (Equiv.refl (Fin 4))))

def groupEnumeration (e : G ≃ Fin n) : GadgetVertex G ≃ Fin (size n) :=
  (vertexEquiv e).trans (enumeration n)

theorem adj_vertexEquiv (e : G ≃ Fin n) (x y : GadgetVertex G) :
    adj (MachinePrograms.GroupInitial.encodedMul e) (vertexEquiv e x) (vertexEquiv e y)=
      FiniteWL.gadgetAdjTest x y := by
  cases x with
  | inl x => cases y with
    | inl y => rfl
    | inr y =>
      rcases y with ⟨g,h,j⟩
      simp [vertexEquiv,adj,FiniteWL.gadgetAdjTest,MachinePrograms.GroupInitial.encodedMul,e.injective.eq_iff]
  | inr x =>
    rcases x with ⟨g,h,i⟩
    cases y with
    | inl y =>
      simp [vertexEquiv,adj,FiniteWL.gadgetAdjTest,MachinePrograms.GroupInitial.encodedMul,e.injective.eq_iff]
    | inr y =>
      rcases y with ⟨g',h',j⟩
      simp [vertexEquiv,adj,FiniteWL.gadgetAdjTest,e.injective.eq_iff]

theorem numericAdj_groupEnumeration (e : G ≃ Fin n) (x y : GadgetVertex G) :
    numericAdj (MachinePrograms.GroupInitial.encodedMul e) (groupEnumeration e x) (groupEnumeration e y)=
      FiniteWL.gadgetAdjTest x y := by
  simpa [numericAdj,groupEnumeration] using adj_vertexEquiv e x y

theorem signature_groupEnumeration (e : G ≃ Fin n) (a : Fin k → GadgetVertex G) :
    MachinePrograms.GraphInitial.signature (numericAdj (MachinePrograms.GroupInitial.encodedMul e))
      (groupEnumeration e ∘ a)=FiniteWL.atomicGraph a := by
  apply Prod.ext
  · funext i j
    simp [MachinePrograms.GraphInitial.signature,FiniteWL.atomicGraph,Function.comp_def,(groupEnumeration e).injective.eq_iff]
  · funext i j
    exact numericAdj_groupEnumeration e (a i) (a j)
end GroupWL.IndexedGadget
