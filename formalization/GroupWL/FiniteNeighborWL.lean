import GroupWL.FiniteGraphWL

/-! # The ordinary neighbor-refinement case at Version-III dimension one -/
set_option synthInstance.maxSize 2048

namespace GroupWL.FiniteWL

open Refinement CompressedRefinement
universe u v
variable {G : Type u} {H : Type v} [Group G] [Group H] [Fintype G] [Fintype H]
variable [DecidableEq G] [DecidableEq H]

abbrev NeighborIndex (G : Type u) (H : Type v) := GadgetVertex G ⊕ GadgetVertex H

def neighborEdges : NeighborIndex G H → Multiset (Fin 1 → NeighborIndex G H)
  | .inl a => (Finset.univ.filter (gadgetAdj a)).val.map (fun b => fun _ => .inl b)
  | .inr a => (Finset.univ.filter (gadgetAdj a)).val.map (fun b => fun _ => .inr b)

def liftNeighbor : (r : ℕ) → NeighborColor r → Color Unit 1 r
  | 0,c => c
  | r+1,(c,m) => (liftNeighbor r c,m.map (fun b => fun _ => liftNeighbor r b))

theorem liftNeighbor_injective (r : ℕ) : Function.Injective (liftNeighbor r) := by
  induction r with
  | zero => exact Function.injective_id
  | succ r ih =>
      intro x y he
      change (liftNeighbor r x.1,x.2.map (fun b => fun _ : Fin 1 => liftNeighbor r b))=
        (liftNeighbor r y.1,y.2.map (fun b => fun _ : Fin 1 => liftNeighbor r b)) at he
      apply Prod.ext
      · exact ih (congrArg Prod.fst he)
      · exact Multiset.map_injective (fun a b h => ih (congrFun h 0)) (congrArg Prod.snd he)

theorem neighbor_labels_left (r : ℕ) (a : GadgetVertex G) :
    labels (neighborEdges (G := G) (H := H)) (fun _ => ()) r (.inl a)=
      liftNeighbor r (neighborColor gadgetAdj r a) := by
  classical
  induction r generalizing a with
  | zero => rfl
  | succ r ih =>
      apply Prod.ext
      · exact ih a
      · simp only [labels,neighborEdges,liftNeighbor,neighborColor,Multiset.map_map]
        apply Multiset.map_congr
        · apply congrArg Finset.val
          ext b
          simp
        · intro b _
          funext i
          exact ih b

theorem neighbor_labels_right (r : ℕ) (a : GadgetVertex H) :
    labels (neighborEdges (G := G) (H := H)) (fun _ => ()) r (.inr a)=
      liftNeighbor r (neighborColor gadgetAdj r a) := by
  classical
  induction r generalizing a with
  | zero => rfl
  | succ r ih =>
      apply Prod.ext
      · exact ih a
      · simp only [labels,neighborEdges,liftNeighbor,neighborColor,Multiset.map_map]
        apply Multiset.map_congr
        · apply congrArg Finset.val
          ext b
          simp
        · intro b _
          funext i
          exact ih b

def leftGroupVertices : Multiset (NeighborIndex G H) :=
  Finset.univ.val.map (fun a : G => .inl (.inl a))

def rightGroupVertices : Multiset (NeighborIndex G H) :=
  Finset.univ.val.map (fun a : H => .inr (.inl a))

def neighborTest : Bool := run (neighborEdges (G := G) (H := H)) (fun _ _ => true)
  leftGroupVertices rightGroupVertices

theorem neighborTest_correct : neighborTest (G := G) (H := H)=true ↔
    ∀ r,neighborGroupHistogram (G := G) r=neighborGroupHistogram (G := H) r := by
  have hh := run_correct (neighborEdges (G := G) (H := H)) (fun _ => ()) (fun _ _ => true)
    (by intros; simp) leftGroupVertices rightGroupVertices
  have hl (r : ℕ) : leftGroupVertices.map (labels (neighborEdges (G := G) (H := H)) (fun _ => ()) r)=
      (neighborGroupHistogram (G := G) r).map (liftNeighbor r) := by
    simp only [leftGroupVertices,neighborGroupHistogram,Multiset.map_map]
    exact Multiset.map_congr rfl (fun a _ => neighbor_labels_left r (.inl a))
  have hr (r : ℕ) : rightGroupVertices.map (labels (neighborEdges (G := G) (H := H)) (fun _ => ()) r)=
      (neighborGroupHistogram (G := H) r).map (liftNeighbor r) := by
    simp only [rightGroupVertices,neighborGroupHistogram,Multiset.map_map]
    exact Multiset.map_congr rfl (fun a _ => neighbor_labels_right r (.inl a))
  simp only [hl,hr] at hh
  unfold neighborTest
  rw [hh]
  exact forall_congr' (fun r => (Multiset.map_injective (liftNeighbor_injective r)).eq_iff)

def versionIII (k : ℕ) : Bool := if k=1 then neighborTest (G := G) (H := H) else graphTest (G := G) (H := H) k

theorem versionIII_correct (k : ℕ) : versionIII (G := G) (H := H) k=true ↔ EquivalentIII k G H := by
  by_cases hk : k=1
  · simpa only [versionIII,EquivalentIII,if_pos hk] using (neighborTest_correct (G := G) (H := H))
  · simpa only [versionIII,EquivalentIII,if_neg hk] using (graphTest_correct (G := G) (H := H) k)

def groupTest (version : Version) (k : ℕ) : Bool :=
  match version with
  | .one => versionI (G := G) (H := H) k
  | .two => versionII (G := G) (H := H) k
  | .three => versionIII (G := G) (H := H) k

theorem groupTest_correct (version : Version) (k : ℕ) :
    groupTest (G := G) (H := H) version k=true ↔ GroupEquivalent version k G H := by
  cases version with
  | one => exact versionI_correct k
  | two => exact versionII_correct k
  | three => exact versionIII_correct k

end GroupWL.FiniteWL
