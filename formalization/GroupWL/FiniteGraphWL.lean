import GroupWL.FiniteWL

/-! # Executable equality-matrix refinement for the multiplication graph -/
set_option synthInstance.maxSize 2048

namespace GroupWL.FiniteWL

open Refinement CompressedRefinement
universe u v
variable {G : Type u} {H : Type v} [Group G] [Group H] [Fintype G] [Fintype H]
variable [DecidableEq G] [DecidableEq H] {k : ℕ}

def gadgetAdjTest : GadgetVertex G → GadgetVertex G → Bool
  | .inl _,.inl _ => false
  | .inl v,.inr (g,h,j) => decide ((j=0 ∧ v=g) ∨ (j=1 ∧ v=h) ∨ (j=3 ∧ v=g*h))
  | .inr (g,h,j),.inl v => decide ((j=0 ∧ v=g) ∨ (j=1 ∧ v=h) ∨ (j=3 ∧ v=g*h))
  | .inr (g,h,i),.inr (g',h',j) =>
      decide (g=g' ∧ h=h' ∧ (i.val+1=j.val ∨ j.val+1=i.val))

@[simp] theorem gadgetAdjTest_correct (a b : GadgetVertex G) :
    gadgetAdjTest a b=true ↔ gadgetAdj a b := by
  cases a <;> cases b <;> simp [gadgetAdjTest,gadgetAdj] <;> rfl

instance gadgetAdjDecidable : DecidableRel (gadgetAdj (G := G)) :=
  fun a b => decidable_of_iff (gadgetAdjTest a b=true) (gadgetAdjTest_correct a b)

def atomicGraph (a : Fin k → GadgetVertex G) :=
  (fun i j => decide (a i=a j),fun i j => gadgetAdjTest (a i) (a j))

theorem atomicGraph_eq (a : Fin k → GadgetVertex G) :
    atomicGraph a=graphInitial gadgetAdj k a := by
  classical
  apply Prod.ext
  · funext i j
    apply Bool.eq_iff_iff.mpr
    simp [atomicGraph,graphInitial]
  · funext i j
    apply Bool.eq_iff_iff.mpr
    simp [atomicGraph,graphInitial]

def graphInitialEq (x y : Index (GadgetVertex G) (GadgetVertex H) k) : Bool :=
  decide (initial atomicGraph atomicGraph x=initial atomicGraph atomicGraph y)

def leftGroupTuples : Multiset (Index (GadgetVertex G) (GadgetVertex H) k) :=
  Finset.univ.val.map (fun a : Fin k → G => .inl (Sum.inl ∘ a))

def rightGroupTuples : Multiset (Index (GadgetVertex G) (GadgetVertex H) k) :=
  Finset.univ.val.map (fun a : Fin k → H => .inr (Sum.inl ∘ a))

def graphTest (k : ℕ) : Bool :=
  run edges (graphInitialEq (G := G) (H := H) (k := k)) leftGroupTuples rightGroupTuples

theorem graphTest_correct (k : ℕ) : graphTest (G := G) (H := H) k=true ↔
    ∀ r,graphGroupHistogram (G := G) k r=graphGroupHistogram (G := H) k r := by
  let init := initial (graphInitial (gadgetAdj (G := G)) k) (graphInitial (gadgetAdj (G := H)) k)
  have hinit (x y : Index (GadgetVertex G) (GadgetVertex H) k) :
      graphInitialEq x y=true ↔ init x=init y := by
    simp only [graphInitialEq,decide_eq_true_eq]
    have he : initial (atomicGraph (G := G)) (atomicGraph (G := H))=init := by
      funext x
      cases x <;> exact atomicGraph_eq _
    rw [he]
  have hh := run_correct edges init graphInitialEq hinit
    (leftGroupTuples (G := G) (H := H)) rightGroupTuples
  have hl (r : ℕ) : leftGroupTuples.map (labels edges init r)=graphGroupHistogram (G := G) k r := by
    simp only [leftGroupTuples,Multiset.map_map,graphGroupHistogram]
    exact Multiset.map_congr rfl (fun x _ => labels_left _ _ r _)
  have hr (r : ℕ) : rightGroupTuples.map (labels edges init r)=graphGroupHistogram (G := H) k r := by
    simp only [rightGroupTuples,Multiset.map_map,graphGroupHistogram]
    exact Multiset.map_congr rfl (fun x _ => labels_right _ _ r _)
  simpa only [graphTest,hl,hr] using hh

end GroupWL.FiniteWL
