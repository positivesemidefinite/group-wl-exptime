import GroupWL.CompressedRefinement
import GroupWL.FiniteWordTypes

/-! # Executable finite matrix tests for group WL

The shared index set contains the tuples from both structures. Replacement
vectors stay in their own structure. Equality matrices are materialized at
each round, avoiding the expansion of recursively nested color expressions.
-/
namespace GroupWL.FiniteWL

open Refinement CompressedRefinement
universe u v w
variable {A : Type u} {B : Type v} [Fintype A] [Fintype B]
variable [DecidableEq A] [DecidableEq B] {k : ℕ}

abbrev Index (A : Type u) (B : Type v) (k : ℕ) := (Fin k → A) ⊕ (Fin k → B)

def edges : Index A B k → Multiset (Fin k → Index A B k)
  | .inl a => Finset.univ.val.map (fun x => fun i => .inl (Function.update a i x))
  | .inr b => Finset.univ.val.map (fun x => fun i => .inr (Function.update b i x))

def initial {C : Type w} (a : (Fin k → A) → C) (b : (Fin k → B) → C) : Index A B k → C :=
  Sum.elim a b

theorem labels_left {C : Type w} (a : (Fin k → A) → C) (b : (Fin k → B) → C)
    (r : ℕ) (x : Fin k → A) :
    labels edges (initial a b) r (.inl x)=color a r x := by
  induction r generalizing x with
  | zero => rfl
  | succ r ih =>
      apply Prod.ext
      · exact ih x
      · change (Finset.univ.val.map (fun y => fun i => Sum.inl (Function.update x i y))).map
          (fun v => fun i => labels edges (initial a b) r (v i)) = _
        rw [Multiset.map_map]
        apply Multiset.map_congr rfl
        intro y _
        funext i
        exact ih (Function.update x i y)

theorem labels_right {C : Type w} (a : (Fin k → A) → C) (b : (Fin k → B) → C)
    (r : ℕ) (x : Fin k → B) :
    labels edges (initial a b) r (.inr x)=color b r x := by
  induction r generalizing x with
  | zero => rfl
  | succ r ih =>
      apply Prod.ext
      · exact ih x
      · change (Finset.univ.val.map (fun y => fun i => Sum.inr (Function.update x i y))).map
          (fun v => fun i => labels edges (initial a b) r (v i)) = _
        rw [Multiset.map_map]
        apply Multiset.map_congr rfl
        intro y _
        funext i
        exact ih (Function.update x i y)

def leftTuples : Multiset (Index A B k) := Finset.univ.val.map Sum.inl
def rightTuples : Multiset (Index A B k) := Finset.univ.val.map Sum.inr

def test (initialEq : Index A B k → Index A B k → Bool) : Bool :=
  run edges initialEq leftTuples rightTuples

theorem test_correct [Nonempty A] {C : Type w}
    (a : (Fin k → A) → C) (b : (Fin k → B) → C)
    (initialEq : Index A B k → Index A B k → Bool)
    (h : ∀ x y,initialEq x y=true ↔ initial a b x=initial a b y) :
    test initialEq=true ↔ Equivalent a b := by
  have hh := run_correct edges (initial a b) initialEq h
    (leftTuples (A := A) (B := B)) rightTuples
  have hl (r : ℕ) : leftTuples.map (labels edges (initial a b) r)=histogram a r := by
    simp only [leftTuples,Multiset.map_map,histogram]
    exact Multiset.map_congr rfl (fun x _ => labels_left a b r x)
  have hr (r : ℕ) : rightTuples.map (labels edges (initial a b) r)=histogram b r := by
    simp only [rightTuples,Multiset.map_map,histogram]
    exact Multiset.map_congr rfl (fun x _ => labels_right a b r x)
  simpa only [test,hl,hr,Equivalent] using hh

variable {G : Type u} {H : Type v} [Group G] [Group H] [Fintype G] [Fintype H]
variable [DecidableEq G] [DecidableEq H]

/-- Computable version of the finite atomic Version-I signature. -/
def atomicI (a : Fin k → G) : InitialI k :=
  (fun i j => decide (a i=a j),fun i j l => decide (a i*a j=a l))

theorem atomicI_eq (a : Fin k → G) : atomicI a=initialI k a := by
  classical
  apply Prod.ext
  · funext i j
    apply Bool.eq_iff_iff.mpr
    simp [atomicI,initialI]
  · funext i j l
    apply Bool.eq_iff_iff.mpr
    simp [atomicI,initialI]

def initialEqI (x y : Index G H k) : Bool :=
  decide (initial atomicI atomicI x=initial atomicI atomicI y)

def initialEqII : Index G H k → Index G H k → Bool
  | .inl a,.inl b => FiniteWordTypes.sameWordType a b
  | .inl a,.inr b => FiniteWordTypes.sameWordType a b
  | .inr a,.inl b => FiniteWordTypes.sameWordType a b
  | .inr a,.inr b => FiniteWordTypes.sameWordType a b

def versionI (k : ℕ) : Bool := test (initialEqI (G := G) (H := H) (k := k))
def versionII (k : ℕ) : Bool := test (initialEqII (G := G) (H := H) (k := k))

theorem versionI_correct (k : ℕ) : versionI (G := G) (H := H) k=true ↔ EquivalentI k G H := by
  apply test_correct (initialI k) (initialI k)
  intro x y
  simp only [initialEqI,decide_eq_true_eq]
  have he : initial (atomicI (G := G)) (atomicI (G := H))=
      initial (initialI (G := G) k) (initialI (G := H) k) := by
    funext x
    cases x <;> exact atomicI_eq _
  rw [he]

theorem versionII_correct (k : ℕ) : versionII (G := G) (H := H) k=true ↔ EquivalentII k G H := by
  apply test_correct (initialII k) (initialII k)
  intro x y
  cases x <;> cases y <;> exact FiniteWordTypes.sameWordType_correct _ _

end GroupWL.FiniteWL
