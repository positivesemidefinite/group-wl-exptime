import GroupWL.InitialIWords
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Multiplication-graph vertices as tagged pairs of group elements -/
namespace GroupWL.GadgetInterpretation

open Refinement InitialIWords

universe u v
variable {G : Type u} {H : Type v} [Group G] [Group H] {k d : ℕ}

/-- A group vertex ignores the second coordinate; internal vertices use both. -/
def decode (tag : Option (Fin 4)) (x y : G) : GadgetVertex G :=
  match tag with
  | none => .inl x
  | some j => .inr (x,y,j)

def decodedAdj (t s : Option (Fin 4)) (x y u v : G) : Prop :=
  match t,s with
  | none,none => False
  | none,some j => (j=0 ∧ x=u) ∨ (j=1 ∧ x=v) ∨ (j=3 ∧ x=u*v)
  | some j,none => (j=0 ∧ u=x) ∨ (j=1 ∧ u=y) ∨ (j=3 ∧ u=x*y)
  | some i,some j => x=u ∧ y=v ∧ (i.val+1=j.val ∨ j.val+1=i.val)

theorem gadgetAdj_decode (t s : Option (Fin 4)) (x y u v : G) :
    gadgetAdj (decode t x y) (decode s u v) ↔ decodedAdj t s x y u v := by
  cases t <;> cases s <;> rfl

/-- Distinct group-coordinate slots for each of a tuple's graph vertices,
with one additional group-coordinate slot available. -/
structure PairSlots (k d : ℕ) where
  tuple : (Fin k × Fin 2) ↪ Fin d
  spare : Fin d
  outside : ∀ i,tuple i ≠ spare

def PairSlots.standard (k : ℕ) : PairSlots k (k*2+1) where
  tuple := finProdFinEquiv.toEmbedding.trans ⟨Fin.castSucc,Fin.castSucc_injective _⟩
  spare := Fin.last (k*2)
  outside i := Fin.castSucc_ne_last (finProdFinEquiv i)

def vertexTuple (s : PairSlots k d) (tags : Fin k → Option (Fin 4)) (a : Fin d → G) :
    Fin k → GadgetVertex G := fun i => decode (tags i) (a (s.tuple (i,0))) (a (s.tuple (i,1)))

private theorem initial_eqs {a : Fin d → G} {b : Fin d → H}
    (h : initialI d a = initialI d b) (i j : Fin d) : a i = a j ↔ b i = b j := by
  classical
  exact decide_eq_decide.mp (congrFun (congrFun (congrArg Prod.fst h) i) j)

private theorem initial_muls {a : Fin d → G} {b : Fin d → H}
    (h : initialI d a = initialI d b) (i j l : Fin d) : a i*a j=a l ↔ b i*b j=b l := by
  classical
  exact decide_eq_decide.mp (congrFun (congrFun (congrFun (congrArg Prod.snd h) i) j) l)

/-- The uncolored graph's initial tuple type is determined by the multiplication
and equality relations of its underlying group coordinates and fixed tags. -/
theorem graphInitial_eq (s : PairSlots k d) (tags : Fin k → Option (Fin 4))
    {a : Fin d → G} {b : Fin d → H} (h : initialI d a = initialI d b) :
    graphInitial gadgetAdj k (vertexTuple s tags a) =
      graphInitial gadgetAdj k (vertexTuple s tags b) := by
  classical
  apply Prod.ext
  · funext i j
    apply decide_eq_decide.mpr
    cases hi : tags i <;> cases hj : tags j <;>
      simp only [vertexTuple,hi,hj,decode,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq,
        Prod.mk.injEq]
    · exact initial_eqs h _ _
    · exact and_congr (initial_eqs h _ _) (and_congr (initial_eqs h _ _) Iff.rfl)
  · funext i j
    apply decide_eq_decide.mpr
    simp only [vertexTuple,gadgetAdj_decode]
    cases hi : tags i <;> cases hj : tags j <;> simp only [decodedAdj]
    · exact or_congr (and_congr Iff.rfl (initial_eqs h _ _))
        (or_congr (and_congr Iff.rfl (initial_eqs h _ _))
          (and_congr Iff.rfl (by simpa [eq_comm] using initial_muls h (s.tuple (j,0)) (s.tuple (j,1)) (s.tuple (i,0)))))
    · exact or_congr (and_congr Iff.rfl (initial_eqs h _ _))
        (or_congr (and_congr Iff.rfl (initial_eqs h _ _))
          (and_congr Iff.rfl (by simpa [eq_comm] using initial_muls h (s.tuple (i,0)) (s.tuple (i,1)) (s.tuple (j,0)))))
    · exact and_congr (initial_eqs h _ _) (and_congr (initial_eqs h _ _) Iff.rfl)

/-- A triangular family of pair bijections induces a genuine graph-carrier
bijection, preserving group vertices and each of the four internal tags. -/
def gadgetEquiv (f : G ≃ H) (next : G → G ≃ H) : GadgetVertex G ≃ GadgetVertex H where
  toFun v := match v with
    | .inl x => .inl (f x)
    | .inr (x,y,j) => .inr (f x,next x y,j)
  invFun v := match v with
    | .inl x => .inl (f.symm x)
    | .inr (x,y,j) => .inr (f.symm x,(next (f.symm x)).symm y,j)
  left_inv v := by cases v with
    | inl x => simp
    | inr v => rcases v with ⟨x,y,j⟩; simp
  right_inv v := by cases v with
    | inl x => simp
    | inr v => rcases v with ⟨x,y,j⟩; simp

@[simp] theorem gadgetEquiv_inl (f : G ≃ H) (next : G → G ≃ H) (x : G) :
    gadgetEquiv f next (.inl x) = .inl (f x) := rfl

@[simp] theorem gadgetEquiv_inr (f : G ≃ H) (next : G → G ≃ H) (x y : G) (j : Fin 4) :
    gadgetEquiv f next (.inr (x,y,j)) = .inr (f x,next x y,j) := rfl

end GroupWL.GadgetInterpretation
