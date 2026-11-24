import GroupWL.GadgetMatching
import GroupWL.StableTuples

/-! # Two implicit group coordinates per graph slot -/
namespace GroupWL.PackedGraph

open Refinement InitialIWords GadgetDecoding GadgetRelations GadgetWords GadgetMatching
universe u v w

/-- Group coordinates are injected into the two input positions of graph
vertices. Two graph slots remain available for the next value and repacking. -/
structure Packing (k d : ℕ) where
  input : Fin k ↪ (Fin d × Fin 2)
  helpers : Fin 2 ↪ Fin d
  outside : ∀ i j,(input i).1 ≠ helpers j

variable {k d : ℕ}

def Packing.coordinate (s : Packing k d) (i : Fin k) : Coordinate d :=
  ((s.input i).1,(s.input i).2.castSucc)

def Packing.move (s : Packing k d) (i : Fin k) : Packing k d where
  input := s.input.trans (Equiv.prodCongr (Equiv.swap (s.input i).1 (s.helpers 1))
    (Equiv.refl (Fin 2))).toEmbedding
  helpers := s.helpers.trans (Equiv.swap (s.input i).1 (s.helpers 1)).toEmbedding
  outside j l := by
    intro he
    exact s.outside j l ((Equiv.swap (s.input i).1 (s.helpers 1)).injective he)

@[simp] theorem move_role (s : Packing k d) (i j : Fin k) :
    ((s.move i).input j).2 = (s.input j).2 := rfl

theorem move_block (s : Packing k d) (i j : Fin k) :
    ((s.move i).input j).1 =
      if (s.input j).1=(s.input i).1 then s.helpers 1 else (s.input j).1 := by
  change Equiv.swap (s.input i).1 (s.helpers 1) (s.input j).1 = _
  by_cases hj : (s.input j).1=(s.input i).1
  · simp [hj]
  · simp [Equiv.swap_apply_of_ne_of_ne,hj,s.outside j 1]

theorem helpers_ne (s : Packing k d) : s.helpers 0 ≠ s.helpers 1 := by
  intro he
  have hh := s.helpers.injective he
  norm_num at hh

variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- Tuple represented by the marked implicit gadget inputs. -/
def tuple (s : Packing k d) (a : Fin d → GadgetVertex G) : Fin k → G :=
  fun i => read a (s.coordinate i)

def UsableAt (s : Packing k d) (a : Fin d → GadgetVertex G) : Prop :=
  ∀ i,Usable (a (s.input i).1)

def after (s : Packing k d) (i : Fin k) (a : Fin d → GadgetVertex G) (x : G) : Fin d → GadgetVertex G :=
  Function.update (Function.update a (s.helpers 0) (.inl x)) (s.helpers 1)
    (newPair (s.input i).2 x (a (s.input i).1))

private theorem newPair_coord (role r : Fin 2) (x : G) (v : GadgetVertex G) :
    coord r.castSucc (newPair role x v) = if r=role then x else coord r.castSucc v := by
  fin_cases role <;> fin_cases r <;> simp [newPair]

/-- Repacking changes precisely the chosen group coordinate. -/
theorem tuple_after (s : Packing k d) (i : Fin k) (a : Fin d → GadgetVertex G) (x : G) :
    tuple (s.move i) (after s i a x) = Function.update (tuple s a) i x := by
  funext j
  change coord ((s.move i).input j).2.castSucc
    (after s i a x ((s.move i).input j).1) = _
  rw [move_role,move_block]
  by_cases hb : (s.input j).1=(s.input i).1
  · rw [if_pos hb]
    simp only [after,Function.update_self,newPair_coord]
    by_cases hji : j=i
    · subst j
      simp
    · have hr : (s.input j).2 ≠ (s.input i).2 := by
        intro he
        exact hji (s.input.injective (Prod.ext hb he))
      rw [if_neg hr,Function.update_of_ne hji]
      simp only [tuple,GadgetWords.read,Packing.coordinate,hb]
  · rw [if_neg hb]
    have hji : j ≠ i := by intro he; subst j; exact hb rfl
    simp only [after,Function.update_of_ne (s.outside j 1),Function.update_of_ne (s.outside j 0),
      Function.update_of_ne hji,tuple,GadgetWords.read,Packing.coordinate]

theorem usable_after [Fintype G] [Nontrivial G] (s : Packing k d) (i : Fin k)
    {a : Fin d → GadgetVertex G} (ha : UsableAt s a) (x : G) :
    UsableAt (s.move i) (after s i a x) := by
  intro j
  change Usable (after s i a x ((s.move i).input j).1)
  rw [move_block]
  by_cases hb : (s.input j).1=(s.input i).1
  · rw [if_pos hb]
    simp only [after,Function.update_self]
    exact newPair_usable (s.input i).2 x (a (s.input i).1)
  · rw [if_neg hb]
    simp only [after,Function.update_of_ne (s.outside j 1),
      Function.update_of_ne (s.outside j 0)]
    exact ha j

private theorem map_univ_congr {A : Type u} {B : Type v} {C : Type w}
    [Fintype A] [Fintype B] (e : A ≃ B) (f : A → C) (g : B → C)
    (h : ∀ a,f a = g (e a)) : Finset.univ.val.map f = Finset.univ.val.map g := by
  calc
    _ = Finset.univ.val.map (g ∘ e) := by congr 1; funext a; exact h a
    _ = (Finset.univ.val.map e).map g := by rw [Multiset.map_map]
    _ = _ := by rw [Multiset.map_univ_val_equiv]

/-- The full Version-II recursive color is determined by the stable graph
color of its packed tuple, with just two available graph slots. -/
theorem color_eq [Fintype G] [Fintype H] [Nontrivial G] [Nontrivial H]
    (hd : 3 ≤ d) (r : ℕ) (s : Packing k d)
    {a : Fin d → GadgetVertex G} {b : Fin d → GadgetVertex H}
    (h : SameGraph a b) (ha : UsableAt s a) (hb : UsableAt s b) :
    color (initialII k) r (tuple s a) = color (initialII k) r (tuple s b) := by
  classical
  induction r generalizing s a b with
  | zero =>
      exact initialII_eq_of_sameGraph hd h s.coordinate (s.helpers 0) (s.helpers 1)
        (helpers_ne s) (fun i => s.outside i 0) (fun i => s.outside i 1) ha hb
  | succ r ih =>
      apply Prod.ext
      · exact ih s h ha hb
      · obtain ⟨f,hf⟩ := group_matching h (s.helpers 0) (s.helpers 1) (helpers_ne s)
        apply map_univ_congr f
        intro x
        funext i
        have hh := repack hd (hf x) (s.input i).1 (s.helpers 1) (s.helpers 0)
          (s.outside i 1) (helpers_ne s) (s.input i).2 x (f x)
          (by simp) (by simp)
          (by simpa only [Function.update_of_ne (s.outside i 0)] using ha i)
          (by simpa only [Function.update_of_ne (s.outside i 0)] using hb i)
        simp only [Function.update_of_ne (s.outside i 0)] at hh
        have hc := ih (s.move i) hh (usable_after s i ha x) (usable_after s i hb (f x))
        change color (initialII k) r (tuple (s.move i) (after s i a x)) =
          color (initialII k) r (tuple (s.move i) (after s i b (f x))) at hc
        simpa only [tuple_after] using hc

end GroupWL.PackedGraph
