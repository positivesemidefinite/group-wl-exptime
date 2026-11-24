import GroupWL.InitialIWords
import GroupWL.RefinementMap

/-! # Concrete Version-I to Version-II comparison

A Version-I tuple with two helper slots tests all words in the remaining
coordinates. A strategy retaining `k+1` pair coordinates uses the picked-up
slot and one extra slot as those two helpers.
-/
namespace GroupWL.ConcreteVersionI

open Refinement PebbleGame GameRefinement InitialIWords

universe u v
variable {G : Type u} {H : Type v} [Group G] [Group H] [Fintype G] [Fintype H]
variable {k d : ℕ}

def trackedPosition (s : Slots (k+1) d) (a : Fin d → G) (b : Fin d → H) : Position (k+1) G H :=
  fun i => some (a (s.tuple i),b (s.tuple i))

theorem atomic_after_pickup (s : Slots (k+1) d) {a : Fin d → G} {b : Fin d → H}
    (h : SameI a b) (i : Fin (k+1)) : Atomic (erase (trackedPosition s a b) i) := by
  let input : Fin k → Fin d := fun j => s.tuple (i.succAbove j)
  have hword := initialII_eq_of_sameI h input (s.tuple i) s.spare (s.outside i)
    (fun j hj => Fin.succAbove_ne i j (s.tuple.injective hj))
    (fun j => s.outside (i.succAbove j))
  apply WordAtomic.atomic_of_initialII_eq hword
  intro j g h' hmark
  have hji : j ≠ i := by intro hj; subst j; simp at hmark
  obtain ⟨l,hl⟩ := Fin.exists_succAbove_eq hji
  have hpairs : a (s.tuple j) = g ∧ b (s.tuple j) = h' := by
    simpa [erase_ne _ _ _ hji,trackedPosition] using hmark
  exact ⟨l,by simpa [input,Function.comp_def,hl] using hpairs.1,
    by simpa [input,Function.comp_def,hl] using hpairs.2⟩

/-- An actual Version-I stable tuple supplies a Version-II strategy for the
tracked pairs, with one additional helper coordinate in the tuple. -/
theorem winning_of_sameI (s : Slots (k+1) d) {a : Fin d → G} {b : Fin d → H}
    (h : SameI a b) : Winning (trackedPosition s a b) := by
  let I : Position (k+1) G H → Prop := fun p =>
    ∃ a b, p = trackedPosition s a b ∧ SameI a b
  refine ⟨I,⟨a,b,rfl,h⟩,?_⟩
  rintro p ⟨a,b,rfl,hab⟩ i
  refine ⟨atomic_after_pickup s hab i,?_⟩
  obtain ⟨f,hf⟩ := Stable.matching hab
  refine ⟨f,fun x => ⟨Function.update a (s.tuple i) x,
    Function.update b (s.tuple i) (f x),?_,hf x (s.tuple i)⟩⟩
  funext j
  by_cases hji : j = i
  · subst j
    simp [trackedPosition,place]
  · have hsji : s.tuple j ≠ s.tuple i := fun he => hji (s.tuple.injective he)
    simp [trackedPosition,place,Function.update,hji,hsji]

theorem sameI_identity_tuple (h : EquivalentI d G H) :
    SameI (fun _ : Fin d => (1:G)) (fun _ : Fin d => (1:H)) := by
  classical
  intro r
  have hm : color (initialI (G := G) d) r (fun _ => 1) ∈ histogram (initialI (G := G) d) r :=
    Multiset.mem_map.mpr ⟨(fun _ => 1),Finset.mem_univ _,rfl⟩
  rw [h r] at hm
  obtain ⟨b,_,hb⟩ := Multiset.mem_map.mp hm
  have hzero : initialI d (fun _ : Fin d => (1:G)) = initialI d b := by
    exact InitialIWords.color_lower (initialA := initialI (G := G) d)
      (initialB := initialI (G := H) d) (r := 0) (Nat.zero_le r) hb.symm
  have hb1 : b = fun _ => 1 := by
    funext i
    have he := congrFun (congrFun (congrFun (congrArg Prod.snd hzero) i) i) i
    have hid : b i * b i = b i := (decide_eq_decide.mp he).mp (by simp)
    apply mul_left_cancel (a := b i)
    simpa using hid
  rw [← hb1]
  exact hb.symm

def comparisonSlots (hkd : k+2 ≤ d) : Slots (k+1) d where
  tuple := ⟨Fin.castLE (show k+1 ≤ d by omega),Fin.castLE_injective _⟩
  spare := ⟨k+1,by omega⟩
  outside i := by
    intro h
    have hi := congrArg Fin.val h
    have := i.isLt
    change i.val = k+1 at hi
    omega

/-- A two-dimension overhead suffices for the actual color definitions.
The manuscript uses the weaker six-dimension overhead. -/
theorem equivalentII_of_equivalentI (hkd : k+2 ≤ d) (h : EquivalentI d G H) :
    EquivalentII k G H := by
  apply GameRefinement.equivalentII_of_winning_empty k
  apply RefinementGame.winning_of_restricts
    (winning_of_sameI (comparisonSlots hkd) (sameI_identity_tuple h))
  intro i g h hmark
  simp [empty] at hmark

theorem equivalentII_of_equivalentI_add_two (h : EquivalentI (k+2) G H) : EquivalentII k G H :=
  equivalentII_of_equivalentI (by omega) h

/-- Identification among all finite groups transfers with the same overhead. -/
theorem identifiesI_of_identifiesII (hkd : k+2 ≤ d) (h : IdentifiesII k G) : IdentifiesI d G := by
  intro H hH
  exact h H (equivalentII_of_equivalentI hkd hH)

end GroupWL.ConcreteVersionI
