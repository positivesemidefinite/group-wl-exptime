import GroupWL.FiniteWordTypes
import Mathlib.GroupTheory.OrderOfElement

/-! Finite paired-subgroup saturation using multiplication alone. This gives
the operational table client an inverse-free scan without changing word types. -/
namespace GroupWL.PositiveWordTypes

open Refinement
variable {G H : Type*} [Group G] [Group H] [DecidableEq G] [DecidableEq H] {k : ℕ}

def step (S : Finset (G×H)) : Finset (G×H) :=
  S ∪ S.biUnion (fun x => S.image (fun y => x*y))

theorem subset_step (S : Finset (G×H)) : S⊆step S := fun _ h => Finset.mem_union_left _ h

def explore (a : Fin k → G) (b : Fin k → H) : ℕ → Finset (G×H)
  | 0 => insert 1 (Finset.univ.image (fun i => (a i,b i)))
  | n+1 => step (explore a b n)

theorem explore_mono (a : Fin k → G) (b : Fin k → H) : Monotone (explore a b) :=
  monotone_nat_of_le_succ (fun _ => subset_step _)

theorem one_mem (a : Fin k → G) (b : Fin k → H) (n : ℕ) : 1∈explore a b n :=
  explore_mono a b (Nat.zero_le n) (Finset.mem_insert_self _ _)

theorem gen_mem (a : Fin k → G) (b : Fin k → H) (n : ℕ) (i : Fin k) :
    (a i,b i)∈explore a b n :=
  explore_mono a b (Nat.zero_le n)
    (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))

theorem stopped_or_card (a : Fin k → G) (b : Fin k → H) (n : ℕ) :
    explore a b n=explore a b (n+1) ∨ n+1≤(explore a b n).card := by
  induction n with
  | zero => exact Or.inr (Finset.card_pos.mpr ⟨1,one_mem a b 0⟩)
  | succ n ih =>
    rcases ih with hf|hc
    · exact Or.inl (congrArg step hf)
    · by_cases hf : explore a b n=explore a b (n+1)
      · exact Or.inl (congrArg step hf)
      · have hlt : (explore a b n).card < (explore a b (n+1)).card :=
          Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨subset_step _,hf⟩)
        exact Or.inr (by omega)

theorem explore_sound (a : Fin k → G) (b : Fin k → H) (n : ℕ)
    (x : G×H) (hx : x∈explore a b n) :
    ∃ w : GroupWord k,(w.eval a,w.eval b)=x := by
  induction n generalizing x with
  | zero =>
    simp only [explore,Finset.mem_insert,Finset.mem_image,Finset.mem_univ,true_and] at hx
    rcases hx with rfl|⟨i,rfl⟩
    · exact ⟨.one,rfl⟩
    · exact ⟨.gen i,rfl⟩
  | succ n ih =>
    simp only [explore,step,Finset.mem_union,Finset.mem_biUnion,Finset.mem_image] at hx
    rcases hx with hx|⟨y,hy,z,hz,rfl⟩
    · exact ih _ hx
    · obtain ⟨w,rfl⟩ := ih _ hy
      obtain ⟨w',rfl⟩ := ih _ hz
      exact ⟨.mul w w',rfl⟩

variable [Fintype G] [Fintype H]

theorem explore_fixed (a : Fin k → G) (b : Fin k → H) :
    explore a b (Fintype.card (G×H))=step (explore a b (Fintype.card (G×H))) := by
  rcases stopped_or_card a b (Fintype.card (G×H)) with h|h
  · exact h
  · have := Finset.card_le_univ (explore a b (Fintype.card (G×H)))
    omega

theorem mul_mem (a : Fin k → G) (b : Fin k → H) {x y : G×H}
    (hx : x∈explore a b (Fintype.card (G×H)))
    (hy : y∈explore a b (Fintype.card (G×H))) :
    x*y∈explore a b (Fintype.card (G×H)) := by
  rw [explore_fixed]
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
    ⟨x,hx,Finset.mem_image.mpr ⟨y,hy,rfl⟩⟩)

theorem pow_mem (a : Fin k → G) (b : Fin k → H) {x : G×H}
    (hx : x∈explore a b (Fintype.card (G×H))) (m : ℕ) :
    x^m∈explore a b (Fintype.card (G×H)) := by
  induction m with
  | zero => simpa using one_mem a b (Fintype.card (G×H))
  | succ m ih => simpa only [pow_succ] using mul_mem a b ih hx

theorem inv_mem (a : Fin k → G) (b : Fin k → H) {x : G×H}
    (hx : x∈explore a b (Fintype.card (G×H))) :
    x⁻¹∈explore a b (Fintype.card (G×H)) := by
  have he : x^(orderOf x-1)=x⁻¹ := by
    apply mul_right_cancel (b := x)
    rw [inv_mul_cancel,←pow_succ,Nat.sub_add_cancel (orderOf_pos x),pow_orderOf_eq_one]
  rw [←he]
  exact pow_mem a b hx _

theorem eval_mem (a : Fin k → G) (b : Fin k → H) (w : GroupWord k) :
    (w.eval a,w.eval b)∈explore a b (Fintype.card (G×H)) := by
  induction w with
  | one => exact one_mem a b _
  | gen i => exact gen_mem a b _ i
  | inv w ih => exact inv_mem a b ih
  | mul w w' ih ih' => exact mul_mem a b ih ih'

theorem explore_eq (a : Fin k → G) (b : Fin k → H) :
    explore a b (Fintype.card (G×H)) = FiniteWordTypes.explore a b (Fintype.card (G×H)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨w,rfl⟩ := explore_sound a b _ x hx
    exact FiniteWordTypes.eval_mem_explore a b w
  · intro hx
    obtain ⟨w,rfl⟩ := FiniteWordTypes.explore_sound a b _ x hx
    exact eval_mem a b w

end GroupWL.PositiveWordTypes
