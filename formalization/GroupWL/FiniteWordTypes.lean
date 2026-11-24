import GroupWL.Identification

/-! # A finite executable test for generated-subgroup word types

Explore the paired subgroup inside the product of the two ambient groups.
After at most the product order many saturation rounds it is closed under
multiplication and inversion. Equal kernels of the two projections are
exactly equality of the complete marked word types.
-/
namespace GroupWL.FiniteWordTypes

open Refinement
universe u v
variable {G : Type u} {H : Type v} [Group G] [Group H]
variable [DecidableEq G] [DecidableEq H] {k : ℕ}

def step (S : Finset (G×H)) : Finset (G×H) :=
  (S ∪ S.image Inv.inv) ∪ S.biUnion (fun x => S.image (fun y => x*y))

theorem subset_step (S : Finset (G×H)) : S ⊆ step S := by
  intro x hx
  exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)

def explore (a : Fin k → G) (b : Fin k → H) : ℕ → Finset (G×H)
  | 0 => insert 1 (Finset.univ.image (fun i => (a i,b i)))
  | n+1 => step (explore a b n)

theorem explore_mono (a : Fin k → G) (b : Fin k → H) : Monotone (explore a b) := by
  apply monotone_nat_of_le_succ
  intro n
  exact subset_step _

theorem one_mem (a : Fin k → G) (b : Fin k → H) (n : ℕ) : 1 ∈ explore a b n :=
  explore_mono a b (Nat.zero_le n) (Finset.mem_insert_self _ _)

theorem gen_mem (a : Fin k → G) (b : Fin k → H) (n : ℕ) (i : Fin k) :
    (a i,b i) ∈ explore a b n := by
  apply explore_mono a b (Nat.zero_le n)
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)

/-- A nonempty increasing iteration either has stopped or has gained at
least one element in every preceding round. -/
theorem stopped_or_card (a : Fin k → G) (b : Fin k → H) (n : ℕ) :
    explore a b n=explore a b (n+1) ∨ n+1 ≤ (explore a b n).card := by
  induction n with
  | zero =>
      exact Or.inr (Finset.card_pos.mpr ⟨1,one_mem a b 0⟩)
  | succ n ih =>
      rcases ih with hf|hc
      · exact Or.inl (congrArg step hf)
      · by_cases hf : explore a b n=explore a b (n+1)
        · exact Or.inl (congrArg step hf)
        · have hlt : (explore a b n).card < (explore a b (n+1)).card :=
            Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨subset_step _,hf⟩)
          exact Or.inr (by omega)

/-- The explicit product-order bound suffices for saturation. -/
theorem explore_fixed [Fintype G] [Fintype H] (a : Fin k → G) (b : Fin k → H) :
    explore a b (Fintype.card (G×H))=step (explore a b (Fintype.card (G×H))) := by
  rcases stopped_or_card a b (Fintype.card (G×H)) with h|h
  · exact h
  · have hle := Finset.card_le_univ (explore a b (Fintype.card (G×H)))
    omega

/-- Every exploration entry is the value of the same word in the two tuples. -/
theorem explore_sound (a : Fin k → G) (b : Fin k → H) (n : ℕ)
    (x : G×H) (hx : x ∈ explore a b n) :
    ∃ w : GroupWord k,(w.eval a,w.eval b)=x := by
  induction n generalizing x with
  | zero =>
      simp only [explore,Finset.mem_insert,Finset.mem_image,Finset.mem_univ,true_and] at hx
      rcases hx with rfl|⟨i,rfl⟩
      · exact ⟨.one,rfl⟩
      · exact ⟨.gen i,rfl⟩
  | succ n ih =>
      simp only [explore,step,Finset.mem_union,Finset.mem_image,Finset.mem_biUnion] at hx
      rcases hx with (hx|⟨y,hy,rfl⟩)|⟨y,hy,z,hz,rfl⟩
      · exact ih _ hx
      · obtain ⟨w,rfl⟩ := ih _ hy
        exact ⟨.inv w,rfl⟩
      · obtain ⟨w,rfl⟩ := ih _ hy
        obtain ⟨w',rfl⟩ := ih _ hz
        exact ⟨.mul w w',rfl⟩

/-- Conversely the saturated exploration contains every word value. -/
theorem eval_mem_explore [Fintype G] [Fintype H]
    (a : Fin k → G) (b : Fin k → H) (w : GroupWord k) :
    (w.eval a,w.eval b) ∈ explore a b (Fintype.card (G×H)) := by
  have hf := explore_fixed a b
  induction w with
  | one => exact one_mem a b _
  | gen i => exact gen_mem a b _ i
  | inv w ih =>
      rw [hf]
      exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨(w.eval a,w.eval b),ih,rfl⟩))
  | mul w w' ih ih' =>
      rw [hf]
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨(w.eval a,w.eval b),ih,Finset.mem_image.mpr ⟨(w'.eval a,w'.eval b),ih',rfl⟩⟩)

def sameWordType [Fintype G] [Fintype H] (a : Fin k → G) (b : Fin k → H) : Bool :=
  decide (∀ x ∈ explore a b (Fintype.card (G×H)),x.1=1 ↔ x.2=1)

/-- The finite test decides the actual infinite word-type initial color. -/
theorem sameWordType_correct [Fintype G] [Fintype H] (a : Fin k → G) (b : Fin k → H) :
    sameWordType a b=true ↔ initialII k a=initialII k b := by
  simp only [sameWordType,decide_eq_true_eq]
  constructor
  · intro h
    funext w
    exact decide_eq_decide.mpr (h (w.eval a,w.eval b) (eval_mem_explore a b w))
  · intro h x hx
    obtain ⟨w,rfl⟩ := explore_sound a b _ x hx
    exact relations_iff_of_initialII_eq h w

/-- At each round there are at most the product order many entries. -/
theorem explore_size [Fintype G] [Fintype H] (a : Fin k → G) (b : Fin k → H) (n : ℕ) :
    (explore a b n).card ≤ Fintype.card G * Fintype.card H := by
  simpa only [Fintype.card_prod] using Finset.card_le_univ (explore a b n)

end GroupWL.FiniteWordTypes
