import GroupWL.StableTuples

/-! # An explicit finite-round bound for joint-vector refinement -/
namespace GroupWL.FiniteRefinement

open Refinement InitialIWords
universe u v w
variable {A : Type u} {B : Type v} [Fintype A] [Fintype B]
variable {C : Type w} {k : ℕ}
variable (initialA : (Fin k → A) → C) (initialB : (Fin k → B) → C)

/-- The finite set of cross-structure tuple matchPairs at a given round. -/
noncomputable def matchPairs (r : ℕ) : Finset ((Fin k → A) × (Fin k → B)) := by
  classical
  exact Finset.univ.filter (fun p => color initialA r p.1=color initialB r p.2)

@[simp] theorem mem_matchPairs (r : ℕ) (a : Fin k → A) (b : Fin k → B) :
    (a,b) ∈ matchPairs initialA initialB r ↔ color initialA r a=color initialB r b := by
  classical
  simp [matchPairs]

theorem matchPairs_subset (r : ℕ) : matchPairs initialA initialB (r+1) ⊆ matchPairs initialA initialB r := by
  rintro ⟨a,b⟩ hp
  exact (mem_matchPairs _ _ r a b).mpr (congrArg Prod.fst ((mem_matchPairs _ _ (r+1) a b).mp hp))

private theorem map_univ_congr {X : Type u} {Y : Type v} {Z : Type w}
    [Fintype X] [Fintype Y] (e : X ≃ Y) (f : X → Z) (g : Y → Z)
    (h : ∀ x,f x=g (e x)) : Finset.univ.val.map f=Finset.univ.val.map g := by
  calc
    _ = Finset.univ.val.map (g ∘ e) := by congr 1; funext x; exact h x
    _ = (Finset.univ.val.map e).map g := by rw [Multiset.map_map]
    _ = _ := by rw [Multiset.map_univ_val_equiv]

private theorem univ_match {X : Type u} {Y : Type v} {Z : Type w}
    [Fintype X] [Fintype Y] (f : X → Z) (g : Y → Z)
    (h : Finset.univ.val.map f=Finset.univ.val.map g) :
    ∃ e : X ≃ Y,∀ x,f x=g (e x) := by
  classical
  have hc (z : Z) : Fintype.card {x : X // f x=z}=Fintype.card {y : Y // g y=z} := by
    have he := congrArg (Multiset.count z) h
    simp only [Multiset.count_map,← Finset.filter_val,eq_comm (a := z)] at he
    rw [Fintype.card_subtype,Fintype.card_subtype]
    exact he
  let es (z : Z) : {x : X // f x=z} ≃ {y : Y // g y=z} := Fintype.equivOfCardEq (hc z)
  exact ⟨Equiv.ofFiberEquiv es,fun x => (Equiv.ofFiberEquiv_map es x).symm⟩

/-- Once no cross-structure tuple class splits, later rounds cannot split one. -/
theorem fixed_next (r : ℕ) (hf : matchPairs initialA initialB r=matchPairs initialA initialB (r+1)) :
    matchPairs initialA initialB (r+1)=matchPairs initialA initialB (r+2) := by
  classical
  apply Finset.Subset.antisymm
  · rintro ⟨a,b⟩ hp
    have he := (mem_matchPairs _ _ (r+1) a b).mp hp
    apply (mem_matchPairs _ _ (r+2) a b).mpr
    apply Prod.ext
    · exact he
    · obtain ⟨f,hf'⟩ := univ_match _ _ (congrArg Prod.snd he)
      apply map_univ_congr f
      intro x
      funext i
      apply (mem_matchPairs _ _ (r+1) _ _).mp
      rw [← hf]
      exact (mem_matchPairs _ _ r _ _).mpr (congrFun (hf' x) i)
  · exact matchPairs_subset _ _ (r+1)

/-- A conservative explicit bound: the number of possible cross-tuple pairs. -/
def bound : ℕ := Fintype.card A ^ k * Fintype.card B ^ k

theorem stopped_or_card (n : ℕ) :
    matchPairs initialA initialB n=matchPairs initialA initialB (n+1) ∨
      (matchPairs initialA initialB n).card+n ≤ bound (A := A) (B := B) (k := k) := by
  classical
  induction n with
  | zero =>
      apply Or.inr
      simpa [bound,Fintype.card_prod,Fintype.card_fun] using
        Finset.card_le_univ (matchPairs initialA initialB 0)
  | succ n ih =>
      rcases ih with hf|hc
      · exact Or.inl (fixed_next _ _ n hf)
      · by_cases hf : matchPairs initialA initialB n=matchPairs initialA initialB (n+1)
        · exact Or.inl (fixed_next _ _ n hf)
        · have hlt : (matchPairs initialA initialB (n+1)).card < (matchPairs initialA initialB n).card :=
            Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
              ⟨matchPairs_subset _ _ n,Ne.symm hf⟩)
          exact Or.inr (by omega)

theorem fixed_at_bound :
    matchPairs initialA initialB (bound (A := A) (B := B) (k := k))=
      matchPairs initialA initialB (bound (A := A) (B := B) (k := k)+1) := by
  classical
  rcases stopped_or_card initialA initialB (bound (A := A) (B := B) (k := k)) with hf|hc
  · exact hf
  · have he : matchPairs initialA initialB (bound (A := A) (B := B) (k := k))=∅ :=
      Finset.card_eq_zero.mp (by omega)
    apply Finset.Subset.antisymm
    · simp [he]
    · exact matchPairs_subset _ _ _

theorem stable_of_color_eq_at_bound {a : Fin k → A} {b : Fin k → B}
    (h : color initialA (bound (A := A) (B := B) (k := k)) a=
      color initialB (bound (A := A) (B := B) (k := k)) b) :
    Stable initialA initialB a b := by
  let M := bound (A := A) (B := B) (k := k)
  have hf (n : ℕ) : matchPairs initialA initialB (M+n)=matchPairs initialA initialB (M+n+1) := by
    induction n with
    | zero => simpa only [Nat.add_zero] using fixed_at_bound initialA initialB
    | succ n ih => simpa only [Nat.add_assoc] using fixed_next initialA initialB (M+n) ih
  have hm (n : ℕ) : matchPairs initialA initialB (M+n)=matchPairs initialA initialB M := by
    induction n with
    | zero => simp
    | succ n ih => rw [← Nat.add_assoc,← hf n,ih]
  intro r
  by_cases hr : r ≤ M
  · exact color_lower hr h
  · obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le (show M ≤ r by omega)
    apply (mem_matchPairs _ _ _ _ _).mp
    rw [hm n]
    exact (mem_matchPairs _ _ _ _ _).mpr h

/-- Stable histogram equivalence is decided at this explicit finite round. -/
theorem equivalent_iff_histogram_at_bound :
    Equivalent initialA initialB ↔
      histogram initialA (bound (A := A) (B := B) (k := k))=
        histogram initialB (bound (A := A) (B := B) (k := k)) := by
  constructor
  · exact fun h => h _
  · intro h
    obtain ⟨e,he⟩ := univ_match _ _ h
    intro r
    apply map_univ_congr e
    intro a
    exact stable_of_color_eq_at_bound initialA initialB (he a) r

end GroupWL.FiniteRefinement
