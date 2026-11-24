import GroupWL.Refinement

/-! # Finite equality-matrix refinement

Every round materializes a finite relation on the fixed index set. Stored
entries are Boolean equalities, so nested colors are never expanded by the
algorithm. Vectors are compared by counting their current equality classes.
-/
namespace GroupWL.CompressedRefinement

open Refinement
universe u v
variable {A : Type u} [Fintype A] [DecidableEq A] {k : ℕ}

/-- Equality of mapped multisets can be checked at representatives from the
domain; values outside the image have count zero on both sides. -/
theorem map_eq_iff_counts {B C : Type*} [DecidableEq C] (f : B → C) (s t : Multiset B) :
    s.map f=t.map f ↔ ∀ b,
      s.countP (fun x => f b=f x)=t.countP (fun x => f b=f x) := by
  classical
  constructor
  · intro h b
    have hc := congrArg (Multiset.count (f b)) h
    simpa only [Multiset.count_map,Multiset.countP_eq_card_filter] using hc
  · intro h
    apply Multiset.ext.mpr
    intro c
    by_cases hc : ∃ b,f b=c
    · obtain ⟨b,rfl⟩ := hc
      simpa only [Multiset.count_map,Multiset.countP_eq_card_filter] using h b
    · have hn (s : Multiset B) : (s.map f).count c=0 := by
        apply Multiset.count_eq_zero_of_notMem
        intro hm
        obtain ⟨b,_,hb⟩ := Multiset.mem_map.mp hm
        exact hc ⟨b,hb⟩
      rw [hn s,hn t]

variable (edges : A → Multiset (Fin k → A))

def step (R : Finset (A×A)) : Finset (A×A) :=
  Finset.univ.filter (fun p => (p.1,p.2) ∈ R ∧ ∀ v : Fin k → A,
    (edges p.1).countP (fun w => ∀ i,(v i,w i) ∈ R)=
    (edges p.2).countP (fun w => ∀ i,(v i,w i) ∈ R))

def table (initialEq : A → A → Bool) : ℕ → Finset (A×A)
  | 0 => Finset.univ.filter (fun p => initialEq p.1 p.2=true)
  | r+1 => step edges (table initialEq r)

/-- Semantic colors, used only to state correctness of the finite matrices. -/
def labels {C : Type v} (initial : A → C) : (r : ℕ) → A → Color C k r
  | 0,a => initial a
  | r+1,a => (labels initial r a,
      (edges a).map (fun v => fun i => labels initial r (v i)))

theorem table_correct {C : Type v} (initial : A → C) (initialEq : A → A → Bool)
    (h : ∀ a b,initialEq a b=true ↔ initial a=initial b) (r : ℕ) (a b : A) :
    (a,b) ∈ table edges initialEq r ↔ labels edges initial r a=labels edges initial r b := by
  classical
  induction r generalizing a b with
  | zero => simpa only [table,Finset.mem_filter,Finset.mem_univ,true_and,labels] using h a b
  | succ r ih =>
      simp only [table,step,Finset.mem_filter,Finset.mem_univ,true_and,ih]
      constructor
      · rintro ⟨hab,hcounts⟩
        apply Prod.ext
        · exact hab
        · apply (map_eq_iff_counts _ (edges a) (edges b)).mpr
          intro v
          simpa only [funext_iff] using hcounts v
      · intro he
        refine ⟨congrArg Prod.fst he,?_⟩
        have hm := congrArg Prod.snd he
        have hc := (map_eq_iff_counts (fun v : Fin k → A => fun i => labels edges initial r (v i))
          (edges a) (edges b)).mp hm
        intro v
        simpa only [funext_iff] using hc v

theorem step_subset (R : Finset (A×A)) : step edges R ⊆ R := by
  intro p hp
  exact (Finset.mem_filter.mp hp).2.1

theorem table_subset (initialEq : A → A → Bool) (r : ℕ) :
    table edges initialEq (r+1) ⊆ table edges initialEq r := step_subset edges _

theorem stopped_or_card (initialEq : A → A → Bool) (r : ℕ) :
    table edges initialEq r=table edges initialEq (r+1) ∨
      (table edges initialEq r).card+r ≤ Fintype.card A ^ 2 := by
  induction r with
  | zero =>
      apply Or.inr
      simpa only [Nat.add_zero,Fintype.card_prod,pow_two] using
        Finset.card_le_univ (table edges initialEq 0)
  | succ r ih =>
      rcases ih with he|hc
      · exact Or.inl (congrArg (step edges) he)
      · by_cases he : table edges initialEq r=table edges initialEq (r+1)
        · exact Or.inl (congrArg (step edges) he)
        · have hh := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
            ⟨table_subset edges initialEq r,Ne.symm he⟩)
          exact Or.inr (by omega)

theorem fixed_at_bound (initialEq : A → A → Bool) :
    table edges initialEq (Fintype.card A ^ 2)=table edges initialEq (Fintype.card A ^ 2+1) := by
  rcases stopped_or_card edges initialEq (Fintype.card A ^ 2) with he|hc
  · exact he
  · have he : table edges initialEq (Fintype.card A ^ 2)=∅ := Finset.card_eq_zero.mp (by omega)
    apply Finset.Subset.antisymm
    · simp [he]
    · exact table_subset edges initialEq _

theorem table_stable (initialEq : A → A → Bool) (n : ℕ) :
    table edges initialEq (Fintype.card A ^ 2+n)=table edges initialEq (Fintype.card A ^ 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.add_succ,table,ih]
      exact (fixed_at_bound edges initialEq).symm

theorem table_antitone (initialEq : A → A → Bool) : Antitone (table edges initialEq) := by
  exact antitone_nat_of_succ_le (table_subset edges initialEq)

theorem mem_table_all_iff (initialEq : A → A → Bool) (a b : A) :
    (∀ r,(a,b) ∈ table edges initialEq r) ↔ (a,b) ∈ table edges initialEq (Fintype.card A ^ 2) := by
  constructor
  · exact fun h => h _
  · intro h r
    by_cases hr : r ≤ Fintype.card A ^ 2
    · exact table_antitone edges initialEq hr h
    · obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le (show Fintype.card A ^ 2 ≤ r by omega)
      simpa only [table_stable] using h

/-- Compare selected histograms using rows of the finite equality matrix. -/
def sameHistogram (R : Finset (A×A)) (s t : Multiset A) : Bool :=
  decide (∀ a,s.countP (fun x => (a,x) ∈ R)=t.countP (fun x => (a,x) ∈ R))

theorem sameHistogram_correct {C : Type v} (initial : A → C) (initialEq : A → A → Bool)
    (h : ∀ a b,initialEq a b=true ↔ initial a=initial b) (r : ℕ) (s t : Multiset A) :
    sameHistogram (table edges initialEq r) s t=true ↔
      s.map (labels edges initial r)=t.map (labels edges initial r) := by
  classical
  simp only [sameHistogram,decide_eq_true_eq,table_correct edges initial initialEq h]
  exact (map_eq_iff_counts (labels edges initial r) s t).symm

/-- Fixed-size finite matrices replace the recursively growing color expressions. -/
theorem table_size (initialEq : A → A → Bool) (r : ℕ) :
    (table edges initialEq r).card ≤ Fintype.card A ^ 2 := by
  simpa only [Fintype.card_prod,pow_two] using Finset.card_le_univ (table edges initialEq r)


/-- After the explicit matrix bound, selected histograms are equal precisely
when their semantic histograms are equal at every refinement round. -/
theorem sameHistogram_bound_correct [Nonempty A] {C : Type v}
    (initial : A → C) (initialEq : A → A → Bool)
    (h : ∀ a b,initialEq a b=true ↔ initial a=initial b) (s t : Multiset A) :
    sameHistogram (table edges initialEq (Fintype.card A ^ 2)) s t=true ↔
      ∀ r,s.map (labels edges initial r)=t.map (labels edges initial r) := by
  classical
  rw [sameHistogram_correct edges initial initialEq h]
  constructor
  · intro he r
    letI : Nonempty (Color C k r) := ⟨labels edges initial r (Classical.choice ‹Nonempty A›)⟩
    have hf : Function.FactorsThrough (labels edges initial r)
        (labels edges initial (Fintype.card A ^ 2)) := by
      intro a b hab
      apply (table_correct edges initial initialEq h r a b).mp
      apply (mem_table_all_iff edges initialEq a b).mpr _ r
      exact (table_correct edges initial initialEq h _ a b).mpr hab
    obtain ⟨f,hf⟩ := (Function.factorsThrough_iff _).mp hf
    rw [hf,← Multiset.map_map,← Multiset.map_map,he]
  · exact fun h => h _

/-- Executable stable refinement with an explicit polynomial number of
materialized matrix rounds. -/
def run (initialEq : A → A → Bool) (s t : Multiset A) : Bool :=
  sameHistogram (table edges initialEq (Fintype.card A ^ 2)) s t

theorem run_correct [Nonempty A] {C : Type v} (initial : A → C)
    (initialEq : A → A → Bool) (h : ∀ a b,initialEq a b=true ↔ initial a=initial b)
    (s t : Multiset A) : run edges initialEq s t=true ↔
      ∀ r,s.map (labels edges initial r)=t.map (labels edges initial r) :=
  sameHistogram_bound_correct edges initial initialEq h s t

end GroupWL.CompressedRefinement
