import GroupWL.CountingLogic

/-! # Explicit bounded-variable group formulas

Exponent, class at most two, centrality, and centralizer cardinalities are
expressed in the concrete syntax and their semantics are verified here.
-/

namespace GroupWL.CountingLogic

open Refinement PebbleGame

def wordPower {m : ℕ} (w : GroupWord m) : ℕ → GroupWord m
  | 0 => .one
  | n + 1 => .mul (wordPower w n) w

@[simp] theorem wordPower_eval {m : ℕ} {G : Type*} [Group G]
    (w : GroupWord m) (n : ℕ) (a : Fin m → G) :
    (wordPower w n).eval a = (w.eval a) ^ n := by
  induction n with
  | zero => simp [wordPower, GroupWord.eval]
  | succ n ih => simp [wordPower, GroupWord.eval, pow_succ, ih]

def commutatorWord {m : ℕ} (u v : GroupWord m) : GroupWord m :=
  .mul (.mul (.mul u v) (.inv u)) (.inv v)

def Formula.commutes {m : ℕ} (u v : GroupWord m) : Formula m := .atom (commutatorWord u v)
def Formula.existsVar {m : ℕ} (i : Fin m) (φ : Formula m) : Formula m := .count 1 i φ
def Formula.allVar {m : ℕ} (i : Fin m) (φ : Formula m) : Formula m := .neg (.existsVar i (.neg φ))

@[simp] theorem realize_commutes {m : ℕ} {G : Type*} [Group G]
    (u v : GroupWord m) (a : Fin m → G) :
    (Formula.commutes u v).Realize a ↔ u.eval a * v.eval a = v.eval a * u.eval a := by
  change u.eval a * v.eval a * (u.eval a)⁻¹ * (v.eval a)⁻¹ = 1 ↔ _
  rw [mul_assoc, ← mul_inv_rev, mul_inv_eq_one]

@[simp] theorem realize_existsVar {m : ℕ} {G : Type*} [Group G] [Finite G]
    (i : Fin m) (φ : Formula m) (a : Fin m → G) :
    (Formula.existsVar i φ).Realize a ↔ ∃ g, φ.Realize (Function.update a i g) := by
  change 1 ≤ Nat.card {g : G // φ.Realize (Function.update a i g)} ↔ _
  rw [Nat.succ_le_iff, Finite.card_pos_iff]
  exact nonempty_subtype

@[simp] theorem realize_allVar {m : ℕ} {G : Type*} [Group G] [Finite G]
    (i : Fin m) (φ : Formula m) (a : Fin m → G) :
    (Formula.allVar i φ).Realize a ↔ ∀ g, φ.Realize (Function.update a i g) := by
  change ¬ (Formula.existsVar i (.neg φ)).Realize a ↔ _
  rw [realize_existsVar]
  simp [Formula.Realize]

def exponentFormula {m : ℕ} (i : Fin m) (n : ℕ) : Formula m :=
  Formula.allVar i (.atom (wordPower (.gen i) n))

@[simp] theorem realize_exponentFormula {m : ℕ} {G : Type*} [Group G] [Finite G]
    (i : Fin m) (n : ℕ) (a : Fin m → G) :
    (exponentFormula i n).Realize a ↔ ∀ g : G, g ^ n = 1 := by
  simp [exponentFormula, Formula.Realize, GroupWord.eval]

def classTwoFormula {m : ℕ} (i j k : Fin m) : Formula m :=
  Formula.allVar i (Formula.allVar j (Formula.allVar k
    (Formula.commutes (commutatorWord (.gen i) (.gen j)) (.gen k))))

@[simp] theorem realize_classTwoFormula {m : ℕ} {G : Type*} [Group G] [Finite G]
    (i j k : Fin m) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (a : Fin m → G) :
    (classTwoFormula i j k).Realize a ↔
      ∀ g h x : G, (g * h * g⁻¹ * h⁻¹) * x = x * (g * h * g⁻¹ * h⁻¹) := by
  simp [classTwoFormula, commutatorWord, GroupWord.eval, hij, hik, hjk]

def centralFormula {m : ℕ} (i j : Fin m) : Formula m :=
  Formula.allVar j (Formula.commutes (.gen i) (.gen j))

@[simp] theorem realize_centralFormula {m : ℕ} {G : Type*} [Group G] [Finite G]
    (i j : Fin m) (hij : i ≠ j) (a : Fin m → G) :
    (centralFormula i j).Realize a ↔ ∀ h : G, a i * h = h * a i := by
  simp [centralFormula, GroupWord.eval, hij]

def centralizerAtLeastFormula {m : ℕ} (i j : Fin m) (n : ℕ) : Formula m :=
  .count n j (Formula.commutes (.gen i) (.gen j))

@[simp] theorem realize_centralizerAtLeastFormula {m : ℕ} {G : Type*} [Group G]
    (i j : Fin m) (hij : i ≠ j) (n : ℕ) (a : Fin m → G) :
    (centralizerAtLeastFormula i j n).Realize a ↔
      n ≤ Nat.card {h : G // a i * h = h * a i} := by
  simp only [centralizerAtLeastFormula, Formula.Realize, Formula.commutes, commutatorWord,
    GroupWord.eval, Function.update, hij, dite_false, dite_true]
  have hiff : ∀ h : G, a i * h * (a i)⁻¹ * h⁻¹ = 1 ↔ a i * h = h * a i := by
    intro h
    rw [mul_assoc, ← mul_inv_rev, mul_inv_eq_one]
  have hc : Nat.card {h : G // a i * h * (a i)⁻¹ * h⁻¹ = 1} =
      Nat.card {h : G // a i * h = h * a i} :=
    Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl G) hiff)
  rw [hc]

theorem wordPower_variables {m : ℕ} (w : GroupWord m) (n : ℕ) :
    wordVariables (wordPower w n) ⊆ wordVariables w := by
  induction n with
  | zero => simp [wordPower, wordVariables]
  | succ n ih =>
      change wordVariables (wordPower w n) ∪ wordVariables w ⊆ wordVariables w
      exact Finset.union_subset ih (Finset.Subset.refl _)

theorem exponentFormula_closed {m : ℕ} (i : Fin m) (n : ℕ) :
    (exponentFormula i n).freeVariables = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  change j ∈ (wordVariables (wordPower (.gen i) n)).erase i at hj
  obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hj
  have heq : j = i := by simpa [wordVariables] using wordPower_variables (.gen i) n hmem
  exact hne heq

theorem classTwoFormula_closed {m : ℕ} (i j k : Fin m) :
    (classTwoFormula i j k).freeVariables = ∅ := by
  ext l
  simp [classTwoFormula, Formula.allVar, Formula.existsVar, Formula.commutes,
    commutatorWord, Formula.freeVariables, wordVariables]
  tauto

theorem centralizerAtLeastFormula_free {m : ℕ} (i j : Fin m) (hij : i ≠ j) (n : ℕ) :
    (centralizerAtLeastFormula i j n).freeVariables = {i} := by
  ext l
  simp [centralizerAtLeastFormula, Formula.commutes, commutatorWord,
    Formula.freeVariables, wordVariables, hij]
  aesop

/-- A retained element has exactly the same centralizer cardinality in its mate. -/
theorem centralizer_card_transfer {m : ℕ} {G H : Type*} [Group G] [Group H]
    [Finite G] [Finite H] {p : Position (m + 1) G H} (hp : Winning p)
    (i j : Fin m) (hij : i ≠ j) {g : G} {h : H}
    (hmark : p i.castSucc = some (g, h)) :
    Nat.card {x : G // g * x = x * g} = Nat.card {x : H // h * x = x * h} := by
  have hthreshold : ∀ n : ℕ,
      n ≤ Nat.card {x : G // g * x = x * g} ↔ n ≤ Nat.card {x : H // h * x = x * h} := by
    intro n
    have htr := realize_iff_of_winning_free (centralizerAtLeastFormula i j n)
      (a := fun _ => g) (b := fun _ => h) hp (by
        intro l hl
        rw [centralizerAtLeastFormula_free i j hij n] at hl
        have : l = i := Finset.mem_singleton.mp hl
        simpa [this] using hmark)
    simpa only [realize_centralizerAtLeastFormula i j hij n] using htr
  exact Nat.le_antisymm ((hthreshold _).1 le_rfl) ((hthreshold _).2 le_rfl)

def centralizerSetCountFormula {m : ℕ} (i j : Fin m) (T N : ℕ) : Formula m :=
  .count N i (centralizerAtLeastFormula i j T)

@[simp] theorem realize_centralizerSetCountFormula {m : ℕ} {G : Type*} [Group G]
    (i j : Fin m) (hij : i ≠ j) (T N : ℕ) (a : Fin m → G) :
    (centralizerSetCountFormula i j T N).Realize a ↔
      N ≤ Nat.card {g : G // T ≤ Nat.card {h : G // g * h = h * g}} := by
  change N ≤ Nat.card {g : G // (centralizerAtLeastFormula i j T).Realize
    (Function.update a i g)} ↔ _
  simp [realize_centralizerAtLeastFormula i j hij]

theorem centralizerSetCountFormula_closed {m : ℕ} (i j : Fin m) (hij : i ≠ j) (T N : ℕ) :
    (centralizerSetCountFormula i j T N).freeVariables = ∅ := by
  simp only [centralizerSetCountFormula, Formula.freeVariables,
    centralizerAtLeastFormula_free i j hij, Finset.erase_singleton]

/-- The cardinality of a centralizer-threshold set transfers as well.
Taking `T + 1` gives exactly the manuscript's strict-threshold predicate. -/
theorem centralizer_set_card_transfer {m : ℕ} {G H : Type*} [Group G] [Group H]
    [Finite G] [Finite H] {p : Position (m + 1) G H} (hp : Winning p)
    (i j : Fin m) (hij : i ≠ j) (T : ℕ) :
    Nat.card {g : G // T ≤ Nat.card {x : G // g * x = x * g}} =
      Nat.card {h : H // T ≤ Nat.card {x : H // h * x = x * h}} := by
  have hthreshold : ∀ N : ℕ,
      N ≤ Nat.card {g : G // T ≤ Nat.card {x : G // g * x = x * g}} ↔
        N ≤ Nat.card {h : H // T ≤ Nat.card {x : H // h * x = x * h}} := by
    intro N
    have htr := realize_iff_of_winning_free (centralizerSetCountFormula i j T N)
      (a := fun _ => 1) (b := fun _ => 1) hp (by
        intro l hl
        simp [centralizerSetCountFormula_closed i j hij] at hl)
    simpa only [realize_centralizerSetCountFormula i j hij T N] using htr
  exact Nat.le_antisymm ((hthreshold _).1 le_rfl) ((hthreshold _).2 le_rfl)

theorem exponent_transfer {m : ℕ} {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    {p : Position (m + 1) G H} (hp : Winning p) (i : Fin m) (n : ℕ) :
    (∀ g : G, g ^ n = 1) ↔ (∀ h : H, h ^ n = 1) := by
  have h := realize_iff_of_winning_free (exponentFormula i n)
    (a := fun _ => 1) (b := fun _ => 1) hp (by
      intro j hj
      simp [exponentFormula_closed] at hj)
  simpa using h

theorem classTwo_transfer {m : ℕ} {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    {p : Position (m + 1) G H} (hp : Winning p)
    (i j k : Fin m) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (∀ g h x : G, (g * h * g⁻¹ * h⁻¹) * x = x * (g * h * g⁻¹ * h⁻¹)) ↔
      (∀ g h x : H, (g * h * g⁻¹ * h⁻¹) * x = x * (g * h * g⁻¹ * h⁻¹)) := by
  have h := realize_iff_of_winning_free (classTwoFormula i j k)
    (a := fun _ => 1) (b := fun _ => 1) hp (by
      intro l hl
      simp [classTwoFormula_closed] at hl)
  simpa only [realize_classTwoFormula i j k hij hik hjk] using h

end GroupWL.CountingLogic
