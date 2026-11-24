import GroupWL.CountingLogic

/-! # Capture-free variable renaming for finite-variable counting formulas -/
namespace GroupWL.CountingLogic
open Refinement PebbleGame

def renameWord {m n : ℕ} (f : Fin m → Fin n) : GroupWord m → GroupWord n
  | .one => .one
  | .gen i => .gen (f i)
  | .mul u v => .mul (renameWord f u) (renameWord f v)
  | .inv u => .inv (renameWord f u)

@[simp] theorem eval_renameWord {m n : ℕ} {G : Type*} [Group G]
    (f : Fin m → Fin n) (w : GroupWord m) (a : Fin n → G) :
    (renameWord f w).eval a = w.eval (a ∘ f) := by
  induction w <;> simp_all [renameWord, GroupWord.eval]

def Formula.rename {m n : ℕ} (f : Fin m → Fin n) : Formula m → Formula n
  | .atom w => .atom (renameWord f w)
  | .neg φ => .neg (φ.rename f)
  | .and φ ψ => .and (φ.rename f) (ψ.rename f)
  | .count c i φ => .count c (f i) (φ.rename f)

@[simp] theorem realize_rename {m n : ℕ} {G : Type*} [Group G]
    (f : Fin m → Fin n) (hf : Function.Injective f)
    (φ : Formula m) (a : Fin n → G) :
    (φ.rename f).Realize a ↔ φ.Realize (a ∘ f) := by
  induction φ generalizing a with
  | atom w => simp [Formula.rename, Formula.Realize]
  | neg φ ih => exact not_congr (ih a)
  | and φ ψ ihφ ihψ => exact and_congr (ihφ a) (ihψ a)
  | count c i φ ih =>
      have hu (g : G) : (Function.update a (f i) g) ∘ f =
          Function.update (a ∘ f) i g := by
        funext j
        simp [Function.comp_def, Function.update, hf.eq_iff]
      have he : ∀ g, (φ.rename f).Realize (Function.update a (f i) g) ↔
          φ.Realize (Function.update (a ∘ f) i g) := by
        intro g
        rw [ih, hu]
      change c ≤ Nat.card {g : G // (φ.rename f).Realize (Function.update a (f i) g)} ↔ _
      have hc : Nat.card {g : G // (φ.rename f).Realize (Function.update a (f i) g)} =
          Nat.card {g : G // φ.Realize (Function.update (a ∘ f) i g)} :=
        Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl G) he)
      rw [hc]
      rfl

theorem variables_renameWord {m n : ℕ} (f : Fin m → Fin n) (w : GroupWord m) :
    wordVariables (renameWord f w) = (wordVariables w).image f := by
  induction w <;> simp_all [renameWord, wordVariables, Finset.image_union]

theorem freeVariables_rename {m n : ℕ} (f : Fin m → Fin n)
    (hf : Function.Injective f) (φ : Formula m) :
    (φ.rename f).freeVariables = φ.freeVariables.image f := by
  induction φ with
  | atom w => exact variables_renameWord f w
  | neg φ ih => exact ih
  | and φ ψ ihφ ihψ => simp [Formula.rename, Formula.freeVariables, ihφ, ihψ, Finset.image_union]
  | count c i φ ih =>
      simp only [Formula.rename, Formula.freeVariables, ih]
      ext j
      simp only [Finset.mem_erase, Finset.mem_image]
      constructor
      · rintro ⟨hne, l, hl, rfl⟩
        exact ⟨l, ⟨fun h => hne (congrArg f h), hl⟩, rfl⟩
      · rintro ⟨l, ⟨hli, hl⟩, rfl⟩
        exact ⟨fun h => hli (hf h), l, hl, rfl⟩

/-- A small formula transfers in any larger game with the needed reserve. -/
theorem realize_iff_of_winning_embedding {m n : ℕ} {G H : Type*}
    [Group G] [Group H] [Finite G] [Finite H]
    (f : Fin m → Fin n) (hf : Function.Injective f) (φ : Formula m)
    {p : Position (n + 1) G H} (hp : Winning p)
    (a : Fin n → G) (b : Fin n → H)
    (ht : ∀ i ∈ φ.freeVariables, p (f i).castSucc = some (a (f i), b (f i))) :
    φ.Realize (a ∘ f) ↔ φ.Realize (b ∘ f) := by
  rw [← realize_rename f hf, ← realize_rename f hf]
  apply realize_iff_of_winning_free _ hp
  intro j hj
  rw [freeVariables_rename f hf] at hj
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
  exact ht i hi

end GroupWL.CountingLogic
