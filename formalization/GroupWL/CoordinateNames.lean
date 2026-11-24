import GroupWL.CountingFormulas
import GroupWL.TensorGroup
import Mathlib.LinearAlgebra.Basis.Defs

/-! # Bounded-variable coordinate names

The recursive formulas alternate two working variables. The three anchors
are retained. Formula length grows with the coordinate description, while
the number of variable names does not.
-/
namespace GroupWL.CoordinateNames

open Refinement CountingLogic PebbleGame Module

def equalWords {m : ℕ} (u v : GroupWord m) : Formula m := .atom (.mul u (.inv v))

@[simp] theorem realize_equalWords {m : ℕ} {G : Type*} [Group G]
    (u v : GroupWord m) (a : Fin m → G) :
    (equalWords u v).Realize a ↔ u.eval a = v.eval a := by
  exact mul_inv_eq_one

def shiftWord {m : ℕ} (u t : Fin m) (c : ℕ) : GroupWord m :=
  .mul (.gen u) (.inv (wordPower (.gen t) c))

@[simp] theorem shiftWord_eval {m : ℕ} {G : Type*} [Group G]
    (u t : Fin m) (c : ℕ) (a : Fin m → G) :
    (shiftWord u t c).eval a = a u * (a t ^ c)⁻¹ := by
  simp [shiftWord, GroupWord.eval]

def hornerName {m : ℕ} (a₀ a₁ t u v : Fin m) : List ℕ → Formula m
  | [] => Formula.commutes (.gen u) (.gen a₀)
  | c :: cs => Formula.existsVar v (.and (hornerName a₀ a₁ t v u cs)
      (equalWords (commutatorWord (shiftWord u t c) (.gen a₀))
        (commutatorWord (.gen v) (.gen a₁))))

def hornerValue {F X : Type*} [Field F] [AddCommGroup X] [Module F X]
    (A : X →ₗ[F] X) (seed : X) : List ℕ → X
  | [] => 0
  | c :: cs => A (hornerValue A seed cs) + c • seed

theorem shiftWord_variables {m : ℕ} (u t : Fin m) (c : ℕ) :
    wordVariables (shiftWord u t c) ⊆ {u, t} := by
  intro j hj
  have hp := wordPower_variables (.gen t) c
  simp only [shiftWord, wordVariables, Finset.mem_union, Finset.mem_singleton] at hj
  rcases hj with rfl | hj
  · simp
  · have h : j = t := by simpa [wordVariables] using hp hj
    simp [h]

/-- Only the query and three anchors are free, regardless of coordinate length. -/
theorem hornerName_free {m : ℕ} (a₀ a₁ t u v : Fin m) (cs : List ℕ) :
    (hornerName a₀ a₁ t u v cs).freeVariables ⊆ {a₀, a₁, t, u} := by
  induction cs generalizing u v with
  | nil =>
      intro j hj
      simp only [hornerName, Formula.commutes, Formula.freeVariables,
        commutatorWord, wordVariables, Finset.mem_union, Finset.mem_singleton] at hj
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
  | cons c cs ih =>
      intro j hj
      have hrec : j ∈ (hornerName a₀ a₁ t v u cs).freeVariables →
          j ∈ ({a₀, a₁, t, v} : Finset (Fin m)) := fun h => ih v u h
      have hshift : j ∈ wordVariables (shiftWord u t c) →
          j ∈ ({u, t} : Finset (Fin m)) := fun h => shiftWord_variables u t c h
      simp only [hornerName, Formula.existsVar, Formula.freeVariables,
        equalWords, commutatorWord, wordVariables, Finset.mem_erase,
        Finset.mem_union, Finset.mem_singleton] at hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hrec hshift ⊢
      tauto

/-- Truth of a coordinate name transfers while only these four pairs are retained. -/
theorem hornerName_transfer {m : ℕ} {G H : Type*} [Group G] [Group H]
    [Finite G] [Finite H] {p : Position (m + 1) G H}
    (hp : Winning p) (a₀ a₁ t u v : Fin m) (cs : List ℕ)
    (a : Fin m → G) (b : Fin m → H)
    (htracks : TracksOn {a₀, a₁, t, u} p a b) :
    (hornerName a₀ a₁ t u v cs).Realize a ↔
      (hornerName a₀ a₁ t u v cs).Realize b := by
  apply realize_iff_of_winning_free _ hp
  intro i hi
  exact htracks i (hornerName_free a₀ a₁ t u v cs hi)

/-- Name a central element by two quotient representatives and four anchors.
The output may itself be a group word, such as a commutator of two queries. -/
def centralName {m : ℕ} (a₀ a₁ t b u v h : Fin m)
    (cs₀ cs₁ : List ℕ) (w : GroupWord m) : Formula m :=
  Formula.existsVar u (Formula.existsVar v
    (.and (hornerName a₀ a₁ t u h cs₀)
      (.and (hornerName a₀ a₁ t v h cs₁)
        (equalWords w (.mul (commutatorWord (.gen u) (.gen a₀))
          (commutatorWord (.gen v) (.gen b)))))))

/-- A quotient coordinate test whose query is an arbitrary group word. -/
def quotientWordName {m : ℕ} (a₀ a₁ t u v : Fin m)
    (cs : List ℕ) (w : GroupWord m) : Formula m :=
  Formula.existsVar u (.and (hornerName a₀ a₁ t u v cs)
    (equalWords (commutatorWord w (.gen a₀)) (commutatorWord (.gen u) (.gen a₀))))

theorem quotientWordName_free {m : ℕ} (a₀ a₁ t u v : Fin m)
    (cs : List ℕ) (w : GroupWord m) :
    (quotientWordName a₀ a₁ t u v cs w).freeVariables ⊆
      {a₀, a₁, t} ∪ wordVariables w := by
  intro j hj
  have hrec : j ∈ (hornerName a₀ a₁ t u v cs).freeVariables →
      j ∈ ({a₀, a₁, t, u} : Finset (Fin m)) := fun h => hornerName_free _ _ _ _ _ _ h
  simp only [quotientWordName, Formula.existsVar, Formula.freeVariables, equalWords,
    commutatorWord, wordVariables, Finset.mem_erase, Finset.mem_union,
    Finset.mem_singleton] at hj
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hrec ⊢
  tauto

theorem centralName_free {m : ℕ} (a₀ a₁ t b u v h : Fin m)
    (cs₀ cs₁ : List ℕ) (w : GroupWord m) :
    (centralName a₀ a₁ t b u v h cs₀ cs₁ w).freeVariables ⊆
      {a₀, a₁, t, b} ∪ wordVariables w := by
  intro j hj
  have h₀ : j ∈ (hornerName a₀ a₁ t u h cs₀).freeVariables →
      j ∈ ({a₀, a₁, t, u} : Finset (Fin m)) :=
    fun h => hornerName_free a₀ a₁ t u _ cs₀ h
  have h₁ : j ∈ (hornerName a₀ a₁ t v h cs₁).freeVariables →
      j ∈ ({a₀, a₁, t, v} : Finset (Fin m)) :=
    fun h => hornerName_free a₀ a₁ t v _ cs₁ h
  simp only [centralName, Formula.existsVar, Formula.freeVariables, equalWords,
    commutatorWord, wordVariables, Finset.mem_erase, Finset.mem_union,
    Finset.mem_singleton] at hj
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at h₀ h₁ ⊢
  tauto

def implication {m : ℕ} (φ ψ : Formula m) : Formula m := .neg (.and φ (.neg ψ))

@[simp] theorem realize_implication {m : ℕ} {G : Type*} [Group G]
    (φ ψ : Formula m) (a : Fin m → G) :
    (implication φ ψ).Realize a ↔ (φ.Realize a → ψ.Realize a) := by
  simp [implication, Formula.Realize]

def conjunction {m : ℕ} : List (Formula m) → Formula m
  | [] => .atom .one
  | φ :: fs => .and φ (conjunction fs)

@[simp] theorem realize_conjunction {m : ℕ} {G : Type*} [Group G]
    (fs : List (Formula m)) (a : Fin m → G) :
    (conjunction fs).Realize a ↔ ∀ φ ∈ fs, φ.Realize a := by
  induction fs with
  | nil => simp [conjunction, Formula.Realize, GroupWord.eval]
  | cons φ fs ih => simp [conjunction, Formula.Realize, ih]

/-- Four anchors, one matrix query and four reusable working variables. -/
def matrixName {n : ℕ} (inputs outputs₀ outputs₁ : Fin n → List ℕ) : Formula 9 :=
  .and (Formula.commutes (.gen 4) (.gen 0))
    (conjunction (List.ofFn (fun i : Fin n => Formula.allVar 5
      (implication (hornerName 0 1 2 5 8 (inputs i))
        (centralName 0 1 2 3 6 7 8 (outputs₀ i) (outputs₁ i)
          (commutatorWord (.gen 5) (.gen 4)))))))

theorem mem_conjunction_free {m : ℕ} (fs : List (Formula m)) (j : Fin m) :
    j ∈ (conjunction fs).freeVariables ↔ ∃ φ ∈ fs, j ∈ φ.freeVariables := by
  induction fs with
  | nil => simp [conjunction, Formula.freeVariables, wordVariables]
  | cons φ fs ih => simp [conjunction, Formula.freeVariables, ih]

theorem matrixName_free {n : ℕ} (inputs outputs₀ outputs₁ : Fin n → List ℕ) :
    (matrixName inputs outputs₀ outputs₁).freeVariables ⊆ {0, 1, 2, 3, 4} := by
  intro j hj
  rcases Finset.mem_union.mp hj with hj | hj
  · simp only [Formula.commutes, Formula.freeVariables, commutatorWord,
      wordVariables, Finset.mem_union, Finset.mem_singleton] at hj
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · obtain ⟨φ, hφ, hj⟩ := (mem_conjunction_free _ j).mp hj
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hφ
    have h₀ : j ∈ (hornerName 0 1 2 5 8 (inputs i)).freeVariables →
        j ∈ ({0, 1, 2, 5} : Finset (Fin 9)) := fun h => hornerName_free _ _ _ _ _ _ h
    have h₁ := centralName_free (0 : Fin 9) 1 2 3 6 7 8 (outputs₀ i) (outputs₁ i)
      (commutatorWord (.gen 5) (.gen 4)) (a := j)
    simp only [Formula.allVar, Formula.existsVar, implication, Formula.freeVariables,
      Finset.mem_erase, Finset.mem_union] at hj
    simp only [commutatorWord, wordVariables, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton] at h₀ h₁ ⊢
    tauto

section Reference

variable {F X Z : Type*} [Field F] [NeZero (2 : F)]
  [AddCommGroup X] [Module F X] [AddCommGroup Z] [Module F Z]
variable (Y : Submodule F (X →ₗ[F] Z)) (ε : AlternatingBilinearMap F X Z)

theorem commutator_anchor (g a : TensorGroup (evaluationTwist Y ε))
    (y : Y) (ha : a.fst = (0, y)) :
    g * a * g⁻¹ * a⁻¹ = ⟨0, (y : X →ₗ[F] Z) g.fst.1⟩ := by
  rw [TensorGroup.commutator_eq]
  congr 1
  simp [evaluationTwist_apply, ha]

theorem commutes_anchor_iff (g a : TensorGroup (evaluationTwist Y ε))
    (y : Y) (ha : a.fst = (0, y)) (hy : Function.Injective (y : X →ₗ[F] Z)) :
    g * a = a * g ↔ g.fst.1 = 0 := by
  rw [TensorGroup.mul_comm_iff]
  simp only [ha, evaluationTwist_apply, map_zero, sub_zero,
    AlternatingBilinearMap.zero_right, add_zero]
  exact hy.eq_iff' (map_zero (y : X →ₗ[F] Z))

theorem compare_anchors (g h a₀ a₁ : TensorGroup (evaluationTwist Y ε))
    (y₀ y₁ : Y) (ha₀ : a₀.fst = (0, y₀)) (ha₁ : a₁.fst = (0, y₁))
    (hy₀ : Function.Injective (y₀ : X →ₗ[F] Z)) (A : X →ₗ[F] X)
    (hA : ∀ x, (y₁ : X →ₗ[F] Z) x = (y₀ : X →ₗ[F] Z) (A x)) :
    g * a₀ * g⁻¹ * a₀⁻¹ = h * a₁ * h⁻¹ * a₁⁻¹ ↔ g.fst.1 = A h.fst.1 := by
  rw [commutator_anchor Y ε g a₀ y₀ ha₀, commutator_anchor Y ε h a₁ y₁ ha₁]
  constructor
  · intro h
    apply hy₀
    exact (congrArg TensorGroup.snd h).trans (hA _)
  · intro h
    congr 1
    rw [h, hA]

theorem quotient_shift (g t : TensorGroup (evaluationTwist Y ε)) (c : ℕ) :
    (g * (t ^ c)⁻¹).fst.1 = g.fst.1 - c • t.fst.1 := by
  rw [TensorGroup.pow_eq]
  simp [sub_eq_add_neg]

/-- The actual reference-group semantics of the fixed-variable Horner formula.
Central offsets of the anchors and every twist are allowed. -/
theorem realize_hornerName {m : ℕ} [Finite (TensorGroup (evaluationTwist Y ε))]
    (a₀ a₁ t u v : Fin m) (huv : u ≠ v)
    (hu : u ∉ ({a₀, a₁, t} : Finset (Fin m)))
    (hv : v ∉ ({a₀, a₁, t} : Finset (Fin m)))
    (y₀ y₁ : Y) (hy₀ : Function.Injective (y₀ : X →ₗ[F] Z))
    (A : X →ₗ[F] X) (hA : ∀ x, (y₁ : X →ₗ[F] Z) x = (y₀ : X →ₗ[F] Z) (A x))
    (cs : List ℕ) (a : Fin m → TensorGroup (evaluationTwist Y ε))
    (ha₀ : (a a₀).fst = (0, y₀)) (ha₁ : (a a₁).fst = (0, y₁)) :
    (hornerName a₀ a₁ t u v cs).Realize a ↔
      (a u).fst.1 = hornerValue A (a t).fst.1 cs := by
  induction cs generalizing u v a with
  | nil =>
      simpa [hornerName, hornerValue, GroupWord.eval] using
        commutes_anchor_iff Y ε (a u) (a a₀) y₀ ha₀ hy₀
  | cons c cs ih =>
      have hv₀ : a₀ ≠ v := by intro h; apply hv; simp [← h]
      have hv₁ : a₁ ≠ v := by intro h; apply hv; simp [← h]
      have hvt : t ≠ v := by intro h; apply hv; simp [← h]
      simp only [hornerName, realize_existsVar, Formula.Realize]
      have hrec (g : TensorGroup (evaluationTwist Y ε)) :
          (hornerName a₀ a₁ t v u cs).Realize (Function.update a v g) ↔
            g.fst.1 = hornerValue A (a t).fst.1 cs := by
        simpa [hv₀, hv₁, hvt] using
          ih v u (Ne.symm huv) hv hu (Function.update a v g)
            (by simpa [hv₀] using ha₀) (by simpa [hv₁] using ha₁)
      have hcmp (g : TensorGroup (evaluationTwist Y ε)) :
          (equalWords (commutatorWord (shiftWord u t c) (.gen a₀))
            (commutatorWord (.gen v) (.gen a₁))).Realize (Function.update a v g) ↔
          (a u).fst.1 - c • (a t).fst.1 = A g.fst.1 := by
        simp only [realize_equalWords, commutatorWord, GroupWord.eval, shiftWord_eval,
          Function.update_self, Function.update_of_ne huv, Function.update_of_ne hv₀,
          Function.update_of_ne hv₁, Function.update_of_ne hvt]
        rw [compare_anchors Y ε _ _ _ _ y₀ y₁ ha₀ ha₁ hy₀ A hA, quotient_shift]
      simp_rw [hrec, hcmp]
      constructor
      · rintro ⟨g, hg, h⟩
        rw [hg] at h
        exact sub_eq_iff_eq_add.mp h
      · intro h
        refine ⟨⟨(hornerValue A (a t).fst.1 cs, 0), 0⟩, rfl, ?_⟩
        exact sub_eq_iff_eq_add.mpr h

theorem realize_quotientWordName {m : ℕ} [Finite (TensorGroup (evaluationTwist Y ε))]
    (a₀ a₁ t u v : Fin m) (huv : u ≠ v)
    (hu : u ∉ ({a₀, a₁, t} : Finset (Fin m)))
    (hv : v ∉ ({a₀, a₁, t} : Finset (Fin m)))
    (y₀ y₁ : Y) (hy₀ : Function.Injective (y₀ : X →ₗ[F] Z))
    (A : X →ₗ[F] X) (hA : ∀ x, (y₁ : X →ₗ[F] Z) x = (y₀ : X →ₗ[F] Z) (A x))
    (cs : List ℕ) (w : GroupWord m) (hw : u ∉ wordVariables w)
    (a : Fin m → TensorGroup (evaluationTwist Y ε))
    (ha₀ : (a a₀).fst = (0, y₀)) (ha₁ : (a a₁).fst = (0, y₁)) :
    (quotientWordName a₀ a₁ t u v cs w).Realize a ↔
      (w.eval a).fst.1 = hornerValue A (a t).fst.1 cs := by
  have hu₀ : a₀ ≠ u := by intro e; apply hu; simp [← e]
  have hu₁ : a₁ ≠ u := by intro e; apply hu; simp [← e]
  have hut : t ≠ u := by intro e; apply hu; simp [← e]
  have hname (g : TensorGroup (evaluationTwist Y ε)) :
      (hornerName a₀ a₁ t u v cs).Realize (Function.update a u g) ↔
        g.fst.1 = hornerValue A (a t).fst.1 cs := by
    simpa [hut] using realize_hornerName Y ε a₀ a₁ t u v huv hu hv
      y₀ y₁ hy₀ A hA cs (Function.update a u g)
      (by simpa [hu₀] using ha₀) (by simpa [hu₁] using ha₁)
  have hcompare (g : TensorGroup (evaluationTwist Y ε)) :
      (equalWords (commutatorWord w (.gen a₀)) (commutatorWord (.gen u) (.gen a₀))).Realize
        (Function.update a u g) ↔ (w.eval a).fst.1 = g.fst.1 := by
    have hw' : w.eval (Function.update a u g) = w.eval a := by
      apply word_eval_congr
      intro j hj
      have hju : j ≠ u := fun e => hw (e ▸ hj)
      simp [hju]
    simp only [realize_equalWords, commutatorWord, GroupWord.eval,
      Function.update_of_ne hu₀, Function.update_self, hw']
    exact compare_anchors Y ε _ _ _ _ y₀ y₀ ha₀ ha₀ hy₀ (LinearMap.id) (fun _ => rfl)
  simp only [quotientWordName, realize_existsVar, Formula.Realize]
  simp_rw [hname, hcompare]
  constructor
  · rintro ⟨g, hg, hwg⟩
    exact hwg.trans hg
  · intro hx
    exact ⟨⟨(hornerValue A (a t).fst.1 cs, 0), 0⟩, rfl, hx⟩

theorem realize_centralName {m : ℕ} [Finite (TensorGroup (evaluationTwist Y ε))]
    (a₀ a₁ t b u v h : Fin m) (huv : u ≠ v) (huh : u ≠ h) (hvh : v ≠ h)
    (hu : u ∉ ({a₀, a₁, t, b} : Finset (Fin m)))
    (hv : v ∉ ({a₀, a₁, t, b} : Finset (Fin m)))
    (hh : h ∉ ({a₀, a₁, t} : Finset (Fin m)))
    (y₀ y₁ yb : Y) (hy₀ : Function.Injective (y₀ : X →ₗ[F] Z))
    (A : X →ₗ[F] X) (hA : ∀ x, (y₁ : X →ₗ[F] Z) x = (y₀ : X →ₗ[F] Z) (A x))
    (cs₀ cs₁ : List ℕ) (w : GroupWord m)
    (hw : u ∉ wordVariables w ∧ v ∉ wordVariables w)
    (a : Fin m → TensorGroup (evaluationTwist Y ε))
    (ha₀ : (a a₀).fst = (0, y₀)) (ha₁ : (a a₁).fst = (0, y₁))
    (hb : (a b).fst = (0, yb)) :
    (centralName a₀ a₁ t b u v h cs₀ cs₁ w).Realize a ↔
      w.eval a = ⟨0, (y₀ : X →ₗ[F] Z) (hornerValue A (a t).fst.1 cs₀) +
        (yb : X →ₗ[F] Z) (hornerValue A (a t).fst.1 cs₁)⟩ := by
  have hu₀ : a₀ ≠ u := by intro e; apply hu; simp [← e]
  have hu₁ : a₁ ≠ u := by intro e; apply hu; simp [← e]
  have hut : t ≠ u := by intro e; apply hu; simp [← e]
  have hub : b ≠ u := by intro e; apply hu; simp [← e]
  have hv₀ : a₀ ≠ v := by intro e; apply hv; simp [← e]
  have hv₁ : a₁ ≠ v := by intro e; apply hv; simp [← e]
  have hvt : t ≠ v := by intro e; apply hv; simp [← e]
  have hvb : b ≠ v := by intro e; apply hv; simp [← e]
  have hu' : u ∉ ({a₀, a₁, t} : Finset (Fin m)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu ⊢
    tauto
  have hv' : v ∉ ({a₀, a₁, t} : Finset (Fin m)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv ⊢
    tauto
  have names₀ (g g' : TensorGroup (evaluationTwist Y ε)) :
      (hornerName a₀ a₁ t u h cs₀).Realize (Function.update (Function.update a u g) v g') ↔
        g.fst.1 = hornerValue A (a t).fst.1 cs₀ := by
    simpa [huv, hu₀, hu₁, hut, hv₀, hv₁, hvt] using
      realize_hornerName Y ε a₀ a₁ t u h huh hu' hh y₀ y₁ hy₀ A hA cs₀
        (Function.update (Function.update a u g) v g')
        (by simpa [hu₀, hv₀] using ha₀) (by simpa [hu₁, hv₁] using ha₁)
  have names₁ (g g' : TensorGroup (evaluationTwist Y ε)) :
      (hornerName a₀ a₁ t v h cs₁).Realize (Function.update (Function.update a u g) v g') ↔
        g'.fst.1 = hornerValue A (a t).fst.1 cs₁ := by
    simpa [hut, hvt] using
      realize_hornerName Y ε a₀ a₁ t v h hvh hv' hh y₀ y₁ hy₀ A hA cs₁
        (Function.update (Function.update a u g) v g')
        (by simpa [hu₀, hv₀] using ha₀) (by simpa [hu₁, hv₁] using ha₁)
  have outputs (g g' : TensorGroup (evaluationTwist Y ε)) :
      (equalWords w (.mul (commutatorWord (.gen u) (.gen a₀))
        (commutatorWord (.gen v) (.gen b)))).Realize
          (Function.update (Function.update a u g) v g') ↔
      w.eval a = ⟨0, (y₀ : X →ₗ[F] Z) g.fst.1 + (yb : X →ₗ[F] Z) g'.fst.1⟩ := by
    have hw' : w.eval (Function.update (Function.update a u g) v g') = w.eval a := by
      apply word_eval_congr
      intro j hj
      have hju : j ≠ u := fun e => hw.1 (e ▸ hj)
      have hjv : j ≠ v := fun e => hw.2 (e ▸ hj)
      simp [hju, hjv]
    simp only [realize_equalWords, commutatorWord, GroupWord.eval, Function.update_self,
      Function.update_of_ne huv, Function.update_of_ne hu₀, Function.update_of_ne hv₀,
      Function.update_of_ne hub, Function.update_of_ne hvb, hw']
    rw [commutator_anchor Y ε g (a a₀) y₀ ha₀, commutator_anchor Y ε g' (a b) yb hb]
    have hm (z z' : Z) : (⟨0, z⟩ : TensorGroup (evaluationTwist Y ε)) * ⟨0, z'⟩ =
        ⟨0, z + z'⟩ := by ext <;> simp
    rw [hm]
  simp only [centralName, realize_existsVar, Formula.Realize]
  simp_rw [names₀, names₁, outputs]
  constructor
  · rintro ⟨g, g', hg, hg', hout⟩
    simpa [hg, hg'] using hout
  · intro hout
    exact ⟨⟨(hornerValue A (a t).fst.1 cs₀, 0), 0⟩,
      ⟨(hornerValue A (a t).fst.1 cs₁, 0), 0⟩, rfl, rfl, hout⟩

/-- The nine-variable matrix formula reads exactly the evaluations at all
listed quotient vectors; it allows arbitrary central offsets in the answer. -/
theorem realize_matrixName {n : ℕ} [Finite (TensorGroup (evaluationTwist Y ε))]
    (inputs outputs₀ outputs₁ : Fin n → List ℕ)
    (y₀ y₁ yb : Y) (hy₀ : Function.Injective (y₀ : X →ₗ[F] Z))
    (A : X →ₗ[F] X) (hA : ∀ x, (y₁ : X →ₗ[F] Z) x = (y₀ : X →ₗ[F] Z) (A x))
    (a : Fin 9 → TensorGroup (evaluationTwist Y ε))
    (ha₀ : (a 0).fst = (0, y₀)) (ha₁ : (a 1).fst = (0, y₁))
    (hb : (a 3).fst = (0, yb)) :
    (matrixName inputs outputs₀ outputs₁).Realize a ↔
      (a 4).fst.1 = 0 ∧ ∀ i,
        ((a 4).fst.2 : X →ₗ[F] Z) (hornerValue A (a 2).fst.1 (inputs i)) =
          (y₀ : X →ₗ[F] Z) (hornerValue A (a 2).fst.1 (outputs₀ i)) +
          (yb : X →ₗ[F] Z) (hornerValue A (a 2).fst.1 (outputs₁ i)) := by
  have namesIn (i : Fin n) (g : TensorGroup (evaluationTwist Y ε)) :
      (hornerName 0 1 2 5 8 (inputs i)).Realize (Function.update a 5 g) ↔
        g.fst.1 = hornerValue A (a 2).fst.1 (inputs i) := by
    simpa using realize_hornerName Y ε (0 : Fin 9) 1 2 5 8 (by decide)
      (by decide) (by decide) y₀ y₁ hy₀ A hA (inputs i) (Function.update a 5 g)
      (by simpa using ha₀) (by simpa using ha₁)
  have namesOut (i : Fin n) (g : TensorGroup (evaluationTwist Y ε)) :
      (centralName 0 1 2 3 6 7 8 (outputs₀ i) (outputs₁ i)
        (commutatorWord (.gen 5) (.gen 4))).Realize (Function.update a 5 g) ↔
      g * a 4 * g⁻¹ * (a 4)⁻¹ =
        ⟨0, (y₀ : X →ₗ[F] Z) (hornerValue A (a 2).fst.1 (outputs₀ i)) +
          (yb : X →ₗ[F] Z) (hornerValue A (a 2).fst.1 (outputs₁ i))⟩ := by
    simpa [commutatorWord, GroupWord.eval] using
      realize_centralName Y ε (0 : Fin 9) 1 2 3 6 7 8 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        y₀ y₁ yb hy₀ A hA (outputs₀ i) (outputs₁ i)
        (commutatorWord (.gen 5) (.gen 4))
        (by decide) (Function.update a 5 g)
        (by simpa using ha₀) (by simpa using ha₁) (by simpa using hb)
  simp only [matrixName, Formula.Realize, realize_commutes, GroupWord.eval,
    realize_conjunction, List.forall_mem_ofFn_iff, realize_allVar, realize_implication]
  rw [commutes_anchor_iff Y ε (a 4) (a 0) y₀ ha₀ hy₀]
  simp_rw [namesIn, namesOut]
  constructor
  · rintro ⟨hx, hall⟩
    refine ⟨hx, fun i => ?_⟩
    have h := hall i (⟨(hornerValue A (a 2).fst.1 (inputs i), 0), 0⟩) rfl
    rw [commutator_anchor Y ε _ (a 4) (a 4).fst.2 (Prod.ext hx rfl)] at h
    exact congrArg TensorGroup.snd h
  · rintro ⟨hx, hall⟩
    refine ⟨hx, fun i g hg => ?_⟩
    rw [commutator_anchor Y ε g (a 4) (a 4).fst.2 (Prod.ext hx rfl), hg, hall i]

theorem realize_matrixName_basis {n : ℕ} [Finite (TensorGroup (evaluationTwist Y ε))]
    (inputs outputs₀ outputs₁ : Fin n → List ℕ)
    (y₀ y₁ yb y : Y) (hy₀ : Function.Injective (y₀ : X →ₗ[F] Z))
    (A : X →ₗ[F] X) (hA : ∀ x, (y₁ : X →ₗ[F] Z) x = (y₀ : X →ₗ[F] Z) (A x))
    (a : Fin 9 → TensorGroup (evaluationTwist Y ε))
    (ha₀ : (a 0).fst = (0, y₀)) (ha₁ : (a 1).fst = (0, y₁))
    (hb : (a 3).fst = (0, yb)) (basis : Basis (Fin n) F X)
    (hinputs : ∀ i, hornerValue A (a 2).fst.1 (inputs i) = basis i)
    (houtputs : ∀ i, (y₀ : X →ₗ[F] Z) (hornerValue A (a 2).fst.1 (outputs₀ i)) +
        (yb : X →ₗ[F] Z) (hornerValue A (a 2).fst.1 (outputs₁ i)) = (y : X →ₗ[F] Z) (basis i)) :
    (matrixName inputs outputs₀ outputs₁).Realize a ↔ (a 4).fst = (0, y) := by
  rw [realize_matrixName Y ε inputs outputs₀ outputs₁ y₀ y₁ yb hy₀ A hA a ha₀ ha₁ hb]
  simp_rw [hinputs, houtputs]
  constructor
  · rintro ⟨hx, he⟩
    exact Prod.ext hx (Subtype.ext (basis.ext he))
  · intro h
    simp [h]

end Reference
end GroupWL.CoordinateNames
