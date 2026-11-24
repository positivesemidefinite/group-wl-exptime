import GroupWL.CountingFormulas
import GroupWL.CentralizerCardinality
import GroupWL.BaerSubgroups

/-! Transfer of the actual centralizer-threshold subgroup to an arbitrary group. -/

namespace GroupWL.CountingLogic

open Refinement PebbleGame

def centralizerWordAtLeastFormula {m : ℕ} (w : GroupWord m) (k : Fin m) (n : ℕ) :
    Formula m := .count n k (Formula.commutes w (.gen k))

theorem realize_centralizerWordAtLeastFormula {m : ℕ} {G : Type*} [Group G]
    (w : GroupWord m) (k : Fin m) (hk : k ∉ wordVariables w) (n : ℕ) (a : Fin m → G) :
    (centralizerWordAtLeastFormula w k n).Realize a ↔
      n ≤ Nat.card {h : G // w.eval a * h = h * w.eval a} := by
  change n ≤ Nat.card {h : G // (Formula.commutes w (.gen k)).Realize
    (Function.update a k h)} ↔ _
  have hw (h : G) : w.eval (Function.update a k h) = w.eval a := by
    apply word_eval_congr
    intro i hi
    have hik : i ≠ k := fun hik => hk (hik ▸ hi)
    exact Function.update_of_ne hik h a
  have hc : Nat.card {h : G // (Formula.commutes w (.gen k)).Realize
      (Function.update a k h)} = Nat.card {h : G // w.eval a * h = h * w.eval a} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquiv (Equiv.refl G) (fun h => by simp [hw, GroupWord.eval])
  rw [hc]

/-- Nonempty, closed under `x*y⁻¹`, and commutative, in three variable names. -/
def thresholdLawsFormula {m : ℕ} (i j k : Fin m) (T : ℕ) : Formula m :=
  .and (centralizerWordAtLeastFormula .one k T)
    (.and
      (Formula.allVar i (Formula.allVar j
        (.neg (.and
          (.and (centralizerAtLeastFormula i k T) (centralizerAtLeastFormula j k T))
          (.neg (centralizerWordAtLeastFormula (.mul (.gen i) (.inv (.gen j))) k T))))))
      (Formula.allVar i (Formula.allVar j
        (.neg (.and
          (.and (centralizerAtLeastFormula i k T) (centralizerAtLeastFormula j k T))
          (.neg (Formula.commutes (.gen i) (.gen j))))))))

theorem realize_thresholdLawsFormula {m : ℕ} {G : Type*} [Group G] [Finite G]
    (i j k : Fin m) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (T : ℕ) (a : Fin m → G) :
    (thresholdLawsFormula i j k T).Realize a ↔
      (T ≤ Nat.card {h : G // (1 : G) * h = h * 1}) ∧
      (∀ x y : G,
        T ≤ Nat.card {h : G // x * h = h * x} →
        T ≤ Nat.card {h : G // y * h = h * y} →
        T ≤ Nat.card {h : G // (x * y⁻¹) * h = h * (x * y⁻¹)}) ∧
      (∀ x y : G,
        T ≤ Nat.card {h : G // x * h = h * x} →
        T ≤ Nat.card {h : G // y * h = h * y} → x * y = y * x) := by
  have hnone : k ∉ wordVariables (GroupWord.one : GroupWord m) := by simp [wordVariables]
  have hword : k ∉ wordVariables (.mul (.gen i) (.inv (.gen j))) := by
    simp [wordVariables, Ne.symm hik, Ne.symm hjk]
  simp [thresholdLawsFormula, Formula.Realize, realize_allVar,
    realize_centralizerWordAtLeastFormula _ _ hnone,
    realize_centralizerWordAtLeastFormula _ _ hword,
    realize_centralizerAtLeastFormula _ _ hik,
    realize_centralizerAtLeastFormula _ _ hjk, GroupWord.eval, hij]

theorem thresholdLawsFormula_closed {m : ℕ} (i j k : Fin m) (T : ℕ) :
    (thresholdLawsFormula i j k T).freeVariables = ∅ := by
  ext l
  simp [thresholdLawsFormula, centralizerWordAtLeastFormula,
    centralizerAtLeastFormula, Formula.allVar, Formula.existsVar, Formula.commutes,
    commutatorWord, Formula.freeVariables, wordVariables]
  tauto

/-- A threshold that is an abelian subgroup in one group is an actual abelian
subgroup in every group with a winning position. -/
theorem threshold_subgroup_transfer {m : ℕ} {G H : Type*} [Group G] [Group H]
    [Finite G] [Finite H] {p : Position (m + 1) G H} (hp : Winning p)
    (i j k : Fin m) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (T : ℕ) (S : Subgroup G)
    (hS : ∀ g : G, g ∈ S ↔ T ≤ Nat.card {x : G // g * x = x * g})
    (hab : ∀ g ∈ S, ∀ h ∈ S, g * h = h * g) :
    ∃ B : Subgroup H,
      (∀ h : H, h ∈ B ↔ T ≤ Nat.card {x : H // h * x = x * h}) ∧
      (∀ g ∈ B, ∀ h ∈ B, g * h = h * g) ∧ Nat.card B = Nat.card S := by
  have hlaws : (thresholdLawsFormula i j k T).Realize (fun _ : Fin m => (1 : G)) := by
    rw [realize_thresholdLawsFormula i j k hij hik hjk]
    refine ⟨(hS 1).mp S.one_mem, ?_, ?_⟩
    · intro x y hx hy
      exact (hS _).mp (S.mul_mem ((hS x).mpr hx) (S.inv_mem ((hS y).mpr hy)))
    · intro x y hx hy
      exact hab x ((hS x).mpr hx) y ((hS y).mpr hy)
  have htr := realize_iff_of_winning_free (thresholdLawsFormula i j k T)
    (a := fun _ => (1 : G)) (b := fun _ => (1 : H)) hp (by
      intro l hl
      simp [thresholdLawsFormula_closed] at hl)
  obtain ⟨h1, hmul, habH⟩ :=
    (realize_thresholdLawsFormula i j k hij hik hjk T (fun _ => (1 : H))).mp (htr.mp hlaws)
  let B : Subgroup H := Subgroup.ofDiv
    {h : H | T ≤ Nat.card {x : H // h * x = x * h}} ⟨1, h1⟩
    (fun x hx y hy => hmul x y hx hy)
  refine ⟨B, fun h => Iff.rfl, ?_, ?_⟩
  · intro g hg h hh
    exact habH g h hg hh
  · have hcard := centralizer_set_card_transfer hp i k hik T
    have hSCard : Nat.card S =
        Nat.card {g : G // T ≤ Nat.card {x : G // g * x = x * g}} := by
      apply Nat.card_congr
      exact Equiv.subtypeEquiv (Equiv.refl G) hS
    exact hcard.symm.trans hSCard.symm

def centerCountFormula {m : ℕ} (i j : Fin m) (n : ℕ) : Formula m :=
  .count n i (centralFormula i j)

theorem centrality_transfer {m : ℕ} {G H : Type*} [Group G] [Group H]
    [Finite G] [Finite H] {p : Position (m + 1) G H} (hp : Winning p)
    (i j : Fin m) (hij : i ≠ j) {g : G} {h : H}
    (hmark : p i.castSucc = some (g, h)) :
    (∀ x : G, g * x = x * g) ↔ (∀ x : H, h * x = x * h) := by
  have htr := realize_iff_of_winning_free (centralFormula i j)
    (a := fun _ => g) (b := fun _ => h) hp (by
      intro l hl
      have hli : l = i := by
        simp only [centralFormula, Formula.allVar, Formula.existsVar, Formula.commutes,
          commutatorWord, Formula.freeVariables, wordVariables, Finset.mem_erase,
          Finset.mem_union, Finset.mem_singleton] at hl
        tauto
      simpa [hli] using hmark)
  simpa only [realize_centralFormula i j hij] using htr

theorem realize_centerCountFormula {m : ℕ} {K : Type*} [Group K] [Finite K]
    (i j : Fin m) (hij : i ≠ j) (n : ℕ) (a : Fin m → K) :
      (centerCountFormula i j n).Realize a ↔ n ≤ Nat.card (Subgroup.center K) := by
    change n ≤ Nat.card {g : K // (centralFormula i j).Realize
      (Function.update a i g)} ↔ _
    have hc : Nat.card {g : K // (centralFormula i j).Realize
        (Function.update a i g)} = Nat.card (Subgroup.center K) := by
      apply Nat.card_congr
      refine Equiv.subtypeEquiv (Equiv.refl K) (fun g => ?_)
      simp only [realize_centralFormula i j hij, Function.update_self, Equiv.refl_apply,
        Subgroup.mem_center_iff]
      exact forall_congr' (fun h => eq_comm)
    rw [hc]

theorem center_card_transfer {m : ℕ} {G H : Type*} [Group G] [Group H]
    [Finite G] [Finite H] {p : Position (m + 1) G H} (hp : Winning p)
    (i j : Fin m) (hij : i ≠ j) :
    Nat.card (Subgroup.center G) = Nat.card (Subgroup.center H) := by
  have hclosed (n : ℕ) : (centerCountFormula i j n).freeVariables = ∅ := by
    ext l
    simp [centerCountFormula, centralFormula, Formula.allVar, Formula.existsVar, Formula.commutes,
      commutatorWord, Formula.freeVariables, wordVariables]
    tauto
  have htr (n : ℕ) : n ≤ Nat.card (Subgroup.center G) ↔
      n ≤ Nat.card (Subgroup.center H) := by
    have h := realize_iff_of_winning_free (centerCountFormula i j n)
      (a := fun _ => (1 : G)) (b := fun _ => (1 : H)) hp (by
        intro l hl
        simp [hclosed] at hl)
    simpa only [realize_centerCountFormula i j hij] using h
  exact Nat.le_antisymm ((htr _).mp le_rfl) ((htr _).mpr le_rfl)

end GroupWL.CountingLogic

namespace GroupWL

open PebbleGame

/-- The matrix sector is recovered as an actual abelian subgroup in an
arbitrary opponent, and has the same exact cardinality. -/
theorem exists_matrix_subgroup_of_winning
    {p m : ℕ} [Fact p.Prime] [NeZero (2 : ZMod p)]
    {X Z H : Type*} [AddCommGroup X] [Module (ZMod p) X]
    [AddCommGroup Z] [Module (ZMod p) Z]
    [FiniteDimensional (ZMod p) X] [FiniteDimensional (ZMod p) Z]
    [Group H] [Finite H]
    (Y : Submodule (ZMod p) (X →ₗ[ZMod p] Z))
    (ε : AlternatingBilinearMap (ZMod p) X Z)
    (heval : ∀ x : X, x ≠ 0 →
      Function.Surjective (fun y : Y => (y : X →ₗ[ZMod p] Z) x))
    (hdim : Module.finrank (ZMod p) X < Module.finrank (ZMod p) Z)
    {pos : Position (m + 1) (TensorGroup (evaluationTwist Y ε)) H} (hp : Winning pos)
    (i j k : Fin m) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ B : Subgroup H,
      (∀ h : H, h ∈ B ↔
        p ^ (Module.finrank (ZMod p) X + Module.finrank (ZMod p) Y) <
          Nat.card {x : H // h * x = x * h}) ∧
      (∀ g ∈ B, ∀ h ∈ B, g * h = h * g) ∧
      Nat.card B = p ^ (Module.finrank (ZMod p) Y + Module.finrank (ZMod p) Z) := by
  letI : Finite X := Module.finite_of_finite (ZMod p)
  letI : Finite Z := Module.finite_of_finite (ZMod p)
  letI : Finite Y := Module.finite_of_finite (ZMod p)
  let S := inputSubgroup Y ε (⊥ : Submodule (ZMod p) X)
  obtain ⟨B, hB, hab, hcard⟩ := CountingLogic.threshold_subgroup_transfer hp i j k hij hik hjk
    (p ^ (Module.finrank (ZMod p) X + Module.finrank (ZMod p) Y) + 1) S (by
      intro g
      change g.fst.1 ∈ (⊥ : Submodule (ZMod p) X) ↔ _
      rw [Submodule.mem_bot, Nat.add_one_le_iff]
      exact matrixSector_iff_centralizer_card_gt Y ε heval hdim g) (by
      intro g hg h hh
      exact matrixSector_commutative Y ε g h hg hh)
  refine ⟨B, ?_, hab, hcard.trans ?_⟩
  · intro h
    exact (hB h).trans Nat.add_one_le_iff
  · exact matrixSector_card Y ε

end GroupWL
