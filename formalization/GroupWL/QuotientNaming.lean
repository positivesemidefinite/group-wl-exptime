import GroupWL.CoordinateNames
import GroupWL.FormulaRename
import GroupWL.BaerGroup
import GroupWL.ThresholdRecognition

/-! Quotient coordinates in an arbitrary opponent, constructed from the
concrete Horner formulas and a winning position. -/

namespace GroupWL.CoordinateNames

open Refinement CountingLogic PebbleGame

/-- The semantic relation tested by the actual quotient-word formula. The
query is a group element, so the same relation applies to compound words. -/
def quotientRelation {G : Type*} [Group G] (a : Fin 9 → G) (cs : List ℕ) (g : G) : Prop :=
  ∃ u : G, (hornerName 0 1 2 6 7 cs).Realize (Function.update a 6 u) ∧
    g * a 0 * g⁻¹ * (a 0)⁻¹ = u * a 0 * u⁻¹ * (a 0)⁻¹

theorem quotientRelation_congr {G : Type*} [Group G]
    {a b : Fin 9 → G} (h : ∀ i ∈ ({0, 1, 2} : Finset (Fin 9)), a i = b i)
    (cs : List ℕ) (g : G) : quotientRelation a cs g ↔ quotientRelation b cs g := by
  have hnames (u : G) :
      (hornerName 0 1 2 6 7 cs).Realize (Function.update a 6 u) ↔
        (hornerName 0 1 2 6 7 cs).Realize (Function.update b 6 u) := by
    apply realize_congr
    intro i hi
    have hi' := hornerName_free (0 : Fin 9) 1 2 6 7 cs hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi'
    rcases hi' with rfl | rfl | rfl | rfl
    · simpa using h 0 (by decide)
    · simpa using h 1 (by decide)
    · simpa using h 2 (by decide)
    · simp
  simp only [quotientRelation, hnames, h 0 (by decide)]

theorem realize_quotientWordName_relation {G : Type*} [Group G] [Finite G]
    (a : Fin 9 → G) (cs : List ℕ) (w : GroupWord 9) (hw : 6 ∉ wordVariables w) :
    (quotientWordName 0 1 2 6 7 cs w).Realize a ↔
      quotientRelation a cs (w.eval a) := by
  have hw' (u : G) : w.eval (Function.update a 6 u) = w.eval a := by
    apply word_eval_congr
    intro i hi
    have hi6 : i ≠ 6 := fun he => hw (he ▸ hi)
    simp [hi6]
  simp only [quotientWordName, realize_existsVar]
  change (∃ u : G, (hornerName 0 1 2 6 7 cs).Realize (Function.update a 6 u) ∧
    (equalWords (commutatorWord w (.gen 0))
      (commutatorWord (.gen 6) (.gen 0))).Realize (Function.update a 6 u)) ↔ _
  simp only [realize_equalWords, commutatorWord, GroupWord.eval, hw',
    Function.update_self, Function.update_of_ne (by decide : (0 : Fin 9) ≠ 6)]
  rfl

section Reference

variable {F X Z : Type*} [Field F] [NeZero (2 : F)]
  [AddCommGroup X] [Module F X] [AddCommGroup Z] [Module F Z]
  (Y : Submodule F (X →ₗ[F] Z)) (ε : AlternatingBilinearMap F X Z)

theorem quotientRelation_reference [Finite (TensorGroup (evaluationTwist Y ε))]
    (y₀ y₁ : Y) (hy₀ : Function.Injective (y₀ : X →ₗ[F] Z))
    (A : X →ₗ[F] X) (hA : ∀ x, (y₁ : X →ₗ[F] Z) x = (y₀ : X →ₗ[F] Z) (A x))
    (a : Fin 9 → TensorGroup (evaluationTwist Y ε))
    (ha₀ : (a 0).fst = (0, y₀)) (ha₁ : (a 1).fst = (0, y₁))
    (cs : List ℕ) (g : TensorGroup (evaluationTwist Y ε)) :
    quotientRelation a cs g ↔ g.fst.1 = hornerValue A (a 2).fst.1 cs := by
  have hrel := realize_quotientWordName_relation (Function.update a 4 g) cs (.gen 4) (by decide)
  have hsem := realize_quotientWordName Y ε (0 : Fin 9) 1 2 6 7 (by decide)
    (by decide) (by decide) y₀ y₁ hy₀ A hA cs (.gen 4) (by decide)
    (Function.update a 4 g) (by simpa using ha₀) (by simpa using ha₁)
  have hcon := quotientRelation_congr (a := Function.update a 4 g) (b := a)
    (by intro i hi; fin_cases i <;> simp_all) cs g
  simpa [GroupWord.eval, hcon] using hrel.symm.trans hsem

end Reference

section Opponent

variable {F X Z H : Type*} [Field F] [NeZero (2 : F)]
  [AddCommGroup X] [Module F X] [AddCommGroup Z] [Module F Z]
  [Group H] [Finite H]
  {Y : Submodule F (X →ₗ[F] Z)} {ε : AlternatingBilinearMap F X Z}
  [Finite (TensorGroup (evaluationTwist Y ε))] {n : ℕ}

/-- Reference anchors and exact Horner codes, together with their actual
retained mates in an arbitrary opponent. No coordinates on the opponent are
part of these data. -/
structure QuotientNamingContext (Y : Submodule F (X →ₗ[F] Z))
    (ε : AlternatingBilinearMap F X Z) (H : Type*) [Group H] (n : ℕ) where
  slot : Fin 9 → Fin n
  slot_injective : Function.Injective slot
  reference : Fin n → TensorGroup (evaluationTwist Y ε)
  opponent : Fin n → H
  position : Position (n + 1) (TensorGroup (evaluationTwist Y ε)) H
  winning : Winning position
  anchors : ∀ i ∈ ({0, 1, 2} : Finset (Fin 9)),
    position (slot i).castSucc = some (reference (slot i), opponent (slot i))
  y₀ : Y
  y₁ : Y
  injective_y₀ : Function.Injective (y₀ : X →ₗ[F] Z)
  shift : X →ₗ[F] X
  shift_relation : ∀ x, (y₁ : X →ₗ[F] Z) x = (y₀ : X →ₗ[F] Z) (shift x)
  anchor_zero : (reference (slot 0)).fst = (0, y₀)
  anchor_one : (reference (slot 1)).fst = (0, y₁)
  code : X → List ℕ
  code_exact : ∀ x, hornerValue shift (reference (slot 2)).fst.1 (code x) = x

namespace QuotientNamingContext

variable (C : QuotientNamingContext Y ε H n)

def Named (x : X) (h : H) : Prop := quotientRelation (C.opponent ∘ C.slot) (C.code x) h

theorem word_transfer
    {pos : Position (n + 1) (TensorGroup (evaluationTwist Y ε)) H} (hp : Winning pos)
    (a : Fin n → TensorGroup (evaluationTwist Y ε)) (b : Fin n → H)
    (ha : ∀ i ∈ ({0, 1, 2} : Finset (Fin 9)), a (C.slot i) = C.reference (C.slot i))
    (hb : ∀ i ∈ ({0, 1, 2} : Finset (Fin 9)), b (C.slot i) = C.opponent (C.slot i))
    (w : GroupWord 9) (hw : 6 ∉ wordVariables w)
    (ht : ∀ i ∈ ({0, 1, 2} : Finset (Fin 9)) ∪ wordVariables w,
      pos (C.slot i).castSucc = some (a (C.slot i), b (C.slot i))) (x : X) :
    C.Named x (w.eval (b ∘ C.slot)) ↔ (w.eval (a ∘ C.slot)).fst.1 = x := by
  have htr := realize_iff_of_winning_embedding C.slot C.slot_injective
    (quotientWordName 0 1 2 6 7 (C.code x) w) hp a b (by
      intro i hi
      exact ht i (quotientWordName_free (0 : Fin 9) 1 2 6 7 (C.code x) w hi))
  rw [realize_quotientWordName_relation _ _ _ hw,
    realize_quotientWordName_relation _ _ _ hw] at htr
  have hcon := quotientRelation_congr (a := b ∘ C.slot) (b := C.opponent ∘ C.slot)
    hb (C.code x) (w.eval (b ∘ C.slot))
  have href := quotientRelation_reference Y ε C.y₀ C.y₁ C.injective_y₀ C.shift
    C.shift_relation (a ∘ C.slot)
    (by simpa only [Function.comp_apply, ha 0 (by decide)] using C.anchor_zero)
    (by simpa only [Function.comp_apply, ha 1 (by decide)] using C.anchor_one)
    (C.code x) (w.eval (a ∘ C.slot))
  rw [Function.comp_apply, ha 2 (by decide), C.code_exact] at href
  exact hcon.symm.trans (htr.symm.trans href)

noncomputable def response : TensorGroup (evaluationTwist Y ε) ≃ H :=
  Classical.choose (winning_step C.winning (C.slot 4).castSucc).2

omit [NeZero (2 : F)] [Finite H] [Finite (TensorGroup (evaluationTwist Y ε))] in
theorem response_winning (g : TensorGroup (evaluationTwist Y ε)) :
    Winning (place C.position (C.slot 4).castSucc g (C.response g)) :=
  Classical.choose_spec (winning_step C.winning (C.slot 4).castSucc).2 g

/-- The quotient label is obtained from a genuine response bijection. -/
noncomputable def quotient (h : H) : X := (C.response.symm h).fst.1

omit [NeZero (2 : F)] [Finite H] [Finite (TensorGroup (evaluationTwist Y ε))] in
theorem slot_ne {i j : Fin 9} (h : i ≠ j) : C.slot i ≠ C.slot j :=
  fun he => h (C.slot_injective he)

theorem slot_cast_ne {i j : Fin 9} (h : i ≠ j) :
    (C.slot i).castSucc ≠ (C.slot j).castSucc := by
  intro he
  exact C.slot_ne h (Fin.ext (congrArg (fun x : Fin (n + 1) => x.val) he))

theorem update_anchor {K : Type*} (a : Fin n → K) (q : Fin 9)
    (hq : q ∉ ({0, 1, 2} : Finset (Fin 9))) (v : K)
    (i : Fin 9) (hi : i ∈ ({0, 1, 2} : Finset (Fin 9))) :
    Function.update a (C.slot q) v (C.slot i) = a (C.slot i) := by
  have hiq : i ≠ q := fun he => hq (he ▸ hi)
  exact Function.update_of_ne (C.slot_ne hiq) _ _

theorem named_iff (x : X) (h : H) : C.Named x h ↔ C.quotient h = x := by
  let g := C.response.symm h
  have hp : Winning (place C.position (C.slot 4).castSucc g h) := by
    simpa [g] using C.response_winning g
  have htr := C.word_transfer hp
    (Function.update C.reference (C.slot 4) g) (Function.update C.opponent (C.slot 4) h)
    (C.update_anchor C.reference 4 (by decide) g)
    (C.update_anchor C.opponent 4 (by decide) h)
    (.gen 4) (by decide) (by
      intro i hi
      simp only [wordVariables, Finset.mem_union, Finset.mem_singleton] at hi
      rcases hi with hi | rfl
      · rw [place_ne _ _ _ _ _ (C.slot_cast_ne (fun he => by
          have hi4 : (4 : Fin 9) ∈ ({0, 1, 2} : Finset (Fin 9)) := he ▸ hi
          contradiction))]
        rw [C.update_anchor C.reference 4 (by decide) g i hi,
          C.update_anchor C.opponent 4 (by decide) h i hi]
        exact C.anchors i hi
      · simp) x
  simpa [GroupWord.eval, quotient, g] using htr

omit [NeZero (2 : F)] [Finite H] [Finite (TensorGroup (evaluationTwist Y ε))] in
theorem quotient_surjective : Function.Surjective C.quotient := by
  intro x
  refine ⟨C.response ⟨(x, 0), 0⟩, ?_⟩
  simp [quotient]

theorem quotient_word
    {pos : Position (n + 1) (TensorGroup (evaluationTwist Y ε)) H} (hp : Winning pos)
    (a : Fin n → TensorGroup (evaluationTwist Y ε)) (b : Fin n → H)
    (ha : ∀ i ∈ ({0, 1, 2} : Finset (Fin 9)), a (C.slot i) = C.reference (C.slot i))
    (hb : ∀ i ∈ ({0, 1, 2} : Finset (Fin 9)), b (C.slot i) = C.opponent (C.slot i))
    (w : GroupWord 9) (hw : 6 ∉ wordVariables w)
    (ht : ∀ i ∈ ({0, 1, 2} : Finset (Fin 9)) ∪ wordVariables w,
      pos (C.slot i).castSucc = some (a (C.slot i), b (C.slot i))) :
    C.quotient (w.eval (b ∘ C.slot)) = (w.eval (a ∘ C.slot)).fst.1 := by
  exact (C.named_iff _ _).mp ((C.word_transfer hp a b ha hb w hw ht _).mpr rfl)

/-- Additivity follows by retaining two opponent elements simultaneously and
testing their product with the concrete quotient-word formula. -/
theorem quotient_mul (h h' : H) : C.quotient (h * h') = C.quotient h + C.quotient h' := by
  let g := C.response.symm h
  have hp₁ : Winning (place C.position (C.slot 4).castSucc g h) := by
    simpa [g] using C.response_winning g
  obtain ⟨f, hf⟩ := (winning_step hp₁ (C.slot 5).castSucc).2
  let g' := f.symm h'
  let pos := place (place C.position (C.slot 4).castSucc g h) (C.slot 5).castSucc g' h'
  have hp : Winning pos := by simpa [pos, g'] using hf g'
  let a := Function.update (Function.update C.reference (C.slot 4) g) (C.slot 5) g'
  let b := Function.update (Function.update C.opponent (C.slot 4) h) (C.slot 5) h'
  have ha : ∀ i ∈ ({0, 1, 2} : Finset (Fin 9)), a (C.slot i) = C.reference (C.slot i) := by
    intro i hi
    rw [show a (C.slot i) = Function.update C.reference (C.slot 4) g (C.slot i) from
      C.update_anchor _ 5 (by decide) g' i hi]
    exact C.update_anchor _ 4 (by decide) g i hi
  have hb : ∀ i ∈ ({0, 1, 2} : Finset (Fin 9)), b (C.slot i) = C.opponent (C.slot i) := by
    intro i hi
    rw [show b (C.slot i) = Function.update C.opponent (C.slot 4) h (C.slot i) from
      C.update_anchor _ 5 (by decide) h' i hi]
    exact C.update_anchor _ 4 (by decide) h i hi
  have ht : ∀ i ∈ ({0, 1, 2} : Finset (Fin 9)) ∪ {4, 5},
      pos (C.slot i).castSucc = some (a (C.slot i), b (C.slot i)) := by
    intro i hi
    by_cases hi5 : i = 5
    · subst i
      simp [pos, a, b]
    by_cases hi4 : i = 4
    · subst i
      simp [pos, a, b, place_ne, C.slot_cast_ne (by decide : (4 : Fin 9) ≠ 5),
        C.slot_ne (by decide : (4 : Fin 9) ≠ 5)]
    have hiA : i ∈ ({0, 1, 2} : Finset (Fin 9)) := by simpa [hi4, hi5] using hi
    rw [show pos (C.slot i).castSucc = C.position (C.slot i).castSucc by
      dsimp [pos]
      rw [place_ne _ _ _ _ _ (C.slot_cast_ne hi5),
        place_ne _ _ _ _ _ (C.slot_cast_ne hi4)], ha i hiA, hb i hiA]
    exact C.anchors i hiA
  have hq₁ := C.quotient_word hp a b ha hb (.gen 4) (by decide) (by
    intro i hi
    apply ht i
    simpa only [wordVariables] using Finset.mem_union.mpr
      (Finset.mem_union.mp hi |>.imp id (fun h => Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp h)))))
  have hq₂ := C.quotient_word hp a b ha hb (.gen 5) (by decide) (by
    intro i hi
    apply ht i
    simpa only [wordVariables] using Finset.mem_union.mpr
      (Finset.mem_union.mp hi |>.imp id (fun h => Finset.mem_insert.mpr (Or.inr h))))
  have hqm := C.quotient_word hp a b ha hb (.mul (.gen 4) (.gen 5)) (by decide) (by
    intro i hi
    apply ht i
    simpa only [wordVariables, Finset.singleton_union] using hi)
  have h45 := C.slot_ne (by decide : (4 : Fin 9) ≠ 5)
  simp only [GroupWord.eval, Function.comp_apply, a, b, Function.update_self,
    Function.update_of_ne h45, TensorGroup.mul_fst, Prod.fst_add] at hq₁ hq₂ hqm
  exact hqm.trans (congrArg₂ (· + ·) hq₁.symm hq₂.symm)

@[simp] theorem quotient_one : C.quotient 1 = 0 := by
  have h := (C.quotient_mul 1 1).symm
  simpa using (add_left_cancel (show C.quotient 1 + C.quotient 1 = C.quotient 1 + 0 by
    simpa using h))

@[simp] theorem quotient_inv (h : H) : C.quotient h⁻¹ = -C.quotient h := by
  have he := C.quotient_mul h h⁻¹
  rw [mul_inv_cancel, C.quotient_one] at he
  exact (eq_neg_of_add_eq_zero_right he.symm)

theorem quotient_pow (h : H) (k : ℕ) : C.quotient (h ^ k) = k • C.quotient h := by
  induction k with
  | zero => simp
  | succ k ih => simp [pow_succ, C.quotient_mul, ih, add_nsmul]

theorem quotient_commutator (g h : H) : C.quotient (g * h * g⁻¹ * h⁻¹) = 0 := by
  simp [C.quotient_mul]

theorem quotient_center {h : H} (hh : h ∈ Subgroup.center H) : C.quotient h = 0 := by
  let g := C.response.symm h
  have hp : Winning (place C.position (C.slot 4).castSucc g h) := by
    simpa [g] using C.response_winning g
  have hcentral := (centrality_transfer hp (C.slot 4) (C.slot 5)
    (C.slot_ne (by decide)) (by simp :
      (place C.position (C.slot 4).castSucc g h) (C.slot 4).castSucc = some (g, h))).mpr
    (fun x => (Subgroup.mem_center_iff.mp hh x).symm)
  exact (commutes_anchor_iff Y ε g (C.reference (C.slot 0)) C.y₀
    C.anchor_zero C.injective_y₀).mp (hcentral _)

theorem response_symm_winning (h : H) :
    Winning (place C.position (C.slot 4).castSucc (C.response.symm h) h) := by
  simpa using C.response_winning (C.response.symm h)

noncomputable def secondResponse (h : H) : TensorGroup (evaluationTwist Y ε) ≃ H :=
  Classical.choose (winning_step (C.response_symm_winning h) (C.slot 5).castSucc).2

noncomputable def pairPosition (h h' : H) :
    Position (n + 1) (TensorGroup (evaluationTwist Y ε)) H :=
  place (place C.position (C.slot 4).castSucc (C.response.symm h) h)
    (C.slot 5).castSucc ((C.secondResponse h).symm h') h'

theorem pair_winning (h h' : H) : Winning (C.pairPosition h h') := by
  have hw := Classical.choose_spec
    (winning_step (C.response_symm_winning h) (C.slot 5).castSucc).2
    ((C.secondResponse h).symm h')
  simpa only [secondResponse, Equiv.apply_symm_apply] using hw

noncomputable def pairReference (h h' : H) : Fin n → TensorGroup (evaluationTwist Y ε) :=
  Function.update (Function.update C.reference (C.slot 4) (C.response.symm h))
    (C.slot 5) ((C.secondResponse h).symm h')

def pairOpponent (h h' : H) : Fin n → H :=
  Function.update (Function.update C.opponent (C.slot 4) h) (C.slot 5) h'

theorem pair_reference_anchor (h h' : H) (i : Fin 9)
    (hi : i ∈ ({0, 1, 2, 3} : Finset (Fin 9))) :
    C.pairReference h h' (C.slot i) = C.reference (C.slot i) := by
  have hi4 : i ≠ 4 := by intro he; subst i; simp at hi
  have hi5 : i ≠ 5 := by intro he; subst i; simp at hi
  simp [pairReference, C.slot_ne hi4, C.slot_ne hi5]

theorem pair_opponent_anchor (h h' : H) (i : Fin 9)
    (hi : i ∈ ({0, 1, 2, 3} : Finset (Fin 9))) :
    C.pairOpponent h h' (C.slot i) = C.opponent (C.slot i) := by
  have hi4 : i ≠ 4 := by intro he; subst i; simp at hi
  have hi5 : i ≠ 5 := by intro he; subst i; simp at hi
  simp [pairOpponent, C.slot_ne hi4, C.slot_ne hi5]

theorem pair_tracks
    (h₃ : C.position (C.slot 3).castSucc =
      some (C.reference (C.slot 3), C.opponent (C.slot 3))) (h h' : H)
    (i : Fin 9) (hi : i ∈ ({0, 1, 2, 3} : Finset (Fin 9)) ∪ {4, 5}) :
    C.pairPosition h h' (C.slot i).castSucc =
      some (C.pairReference h h' (C.slot i), C.pairOpponent h h' (C.slot i)) := by
  by_cases hi5 : i = 5
  · subst i
    simp [pairPosition, pairReference, pairOpponent]
  by_cases hi4 : i = 4
  · subst i
    simp [pairPosition, pairReference, pairOpponent,
      C.slot_cast_ne (by decide : (4 : Fin 9) ≠ 5), C.slot_ne (by decide : (4 : Fin 9) ≠ 5)]
  have hiA : i ∈ ({0, 1, 2, 3} : Finset (Fin 9)) := by simpa [hi4, hi5] using hi
  rw [pair_reference_anchor C h h' i hiA, pair_opponent_anchor C h h' i hiA]
  change (place (place C.position (C.slot 4).castSucc (C.response.symm h) h)
    (C.slot 5).castSucc ((C.secondResponse h).symm h') h') (C.slot i).castSucc = _
  rw [place_ne _ _ _ _ _ (C.slot_cast_ne hi5), place_ne _ _ _ _ _ (C.slot_cast_ne hi4)]
  by_cases hi3 : i = 3
  · subst i
    exact h₃
  · apply C.anchors
    simp only [Finset.mem_insert, Finset.mem_singleton] at hiA ⊢
    tauto

@[simp] theorem pairReference_four (h h' : H) :
    C.pairReference h h' (C.slot 4) = C.response.symm h := by
  simp [pairReference, C.slot_ne (by decide : (4 : Fin 9) ≠ 5)]

@[simp] theorem pairReference_five (h h' : H) :
    C.pairReference h h' (C.slot 5) = (C.secondResponse h).symm h' := by simp [pairReference]

@[simp] theorem pairOpponent_four (h h' : H) :
    C.pairOpponent h h' (C.slot 4) = h := by
  simp [pairOpponent, C.slot_ne (by decide : (4 : Fin 9) ≠ 5)]

omit [NeZero (2 : F)] [Finite H] [Finite (TensorGroup (evaluationTwist Y ε))] in
@[simp] theorem pairOpponent_five (h h' : H) :
    C.pairOpponent h h' (C.slot 5) = h' := by simp [pairOpponent]

end QuotientNamingContext

end Opponent

section PrimeField

variable {p n : ℕ} [Fact p.Prime] [NeZero (2 : ZMod p)]
  {X Z H : Type*} [AddCommGroup X] [Module (ZMod p) X]
  [AddCommGroup Z] [Module (ZMod p) Z] [Group H] [Finite H]
  {Y : Submodule (ZMod p) (X →ₗ[ZMod p] Z)}
  {ε : AlternatingBilinearMap (ZMod p) X Z}
  [Finite (TensorGroup (evaluationTwist Y ε))]

namespace QuotientNamingContext

variable (C : QuotientNamingContext Y ε H n) (D : Baer.Data p H)

/-- The transferred quotient label is linear for the recovered Baer structure. -/
noncomputable def quotientLinear : Baer.Data.Vector D →ₗ[ZMod p] X :=
  AddMonoidHom.toZModLinearMap p
    { toFun a := C.quotient a.val
      map_zero' := C.quotient_one
      map_add' a b := by
        change C.quotient (D.sum a.val b.val) = C.quotient a.val + C.quotient b.val
        simp [Baer.Data.sum, Baer.Data.correction, C.quotient_mul, C.quotient_pow,
          commutatorElement_def] }

@[simp] theorem quotientLinear_apply (a : Baer.Data.Vector D) :
    C.quotientLinear D a = C.quotient a.val := rfl

theorem quotientLinear_surjective : Function.Surjective (C.quotientLinear D) := by
  intro x
  obtain ⟨h, hh⟩ := C.quotient_surjective x
  exact ⟨⟨h⟩, hh⟩

/-- Matrix labels are read from the same actual response bijection as the
quotient labels; membership in `Y` is automatic. Their linearity and
evaluation law are proved from central coordinate names below. -/
noncomputable def operatorRaw (m : LinearMap.ker (C.quotientLinear D)) : Y :=
  (C.response.symm m.val.val).fst.2

theorem operatorRaw_preimage (m : LinearMap.ker (C.quotientLinear D)) :
    (C.response.symm m.val.val).fst = (0, C.operatorRaw D m) :=
  Prod.ext m.property rfl

theorem operatorRaw_surjective : Function.Surjective (C.operatorRaw D) := by
  intro y
  let g : TensorGroup (evaluationTwist Y ε) := ⟨(0, y), 0⟩
  let a : Baer.Data.Vector D := ⟨C.response g⟩
  have ha : a ∈ LinearMap.ker (C.quotientLinear D) := by
    change (C.response.symm (C.response g)).fst.1 = 0
    simp [g]
  exact ⟨⟨a, ha⟩, by simp [operatorRaw, a, g]⟩

theorem quotientLinear_center (a : Baer.Data.Vector D) (ha : a ∈ D.centerSubmodule) :
    C.quotientLinear D a = 0 := C.quotient_center ha

/-- Exponent and nilpotency identities of the arbitrary opponent are proved
from the winning position, before its Baer vector structure is used. -/
def baerData (hodd : Odd p) : Baer.Data p H where
  odd := hodd
  exponent := (exponent_transfer C.winning (C.slot 0) p).mp
    (TensorGroup.pow_char_eq_one p)
  central := by
    have hc : ∀ g h x : TensorGroup (evaluationTwist Y ε),
        (g * h * g⁻¹ * h⁻¹) * x = x * (g * h * g⁻¹ * h⁻¹) := by
      intro g h x
      rw [TensorGroup.commutator_eq]
      apply (TensorGroup.mul_comm_iff _ _).mpr
      simp
    have htr := (classTwo_transfer C.winning (C.slot 0) (C.slot 1) (C.slot 2)
      (C.slot_ne (by decide)) (C.slot_ne (by decide)) (C.slot_ne (by decide))).mp hc
    intro a b c
    exact htr a b c

theorem quotient_eq_zero_iff_centralizer
    [FiniteDimensional (ZMod p) X] [FiniteDimensional (ZMod p) Z]
    (heval : ∀ x : X, x ≠ 0 →
      Function.Surjective (fun y : Y => (y : X →ₗ[ZMod p] Z) x))
    (hdim : Module.finrank (ZMod p) X < Module.finrank (ZMod p) Z) (h : H) :
    C.quotient h = 0 ↔
      p ^ (Module.finrank (ZMod p) X + Module.finrank (ZMod p) Y) <
        Nat.card {k : H // h * k = k * h} := by
  let g := C.response.symm h
  have hp : Winning (place C.position (C.slot 4).castSucc g h) := by
    simpa [g] using C.response_winning g
  have hcard := centralizer_card_transfer hp (C.slot 4) (C.slot 5)
    (C.slot_ne (by decide)) (by simp :
      (place C.position (C.slot 4).castSucc g h) (C.slot 4).castSucc = some (g, h))
  change g.fst.1 = 0 ↔ _
  rw [matrixSector_iff_centralizer_card_gt Y ε heval hdim, hcard]

theorem quotientLinear_kernel
    [FiniteDimensional (ZMod p) X] [FiniteDimensional (ZMod p) Z]
    (heval : ∀ x : X, x ≠ 0 →
      Function.Surjective (fun y : Y => (y : X →ₗ[ZMod p] Z) x))
    (hdim : Module.finrank (ZMod p) X < Module.finrank (ZMod p) Z)
    (B : Subgroup H) (hB : ∀ h : H, h ∈ B ↔
      p ^ (Module.finrank (ZMod p) X + Module.finrank (ZMod p) Y) <
        Nat.card {k : H // h * k = k * h}) :
    LinearMap.ker (C.quotientLinear D) = D.subgroupSubmodule B := by
  ext a
  change C.quotient a.val = 0 ↔ a.val ∈ B
  exact (C.quotient_eq_zero_iff_centralizer heval hdim a.val).trans (hB a.val).symm

end QuotientNamingContext

end PrimeField

end GroupWL.CoordinateNames
