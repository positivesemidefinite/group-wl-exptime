import GroupWL.QuotientNaming

/-! # Central coordinates in an arbitrary winning opponent -/
namespace GroupWL.CoordinateNames
open Refinement CountingLogic PebbleGame

theorem realize_update_unused {m : ℕ} {G : Type*} [Group G] (φ : Formula m)
    (a : Fin m → G) (i : Fin m) (hi : i ∉ φ.freeVariables) (g : G) :
    φ.Realize (Function.update a i g) ↔ φ.Realize a := by
  apply realize_congr φ
  intro j hj
  have hji : j ≠ i := fun e => hi (e ▸ hj)
  exact Function.update_of_ne hji _ _

def centralRelation {G : Type*} [Group G] (a : Fin 9 → G)
    (cs₀ cs₁ : List ℕ) (g : G) : Prop :=
  ∃ u v : G,
    (hornerName 0 1 2 6 8 cs₀).Realize (Function.update a 6 u) ∧
    (hornerName 0 1 2 7 8 cs₁).Realize (Function.update a 7 v) ∧
    g = (u * a 0 * u⁻¹ * (a 0)⁻¹) * (v * a 3 * v⁻¹ * (a 3)⁻¹)

theorem centralRelation_congr {G : Type*} [Group G] {a b : Fin 9 → G}
    (hab : ∀ i ∈ ({0, 1, 2, 3} : Finset (Fin 9)), a i = b i)
    (cs₀ cs₁ : List ℕ) (g : G) : centralRelation a cs₀ cs₁ g ↔ centralRelation b cs₀ cs₁ g := by
  have hn (j : Fin 9) (cs : List ℕ) (u : G) :
      (hornerName 0 1 2 j 8 cs).Realize (Function.update a j u) ↔
      (hornerName 0 1 2 j 8 cs).Realize (Function.update b j u) := by
    apply realize_congr (hornerName 0 1 2 j 8 cs)
      (a := Function.update a j u) (b := Function.update b j u)
    intro i hi
    by_cases hij : i = j
    · subst i
      exact (Function.update_self j u a).trans (Function.update_self j u b).symm
    · have hi' := hornerName_free (0 : Fin 9) 1 2 j 8 cs hi
      have hiA : i ∈ ({0, 1, 2, 3} : Finset (Fin 9)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi' ⊢
        tauto
      simpa [hij] using hab i hiA
  simp only [centralRelation, hn, hab 0 (by decide), hab 3 (by decide)]

theorem realize_centralName_relation {G : Type*} [Group G] [Finite G]
    (a : Fin 9 → G) (cs₀ cs₁ : List ℕ) (w : GroupWord 9)
    (hw : 6 ∉ wordVariables w ∧ 7 ∉ wordVariables w) :
    (centralName 0 1 2 3 6 7 8 cs₀ cs₁ w).Realize a ↔
      centralRelation a cs₀ cs₁ (w.eval a) := by
  have h₀ (u v : G) :
      (hornerName 0 1 2 6 8 cs₀).Realize (Function.update (Function.update a 6 u) 7 v) ↔
        (hornerName 0 1 2 6 8 cs₀).Realize (Function.update a 6 u) := by
    apply realize_update_unused
    intro h
    have h' := hornerName_free (0 : Fin 9) 1 2 6 8 cs₀ h
    exact (by decide : (7 : Fin 9) ∉ ({0, 1, 2, 6} : Finset (Fin 9))) h'
  have h₁ (u v : G) :
      (hornerName 0 1 2 7 8 cs₁).Realize (Function.update (Function.update a 6 u) 7 v) ↔
        (hornerName 0 1 2 7 8 cs₁).Realize (Function.update a 7 v) := by
    apply realize_congr (hornerName 0 1 2 7 8 cs₁)
      (a := Function.update (Function.update a 6 u) 7 v) (b := Function.update a 7 v)
    intro i hi
    have hi' := hornerName_free (0 : Fin 9) 1 2 7 8 cs₁ hi
    have hi6 : i ≠ 6 := by
      intro h
      subst i
      exact (by decide : (6 : Fin 9) ∉ ({0, 1, 2, 7} : Finset (Fin 9))) hi'
    by_cases hi7 : i = 7
    · subst i; rfl
    · rw [Function.update_of_ne hi7, Function.update_of_ne hi7, Function.update_of_ne hi6]
  have hw' (u v : G) : w.eval (Function.update (Function.update a 6 u) 7 v) = w.eval a := by
    apply word_eval_congr
    intro i hi
    have hi6 : i ≠ 6 := fun h => hw.1 (h ▸ hi)
    have hi7 : i ≠ 7 := fun h => hw.2 (h ▸ hi)
    simp [hi6, hi7]
  simp only [centralName, realize_existsVar, Formula.Realize, h₀, h₁,
    realize_equalWords, commutatorWord, GroupWord.eval, hw', Function.update_self,
    Function.update_of_ne (by decide : (0 : Fin 9) ≠ 6),
    Function.update_of_ne (by decide : (0 : Fin 9) ≠ 7),
    Function.update_of_ne (by decide : (3 : Fin 9) ≠ 6),
    Function.update_of_ne (by decide : (3 : Fin 9) ≠ 7),
    Function.update_of_ne (by decide : (6 : Fin 9) ≠ 7)]
  rfl

section Opponent

variable {F X Z H : Type*} [Field F] [NeZero (2 : F)]
  [AddCommGroup X] [Module F X] [AddCommGroup Z] [Module F Z]
  [Group H] [Finite H]
  {Y : Submodule F (X →ₗ[F] Z)} {ε : AlternatingBilinearMap F X Z}
  [Finite (TensorGroup (evaluationTwist Y ε))] {n : ℕ}

/-- Four actual retained anchors and linear decompositions of output labels. -/
structure CentralNamingContext (Y : Submodule F (X →ₗ[F] Z))
    (ε : AlternatingBilinearMap F X Z) (H : Type*) [Group H] (n : ℕ)
    extends QuotientNamingContext Y ε H n where
  yb : Y
  anchor_b : (reference (slot 3)).fst = (0, yb)
  anchor_b_tracked : position (slot 3).castSucc =
    some (reference (slot 3), opponent (slot 3))
  input₀ : Z →ₗ[F] X
  input₁ : Z →ₗ[F] X
  output_exact : ∀ z, (y₀ : X →ₗ[F] Z) (input₀ z) + (yb : X →ₗ[F] Z) (input₁ z) = z

namespace CentralNamingContext
variable (C : CentralNamingContext Y ε H n)

theorem anchors_four (i : Fin 9) (hi : i ∈ ({0, 1, 2, 3} : Finset (Fin 9))) :
    C.position (C.slot i).castSucc = some (C.reference (C.slot i), C.opponent (C.slot i)) := by
  by_cases hi3 : i = 3
  · subst i; exact C.anchor_b_tracked
  · apply C.anchors
    simpa [hi3] using hi

def Named (z : Z) (h : H) : Prop :=
  centralRelation (C.opponent ∘ C.slot) (C.code (C.input₀ z)) (C.code (C.input₁ z)) h

theorem word_transfer
    {pos : Position (n + 1) (TensorGroup (evaluationTwist Y ε)) H} (hp : Winning pos)
    (a : Fin n → TensorGroup (evaluationTwist Y ε)) (b : Fin n → H)
    (ha : ∀ i ∈ ({0, 1, 2, 3} : Finset (Fin 9)), a (C.slot i) = C.reference (C.slot i))
    (hb : ∀ i ∈ ({0, 1, 2, 3} : Finset (Fin 9)), b (C.slot i) = C.opponent (C.slot i))
    (w : GroupWord 9) (hw : 6 ∉ wordVariables w ∧ 7 ∉ wordVariables w)
    (ht : ∀ i ∈ ({0, 1, 2, 3} : Finset (Fin 9)) ∪ wordVariables w,
      pos (C.slot i).castSucc = some (a (C.slot i), b (C.slot i))) (z : Z) :
    C.Named z (w.eval (b ∘ C.slot)) ↔ w.eval (a ∘ C.slot) = ⟨0, z⟩ := by
  have htr := realize_iff_of_winning_embedding C.slot C.slot_injective
    (centralName 0 1 2 3 6 7 8 (C.code (C.input₀ z)) (C.code (C.input₁ z)) w) hp a b (by
      intro i hi
      exact ht i (centralName_free (0 : Fin 9) 1 2 3 6 7 8
        (C.code (C.input₀ z)) (C.code (C.input₁ z)) w hi))
  have hr := realize_centralName_relation (b ∘ C.slot)
    (C.code (C.input₀ z)) (C.code (C.input₁ z)) w hw
  have hcon := centralRelation_congr (a := b ∘ C.slot) (b := C.opponent ∘ C.slot)
    hb (C.code (C.input₀ z)) (C.code (C.input₁ z)) (w.eval (b ∘ C.slot))
  have href := realize_centralName Y ε (0 : Fin 9) 1 2 3 6 7 8
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    C.y₀ C.y₁ C.yb C.injective_y₀ C.shift C.shift_relation
    (C.code (C.input₀ z)) (C.code (C.input₁ z)) w hw (a ∘ C.slot)
    (by simpa only [Function.comp_apply, ha 0 (by decide)] using C.anchor_zero)
    (by simpa only [Function.comp_apply, ha 1 (by decide)] using C.anchor_one)
    (by simpa only [Function.comp_apply, ha 3 (by decide)] using C.anchor_b)
  rw [Function.comp_apply, ha 2 (by decide), C.code_exact, C.code_exact, C.output_exact] at href
  exact (htr.trans (hr.trans hcon)).symm.trans href

noncomputable def center (z : Z) : H := C.toQuotientNamingContext.response ⟨0, z⟩

theorem update_anchor {K : Type*} (a : Fin n → K) (q : Fin 9)
    (hq : q ∉ ({0, 1, 2, 3} : Finset (Fin 9))) (v : K)
    (i : Fin 9) (hi : i ∈ ({0, 1, 2, 3} : Finset (Fin 9))) :
    Function.update a (C.slot q) v (C.slot i) = a (C.slot i) := by
  have hiq : i ≠ q := fun he => hq (he ▸ hi)
  exact Function.update_of_ne (C.toQuotientNamingContext.slot_ne hiq) _ _

theorem named_iff (z : Z) (h : H) : C.Named z h ↔ h = C.center z := by
  let Q := C.toQuotientNamingContext
  let g := Q.response.symm h
  have hp : Winning (place C.position (C.slot 4).castSucc g h) := Q.response_symm_winning h
  have htr := C.word_transfer hp
    (Function.update C.reference (C.slot 4) g) (Function.update C.opponent (C.slot 4) h)
    (C.update_anchor C.reference 4 (by decide) g)
    (C.update_anchor C.opponent 4 (by decide) h)
    (.gen 4) (by decide) (by
      intro i hi
      simp only [wordVariables, Finset.mem_union, Finset.mem_singleton] at hi
      rcases hi with hi | rfl
      · have hi4 : i ≠ 4 := by
          intro he
          subst i
          exact (by decide : (4 : Fin 9) ∉ ({0, 1, 2, 3} : Finset (Fin 9))) hi
        rw [place_ne _ _ _ _ _ (Q.slot_cast_ne hi4),
          C.update_anchor C.reference 4 (by decide) g i hi,
          C.update_anchor C.opponent 4 (by decide) h i hi]
        exact C.anchors_four i hi
      · simp) z
  simpa only [GroupWord.eval, Function.comp_apply, Function.update_self,
    g, Equiv.symm_apply_eq, center] using htr

theorem center_injective : Function.Injective C.center := by
  intro z z' h
  have he := C.toQuotientNamingContext.response.injective h
  exact congrArg TensorGroup.snd he

/-- Any word avoiding the two bound naming variables has its exact central
value preserved at every continuation retaining the four anchors. -/
theorem center_word
    {pos : Position (n + 1) (TensorGroup (evaluationTwist Y ε)) H} (hp : Winning pos)
    (a : Fin n → TensorGroup (evaluationTwist Y ε)) (b : Fin n → H)
    (ha : ∀ i ∈ ({0, 1, 2, 3} : Finset (Fin 9)), a (C.slot i) = C.reference (C.slot i))
    (hb : ∀ i ∈ ({0, 1, 2, 3} : Finset (Fin 9)), b (C.slot i) = C.opponent (C.slot i))
    (w : GroupWord 9) (hw : 6 ∉ wordVariables w ∧ 7 ∉ wordVariables w)
    (ht : ∀ i ∈ ({0, 1, 2, 3} : Finset (Fin 9)) ∪ wordVariables w,
      pos (C.slot i).castSucc = some (a (C.slot i), b (C.slot i))) (z : Z) :
    w.eval (b ∘ C.slot) = C.center z ↔ w.eval (a ∘ C.slot) = ⟨0, z⟩ :=
  (C.named_iff z _).symm.trans (C.word_transfer hp a b ha hb w hw ht z)

theorem pair_center_word (h h' : H) (w : GroupWord 9)
    (hw : wordVariables w ⊆ ({4, 5} : Finset (Fin 9))) (z : Z) :
    w.eval (C.toQuotientNamingContext.pairOpponent h h' ∘ C.slot) = C.center z ↔
      w.eval (C.toQuotientNamingContext.pairReference h h' ∘ C.slot) = ⟨0, z⟩ := by
  let Q := C.toQuotientNamingContext
  apply C.center_word (Q.pair_winning h h') _ _
    (Q.pair_reference_anchor h h') (Q.pair_opponent_anchor h h')
  · constructor <;> intro hi
    · exact (by decide : (6 : Fin 9) ∉ ({4, 5} : Finset (Fin 9))) (hw hi)
    · exact (by decide : (7 : Fin 9) ∉ ({4, 5} : Finset (Fin 9))) (hw hi)
  · intro i hi
    apply Q.pair_tracks C.anchor_b_tracked h h' i
    exact Finset.mem_union.mpr ((Finset.mem_union.mp hi).imp id (fun h => hw h))

theorem center_central (z : Z) (h : H) : C.center z * h = h * C.center z := by
  let Q := C.toQuotientNamingContext
  have ht := centrality_transfer (Q.response_winning ⟨0, z⟩) (C.slot 4) (C.slot 5)
    (Q.slot_ne (by decide)) (g := ⟨0, z⟩) (h := C.center z) (by simp [center, Q])
  apply ht.mp _ h
  intro g
  exact (TensorGroup.mul_comm_iff _ _).mpr (by simp)

theorem center_range (h : H) : (∃ z, C.center z = h) ↔ ∀ k : H, h * k = k * h := by
  constructor
  · rintro ⟨z, rfl⟩
    exact C.center_central z
  · intro hh
    let Q := C.toQuotientNamingContext
    let g := Q.response.symm h
    have hgcentral : ∀ k, g * k = k * g :=
      (centrality_transfer (Q.response_symm_winning h) (C.slot 4) (C.slot 5)
        (Q.slot_ne (by decide)) (g := g) (h := h) (by simp [g, Q])).mpr hh
    have hgzero : g.fst = 0 := (evaluationGroup_center Y ε (fun x hx =>
      C.injective_y₀ (by simpa using hx C.y₀)) g).mp hgcentral
    refine ⟨g.snd, ?_⟩
    have he : (⟨0, g.snd⟩ : TensorGroup (evaluationTwist Y ε)) = g := by
      apply TensorGroup.ext
      · exact hgzero.symm
      · rfl
    change Q.response ⟨0, g.snd⟩ = h
    rw [he]
    exact Q.response.apply_symm_apply h

theorem center_add (z z' : Z) : C.center (z + z') = C.center z * C.center z' := by
  let Q := C.toQuotientNamingContext
  have h₅ : Q.pairReference (C.center z) (C.center z') (C.slot 5) =
      (⟨0, z'⟩ : TensorGroup (evaluationTwist Y ε)) := by
    have ht := C.pair_center_word (C.center z) (C.center z') (.gen 5) (by decide) z'
    exact ht.mp (by simp [GroupWord.eval])
  have h₄ : Q.pairReference (C.center z) (C.center z') (C.slot 4) =
      (⟨0, z⟩ : TensorGroup (evaluationTwist Y ε)) := by
    simp [Q, center]
  have ht := C.pair_center_word (C.center z) (C.center z') (.mul (.gen 4) (.gen 5))
    (by decide) (z + z')
  have hr : (.mul (.gen 4) (.gen 5) : GroupWord 9).eval
      (Q.pairReference (C.center z) (C.center z') ∘ C.slot) = ⟨0, z + z'⟩ := by
    simp only [GroupWord.eval, Function.comp_apply, h₄, h₅]
    apply TensorGroup.ext <;> simp
  simpa only [GroupWord.eval, Function.comp_apply, QuotientNamingContext.pairOpponent_four,
    QuotientNamingContext.pairOpponent_five] using (ht.mpr hr).symm

@[simp] theorem center_zero : C.center 0 = 1 := by
  have h := C.center_add 0 0
  simpa using (mul_left_cancel (a := C.center 0) (by simpa using h.symm :
    C.center 0 * C.center 0 = C.center 0 * 1))

end CentralNamingContext
end Opponent

section PrimeField
variable {p n : ℕ} [Fact p.Prime] [NeZero (2 : ZMod p)]
  {X Z H : Type*} [AddCommGroup X] [Module (ZMod p) X]
  [AddCommGroup Z] [Module (ZMod p) Z] [Group H] [Finite H]
  {Y : Submodule (ZMod p) (X →ₗ[ZMod p] Z)}
  {ε : AlternatingBilinearMap (ZMod p) X Z}
  [Finite (TensorGroup (evaluationTwist Y ε))]

namespace CentralNamingContext
variable (C : CentralNamingContext Y ε H n) (D : Baer.Data p H)

/-- The exact central coordinates are linear in the recovered prime-field
vector space. No linear structure on the opponent was assumed by the game. -/
noncomputable def centerLinear : Z →ₗ[ZMod p] Baer.Data.Vector D :=
  AddMonoidHom.toZModLinearMap p
    { toFun z := ⟨C.center z⟩
      map_zero' := by apply Baer.Data.Vector.ext; exact C.center_zero
      map_add' z z' := by
        apply Baer.Data.Vector.ext
        change C.center (z + z') = D.sum (C.center z) (C.center z')
        rw [D.sum_of_commute (C.center_central z (C.center z')), C.center_add] }

@[simp] theorem centerLinear_apply (z : Z) : (C.centerLinear D z).val = C.center z := rfl

theorem centerLinear_injective : Function.Injective (C.centerLinear D) := by
  intro z z' h
  exact C.center_injective (congrArg Baer.Data.Vector.val h)

theorem centerLinear_range : LinearMap.range (C.centerLinear D) = D.centerSubmodule := by
  ext a
  rw [LinearMap.mem_range, D.mem_centerSubmodule]
  constructor
  · rintro ⟨z, rfl⟩ k
    exact (C.center_central z k).symm
  · intro ha
    obtain ⟨z, hz⟩ := (C.center_range a.val).mpr (fun k => (ha k).symm)
    exact ⟨z, Baer.Data.Vector.ext hz⟩

end CentralNamingContext
end PrimeField
end GroupWL.CoordinateNames
