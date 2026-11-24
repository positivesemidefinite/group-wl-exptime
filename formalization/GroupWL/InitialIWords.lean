import GroupWL.RefinementGame

/-! # Group words in the multiplication language

Two reusable variable names suffice to evaluate a signed word while all
input names stay fixed. This supplies the concrete Version-I to Version-II
comparison; no comparison theorem is assumed.
-/

namespace GroupWL.InitialIWords

open Refinement PebbleGame

universe u v w

/-- Stable color equality for arbitrary initial colors. -/
def Stable {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    {C : Type w} {d : ℕ} (initialA : (Fin d → A) → C) (initialB : (Fin d → B) → C)
    (a : Fin d → A) (b : Fin d → B) : Prop :=
  ∀ r, color initialA r a = color initialB r b

theorem color_lower {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    {C : Type w} {d : ℕ} {initialA : (Fin d → A) → C} {initialB : (Fin d → B) → C}
    {a : Fin d → A} {b : Fin d → B} {r s : ℕ} (hrs : r ≤ s)
    (h : color initialA s a = color initialB s b) : color initialA r a = color initialB r b := by
  induction s generalizing r with
  | zero =>
      have hr : r = 0 := by omega
      subst r
      exact h
  | succ s ih =>
      by_cases h' : r ≤ s
      · exact ih h' (congrArg Prod.fst h)
      · have hr : r = s+1 := by omega
        subst r
        exact h

private theorem univ_match {A : Type u} {B : Type v} {C : Type w}
    [Fintype A] [Fintype B] (f : A → C) (g : B → C)
    (h : Finset.univ.val.map f = Finset.univ.val.map g) :
    ∃ e : A ≃ B, ∀ a, f a = g (e a) := by
  classical
  have hc (c : C) : Fintype.card {a : A // f a = c} = Fintype.card {b : B // g b = c} := by
    have he := congrArg (Multiset.count c) h
    simp only [Multiset.count_map, ← Finset.filter_val, eq_comm (a := c)] at he
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact he
  let es (c : C) : {a : A // f a = c} ≃ {b : B // g b = c} := Fintype.equivOfCardEq (hc c)
  exact ⟨Equiv.ofFiberEquiv es,fun a => (Equiv.ofFiberEquiv_map es a).symm⟩

/-- One bijection works for all coordinates and all further rounds. -/
theorem Stable.matching {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    {C : Type w} {d : ℕ} {initialA : (Fin d → A) → C} {initialB : (Fin d → B) → C}
    {a : Fin d → A} {b : Fin d → B} (h : Stable initialA initialB a b) :
    ∃ f : A ≃ B, ∀ x i, Stable initialA initialB (Function.update a i x) (Function.update b i (f x)) := by
  classical
  have at_round (r : ℕ) : ∃ f : A ≃ B, ∀ x i,
      color initialA r (Function.update a i x) = color initialB r (Function.update b i (f x)) := by
    obtain ⟨f,hf⟩ := univ_match _ _ (congrArg Prod.snd (h (r+1)))
    exact ⟨f,fun x i => congrFun (hf x) i⟩
  by_contra hn
  have hbad : ∀ f : A ≃ B, ∃ r : ℕ, ¬ ∀ x i,
      color initialA r (Function.update a i x) = color initialB r (Function.update b i (f x)) := by
    intro f
    by_contra hgood
    push Not at hgood
    exact hn ⟨f,fun x i r => hgood r x i⟩
  choose r hr using hbad
  let R : ℕ := Finset.univ.sup r
  obtain ⟨f,hf⟩ := at_round R
  apply hr f
  intro x i
  exact color_lower (Finset.le_sup (Finset.mem_univ f)) (hf x i)

inductive Formula (d : ℕ) where
  | mul : Fin d → Fin d → Fin d → Formula d
  | and : Formula d → Formula d → Formula d
  | ex : Fin d → Formula d → Formula d

variable {G : Type u} {H : Type v} [Group G] [Group H] {d k : ℕ}

def Formula.Realize (a : Fin d → G) : Formula d → Prop
  | .mul i j l => a i * a j = a l
  | .and φ ψ => φ.Realize a ∧ ψ.Realize a
  | .ex i φ => ∃ x, φ.Realize (Function.update a i x)

def SameI [Fintype G] [Fintype H] (a : Fin d → G) (b : Fin d → H) : Prop :=
  Stable (initialI d) (initialI d) a b

/-- The multiplication-language semantics is preserved by actual Version-I colors. -/
theorem realize_iff [Fintype G] [Fintype H] (φ : Formula d)
    {a : Fin d → G} {b : Fin d → H} (h : SameI a b) : φ.Realize a ↔ φ.Realize b := by
  classical
  induction φ generalizing a b with
  | mul i j l =>
      have he := congrFun (congrFun (congrFun (congrArg Prod.snd (h 0)) i) j) l
      exact decide_eq_decide.mp he
  | and φ ψ ihφ ihψ => exact and_congr (ihφ h) (ihψ h)
  | ex i φ ih =>
      obtain ⟨f,hf⟩ := Stable.matching h
      constructor
      · rintro ⟨x,hx⟩
        exact ⟨f x,(ih (hf x i)).mp hx⟩
      · rintro ⟨y,hy⟩
        refine ⟨f.symm y,?_⟩
        apply (ih (hf (f.symm y) i)).mpr
        simpa using hy

abbrev Letter (k : ℕ) := Fin k × Bool

def letterEval (a : Fin k → G) (l : Letter k) : G := if l.2 then (a l.1)⁻¹ else a l.1

def listEval (a : Fin k → G) (L : List (Letter k)) : G := (L.map (letterEval a)).prod

def flip (l : Letter k) : Letter k := (l.1,!l.2)

@[simp] theorem letterEval_flip (a : Fin k → G) (l : Letter k) :
    letterEval a (flip l) = (letterEval a l)⁻¹ := by
  rcases l with ⟨i,b⟩
  cases b <;> simp [letterEval,flip]

@[simp] theorem listEval_nil (a : Fin k → G) : listEval a [] = 1 := rfl
@[simp] theorem listEval_cons (a : Fin k → G) (l : Letter k) (L : List (Letter k)) :
    listEval a (l::L) = letterEval a l * listEval a L := rfl

theorem listEval_append (a : Fin k → G) (L M : List (Letter k)) :
    listEval a (L++M) = listEval a L * listEval a M := by simp [listEval]

theorem listEval_inverse (a : Fin k → G) (L : List (Letter k)) :
    listEval a (L.reverse.map flip) = (listEval a L)⁻¹ := by
  induction L with
  | nil => simp [listEval]
  | cons l L ih =>
      simp only [List.reverse_cons,List.map_append,List.map_cons,List.map_nil,
        listEval_append,listEval_cons,listEval_nil,mul_one,letterEval_flip,ih,mul_inv_rev]

def linearize : GroupWord k → List (Letter k)
  | .one => []
  | .gen i => [(i,false)]
  | .mul s t => linearize s ++ linearize t
  | .inv s => (linearize s).reverse.map flip

theorem linearize_eval (a : Fin k → G) (w : GroupWord k) : listEval a (linearize w) = w.eval a := by
  induction w with
  | one => rfl
  | gen i => simp [linearize,letterEval,GroupWord.eval]
  | mul s t hs ht => simp [linearize,listEval_append,hs,ht,GroupWord.eval]
  | inv s hs =>
      change listEval a ((linearize s).reverse.map flip) = (s.eval a)⁻¹
      rw [listEval_inverse,hs]

/-- `out` and `helper` alternate under nesting, so word length never creates
additional variable names. -/
def evaluationFormula (input : Fin k → Fin d) : List (Letter k) → Fin d → Fin d → Formula d
  | [],out,_ => .mul out out out
  | (i,negative)::L,out,helper =>
      .ex helper (.and (if negative then .mul (input i) out helper else .mul (input i) helper out)
        (evaluationFormula input L helper out))

private theorem input_update (input : Fin k → Fin d) (a : Fin d → G) (h : Fin d) (x : G)
    (hn : ∀ i,input i ≠ h) : (Function.update a h x) ∘ input = a ∘ input := by
  funext i
  exact Function.update_of_ne (hn i) x a

/-- Exact semantics of the two-helper-variable word evaluator. -/
theorem evaluationFormula_correct (input : Fin k → Fin d) (L : List (Letter k))
    (out helper : Fin d) (hneq : out ≠ helper)
    (hout : ∀ i,input i ≠ out) (hhelper : ∀ i,input i ≠ helper) (a : Fin d → G) :
    (evaluationFormula input L out helper).Realize a ↔ a out = listEval (a ∘ input) L := by
  induction L generalizing out helper a with
  | nil =>
      change a out * a out = a out ↔ a out = 1
      constructor
      · intro h
        apply mul_left_cancel (a := a out)
        simpa using h
      · rintro h
        simp [h]
  | cons l L ih =>
      rcases l with ⟨i,b⟩
      cases b <;>
        simp only [evaluationFormula,Formula.Realize,Bool.false_eq_true,if_false,if_true]
      · constructor
        · rintro ⟨x,hm,hr⟩
          have hv := (ih helper out hneq.symm hhelper hout (Function.update a helper x)).mp hr
          rw [input_update input a helper x hhelper] at hv
          simp only [Function.update_self] at hv
          have hout' : Function.update a helper x out = a out := Function.update_of_ne hneq x a
          have hi' : Function.update a helper x (input i) = a (input i) := Function.update_of_ne (hhelper i) x a
          rw [hout',hi',Function.update_self,hv] at hm
          simpa [listEval_cons,letterEval] using hm.symm
        · intro hv
          refine ⟨listEval (a ∘ input) L,?_,?_⟩
          · simp only [Function.update_of_ne hneq,Function.update_of_ne (hhelper i),Function.update_self]
            simpa [listEval_cons,letterEval] using hv.symm
          · apply (ih helper out hneq.symm hhelper hout _).mpr
            rw [input_update input a helper _ hhelper]
            simp
      · constructor
        · rintro ⟨x,hm,hr⟩
          have hv := (ih helper out hneq.symm hhelper hout (Function.update a helper x)).mp hr
          rw [input_update input a helper x hhelper] at hv
          simp only [Function.update_self] at hv
          have hout' : Function.update a helper x out = a out := Function.update_of_ne hneq x a
          have hi' : Function.update a helper x (input i) = a (input i) := Function.update_of_ne (hhelper i) x a
          rw [hout',hi',Function.update_self,hv] at hm
          simpa [listEval_cons,letterEval] using (eq_inv_mul_iff_mul_eq.mpr hm)
        · intro hv
          refine ⟨listEval (a ∘ input) L,?_,?_⟩
          · simp only [Function.update_of_ne hneq,Function.update_of_ne (hhelper i),Function.update_self]
            exact eq_inv_mul_iff_mul_eq.mp (by simpa [listEval_cons,letterEval] using hv)
          · apply (ih helper out hneq.symm hhelper hout _).mpr
            rw [input_update input a helper _ hhelper]
            simp

/-- A closed output test expresses any word relation using the same two helpers. -/
def wordFormula (input : Fin k → Fin d) (out helper : Fin d) (w : GroupWord k) : Formula d :=
  .ex out (.and (.mul out out out) (evaluationFormula input (linearize w) out helper))

theorem wordFormula_correct (input : Fin k → Fin d) (out helper : Fin d)
    (hneq : out ≠ helper) (hout : ∀ i,input i ≠ out) (hhelper : ∀ i,input i ≠ helper)
    (w : GroupWord k) (a : Fin d → G) :
    (wordFormula input out helper w).Realize a ↔ w.eval (a ∘ input) = 1 := by
  change (∃ x, _ ∧ _) ↔ _
  constructor
  · rintro ⟨x,hx,hword⟩
    have hx1 : x = 1 := by
      simp only [Formula.Realize,Function.update_self] at hx
      apply mul_left_cancel (a := x)
      simpa using hx
    have hw := (evaluationFormula_correct input (linearize w) out helper hneq hout hhelper
      (Function.update a out x)).mp hword
    rw [input_update input a out x hout,linearize_eval] at hw
    simpa [hx1] using hw.symm
  · intro hw
    refine ⟨1,by simp [Formula.Realize],?_⟩
    apply (evaluationFormula_correct input (linearize w) out helper hneq hout hhelper _).mpr
    rw [input_update input a out 1 hout,linearize_eval,hw]
    simp

/-- Stable Version-I colors force the complete word type of every marked
subtuple with two available helper slots. -/
theorem initialII_eq_of_sameI [Fintype G] [Fintype H]
    {a : Fin d → G} {b : Fin d → H} (h : SameI a b)
    (input : Fin k → Fin d) (out helper : Fin d)
    (hneq : out ≠ helper) (hout : ∀ i,input i ≠ out) (hhelper : ∀ i,input i ≠ helper) :
    initialII k (a ∘ input) = initialII k (b ∘ input) := by
  classical
  funext word
  apply decide_eq_decide.mpr
  rw [← wordFormula_correct input out helper hneq hout hhelper,
    ← wordFormula_correct input out helper hneq hout hhelper]
  exact realize_iff _ h

end GroupWL.InitialIWords
