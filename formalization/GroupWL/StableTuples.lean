import GroupWL.InitialIWords

/-! # Sequential tuple bijections for stable refinement colors -/
namespace GroupWL.InitialIWords

open Refinement
universe u v w

/-- Completing distinct slots gives a triangular tuple bijection, preserving
all coordinates outside the completed slots. -/
theorem Stable.complete_tuples {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    {C : Type w} {d : ℕ} {initialA : (Fin d → A) → C} {initialB : (Fin d → B) → C}
    (n : ℕ) (slot : Fin n ↪ Fin d) {a : Fin d → A} {b : Fin d → B}
    (h : Stable initialA initialB a b) :
    ∃ e : (Fin n → A) ≃ (Fin n → B), ∀ t, ∃ a' b',
      Stable initialA initialB a' b' ∧
        (∀ i, a' (slot i) = t i ∧ b' (slot i) = e t i) ∧
        ∀ j, (∀ i, slot i ≠ j) → a' j = a j ∧ b' j = b j := by
  classical
  induction n generalizing a b with
  | zero =>
      let e : (Fin 0 → A) ≃ (Fin 0 → B) :=
        { toFun := fun _ i => Fin.elim0 i
          invFun := fun _ i => Fin.elim0 i
          left_inv := fun _ => by funext i; exact Fin.elim0 i
          right_inv := fun _ => by funext i; exact Fin.elim0 i }
      exact ⟨e,fun _ => ⟨a,b,h,fun i => Fin.elim0 i,fun _ _ => ⟨rfl,rfl⟩⟩⟩
  | succ n ih =>
      obtain ⟨f,hf⟩ := h.matching
      let tailSlot : Fin n ↪ Fin d :=
        ⟨fun i => slot i.succ,fun i j h => Fin.succ_injective n (slot.injective h)⟩
      have htail : ∀ x : A, ∃ e : (Fin n → A) ≃ (Fin n → B), ∀ t, ∃ a' b',
          Stable initialA initialB a' b' ∧
            (∀ i,a' (tailSlot i) = t i ∧ b' (tailSlot i) = e t i) ∧
            ∀ j,(∀ i,tailSlot i ≠ j) →
              a' j = Function.update a (slot 0) x j ∧
              b' j = Function.update b (slot 0) (f x) j :=
        fun x => ih tailSlot (hf x (slot 0))
      choose es hes using htail
      let e : (Fin (n+1) → A) ≃ (Fin (n+1) → B) :=
        (Fin.consEquiv (fun _ : Fin (n+1) => A)).symm.trans
          ((Equiv.prodCongrRight es).trans
            ((Equiv.prodCongr f (Equiv.refl (Fin n → B))).trans
              (Fin.consEquiv (fun _ : Fin (n+1) => B))))
      have e_zero (t : Fin (n+1) → A) : e t 0 = f (t 0) := rfl
      refine ⟨e,fun t => ?_⟩
      obtain ⟨a',b',hh,hmarks,hpreserve⟩ := hes (t 0) (Fin.tail t)
      refine ⟨a',b',hh,?_,?_⟩
      · intro i
        refine Fin.cases ?_ (fun i => ?_) i
        · have hp := hpreserve (slot 0) (fun i hi =>
            Fin.succ_ne_zero i (slot.injective hi))
          simpa only [Function.update_self,e_zero] using hp
        · exact hmarks i
      · intro j hj
        have hp := hpreserve j (fun i => hj i.succ)
        simpa only [Function.update_of_ne (hj 0).symm] using hp

/-- Finite matching candidates allow one candidate to match at every round. -/
theorem exists_stable_of_forall_exists {A : Type u} {B : Type v}
    [Fintype A] [Fintype B] {C : Type w} {d : ℕ}
    {initialA : (Fin d → A) → C} {initialB : (Fin d → B) → C}
    (a : Fin d → A) (P : (Fin d → B) → Prop)
    (h : ∀ r,∃ b,P b ∧ color initialA r a=color initialB r b) :
    ∃ b,P b ∧ Stable initialA initialB a b := by
  classical
  by_contra hn
  have hbad : ∀ b,∃ r,P b → color initialA r a ≠ color initialB r b := by
    intro b
    by_cases hb : P b
    · have hh : ¬ Stable initialA initialB a b := fun hs => hn ⟨b,hb,hs⟩
      simp only [Stable,not_forall] at hh
      obtain ⟨r,hr⟩ := hh
      exact ⟨r,fun _ => hr⟩
    · exact ⟨0,fun hpb => (hb hpb).elim⟩
  choose r hr using hbad
  let R := Finset.univ.sup r
  obtain ⟨b,hb,he⟩ := h R
  exact hr b hb (color_lower (Finset.le_sup (Finset.mem_univ b)) he)

/-- A single stable tuple match gives matching histograms, because successive
coordinate replacements enumerate all tuples bijectively. -/
theorem Stable.equivalent {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    {C : Type w} {d : ℕ} {initialA : (Fin d → A) → C} {initialB : (Fin d → B) → C}
    {a : Fin d → A} {b : Fin d → B} (h : Stable initialA initialB a b) :
    Equivalent initialA initialB := by
  classical
  obtain ⟨e,he⟩ := h.complete_tuples d (Function.Embedding.refl _)
  intro r
  have hm (t : Fin d → A) : color initialA r t = color initialB r (e t) := by
    obtain ⟨a',b',hh,hcoords,_⟩ := he t
    have ha : a'=t := funext fun i => (hcoords i).1
    have hb : b'=e t := funext fun i => (hcoords i).2
    simpa only [ha,hb] using hh r
  change Finset.univ.val.map (color initialA r) = Finset.univ.val.map (color initialB r)
  calc
    _ = Finset.univ.val.map ((color initialB r) ∘ e) := by
      congr 1
      funext t
      exact hm t
    _ = (Finset.univ.val.map e).map (color initialB r) := by rw [Multiset.map_map]
    _ = _ := by rw [Multiset.map_univ_val_equiv]

end GroupWL.InitialIWords
