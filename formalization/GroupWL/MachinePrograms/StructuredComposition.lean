import GroupWL.MachinePrograms.StructuredComplexity
import GroupWL.MachinePrograms.StackLibrary

/-! Compose two finite stack programs across a bit-word output port,
preserving the exact costs of the constituent runs. -/
namespace GroupWL.MachinePrograms.Structured

def Program.relabel {K J : Type*} (f : K → J) : Program K → Program J
  | .skip => .skip
  | .push k b => .push (f k) b
  | .pop k n a b => .pop (f k) (n.relabel f) (a.relabel f) (b.relabel f)
  | .peek k n a b => .peek (f k) (n.relabel f) (a.relabel f) (b.relabel f)
  | .seq p q => .seq (p.relabel f) (q.relabel f)
  | .while k g p => .while (f k) g (p.relabel f)

private theorem relabel_select {K J : Type*} (f : K → J) (o : Option Bool) (n a b : Program K) :
    (select o n a b).relabel f = select o (n.relabel f) (a.relabel f) (b.relabel f) := by
  rcases o with _|(_|_) <;> rfl

variable {K J : Type*} [DecidableEq K] [DecidableEq J]

theorem Runs.relabel {p : Program K} {S T : Store K} {t : ℕ} (hr : Runs p S t T)
    (f : K → J) (embed : Store K → Store J)
    (get : ∀ (V : Store K) k, embed V (f k) = V k)
    (put : ∀ (V : Store K) k bs, embed (Function.update V k bs) =
      Function.update (embed V) (f k) bs) :
    Runs (p.relabel f) (embed S) t (embed T) := by
  induction hr with
  | skip => exact .skip _
  | push S k b => simpa [Program.relabel,put,get] using Runs.push (embed S) (f k) b
  | pop branch ih =>
    apply Runs.pop
    simpa only [relabel_select,put,get] using ih
  | peek branch ih =>
    apply Runs.peek
    simpa only [relabel_select,get] using ih
  | seq first second ih₁ ih₂ => exact .seq ih₁ ih₂
  | while_false stop => exact .while_false (by simpa only [get] using stop)
  | while_true go first rest ih₁ ih₂ =>
    exact .while_true (by simpa only [get] using go) ih₁ ih₂

abbrev ComposeIndex (K J : Type*) := K ⊕ (J ⊕ Unit)
private def merge (S : Store K) (T : Store J) : Store (ComposeIndex K J) :=
  Sum.elim S (Sum.elim T (fun _ => []))

private theorem merge_left (p : Program K) {S S' : Store K} {t : ℕ}
    (h : Runs p S t S') (T : Store J) :
    Runs (p.relabel Sum.inl) (merge S T) t (merge S' T) := by
  apply h.relabel Sum.inl (fun V => merge V T) (fun _ _ => rfl)
  intro V k bs
  funext v
  rcases v with j|j
  · by_cases hj : j=k <;> simp [merge,Function.update_apply,hj]
  · simp [merge]

private theorem merge_right (p : Program J) {T T' : Store J} {t : ℕ}
    (h : Runs p T t T') (S : Store K) :
    Runs (p.relabel (fun j => Sum.inr (.inl j))) (merge S T) t (merge S T') := by
  apply h.relabel (fun j => Sum.inr (Sum.inl j)) (fun V => merge S V) (fun _ _ => rfl)
  intro V k bs
  funext v
  rcases v with j|j|j
  · rw [Function.update_of_ne (by simp)]
    rfl
  · by_cases hj : j=k
    · subst j
      rw [Function.update_self]
      change Function.update V k bs k = bs
      exact Function.update_self ..
    · rw [Function.update_of_ne (by simpa using hj)]
      exact Function.update_of_ne hj _ _
  · rw [Function.update_of_ne (by simp)]
    rfl

def Program.composeWords (p : Program K) (fromPort : K) (q : Program J) (toPort : J) :
    Program (ComposeIndex K J) :=
  .seq (p.relabel Sum.inl) (.seq (copy (.inl fromPort) (.inr (.inl toPort)) (.inr (.inr ())))
    (q.relabel (fun j => Sum.inr (.inl j))))

theorem composeWords_runs {p : Program K} {q : Program J} (input out : K) (port result : J)
    {w middle value : List Bool} {t u : ℕ} {S : Store K} {T : Store J}
    (first : Runs p (Function.update (fun _ => []) input w.reverse) t S)
    (handoff : (S out).reverse = middle)
    (second : Runs q (Function.update (fun _ => []) port middle.reverse) u T)
    (output : (T result).reverse = value) :
    ∃ U, Runs (p.composeWords out q port)
      (Function.update (fun _ => []) (.inl input) w.reverse)
      (t+(7*middle.length+2+u)) U ∧
      (U (.inr (.inl result))).reverse = value := by
  let zero : Store J := fun _ => []
  have init : merge (Function.update (fun _ => []) input w.reverse) zero =
      Function.update (fun _ => []) (Sum.inl input) w.reverse := by
    funext x
    rcases x with j|j|j
    · by_cases hj : j=input <;> simp [merge,Function.update_apply,hj]
    · simp [merge,zero]
    · simp [merge]
  have hs : S out = middle.reverse := by simp [← handoff]
  have copied := copy_runs (merge S zero) (.inl out) (.inr (.inl port))
    (.inr (.inr ())) (by simp) (by simp) (by simp) rfl
  have before : Function.update (merge S zero) (.inr (.inl port))
      (merge S zero (.inl out) ++ merge S zero (.inr (.inl port))) =
      merge S (Function.update (fun _ => []) port middle.reverse) := by
    funext x
    rcases x with j|j|j
    · simp [merge]
    · by_cases hj : j=port <;> simp [merge,Function.update_apply,zero,hs,hj]
    · simp [merge]
  rw [before] at copied
  have a := merge_left p first zero
  rw [init] at a
  refine ⟨merge S T,?_,output⟩
  simpa only [Program.composeWords,merge,Sum.elim_inl,hs,List.length_reverse] using
    a.seq (copied.seq (merge_right q second S))

end GroupWL.MachinePrograms.Structured
