import GroupWL.MachinePrograms.Stacks

/-! A structured language over a fixed finite set of Boolean stacks.
Every primitive reads at most one top symbol and performs at most one stack
operation; tests are finite tables on `Option Bool`. -/
namespace GroupWL.MachinePrograms.Structured

abbrev Store (K : Type*) := K → List Bool

inductive Program (K : Type*) where
  | skip : Program K
  | push : K → Bool → Program K
  | pop : K → Program K → Program K → Program K → Program K
  | peek : K → Program K → Program K → Program K → Program K
  | seq : Program K → Program K → Program K
  | while : K → (Option Bool → Bool) → Program K → Program K

variable {K : Type*}

def select (a : Option Bool) (pn pf pt : Program K) : Program K :=
  match a with
  | none => pn
  | some false => pf
  | some true => pt

variable [DecidableEq K]

/-- Exact primitive-operation counts. Sequencing and the empty program are
free; every branch/loop guard performs one actual stack read. -/
inductive Runs : Program K → Store K → ℕ → Store K → Prop where
  | skip (S : Store K) : Runs .skip S 0 S
  | push (S : Store K) (k : K) (b : Bool) :
      Runs (.push k b) S 1 (Function.update S k (b :: S k))
  | pop {S S' : Store K} {k : K} {pn pf pt : Program K} {t : ℕ}
      (branch : Runs (select (S k).head? pn pf pt)
        (Function.update S k (S k).tail) t S') :
      Runs (.pop k pn pf pt) S (t+1) S'
  | peek {S S' : Store K} {k : K} {pn pf pt : Program K} {t : ℕ}
      (branch : Runs (select (S k).head? pn pf pt) S t S') :
      Runs (.peek k pn pf pt) S (t+1) S'
  | seq {S S' S'' : Store K} {p q : Program K} {t u : ℕ}
      (first : Runs p S t S') (second : Runs q S' u S'') :
      Runs (.seq p q) S (t+u) S''
  | while_false {S : Store K} {k : K} {test : Option Bool → Bool} {body : Program K}
      (stop : test (S k).head? = false) :
      Runs (.while k test body) S 1 S
  | while_true {S S' S'' : Store K} {k : K} {test : Option Bool → Bool}
      {body : Program K} {t u : ℕ} (go : test (S k).head? = true)
      (first : Runs body S t S') (rest : Runs (.while k test body) S' u S'') :
      Runs (.while k test body) S (t+u+1) S''

/-- One label per primitive or loop guard, and no label for a sequencing node. -/
def Label : Program K → Type
  | .skip => Empty
  | .push _ _ => Unit
  | .pop _ pn pf pt => Unit ⊕ (Label pn ⊕ (Label pf ⊕ Label pt))
  | .peek _ pn pf pt => Unit ⊕ (Label pn ⊕ (Label pf ⊕ Label pt))
  | .seq p q => Label p ⊕ Label q
  | .while _ _ p => Unit ⊕ Label p

instance labelFintype : (p : Program K) → Fintype (Label p)
  | .skip => inferInstanceAs (Fintype Empty)
  | .push _ _ => inferInstanceAs (Fintype Unit)
  | .pop _ pn pf pt => by
      letI := labelFintype pn
      letI := labelFintype pf
      letI := labelFintype pt
      exact inferInstanceAs (Fintype (Unit ⊕ (Label pn ⊕ (Label pf ⊕ Label pt))))
  | .peek _ pn pf pt => by
      letI := labelFintype pn
      letI := labelFintype pf
      letI := labelFintype pt
      exact inferInstanceAs (Fintype (Unit ⊕ (Label pn ⊕ (Label pf ⊕ Label pt))))
  | .seq p q => by
      letI := labelFintype p
      letI := labelFintype q
      exact inferInstanceAs (Fintype (Label p ⊕ Label q))
  | .while _ _ p => by
      letI := labelFintype p
      exact inferInstanceAs (Fintype (Unit ⊕ Label p))

instance labelDecidableEq : (p : Program K) → DecidableEq (Label p)
  | .skip => inferInstanceAs (DecidableEq Empty)
  | .push _ _ => inferInstanceAs (DecidableEq Unit)
  | .pop _ pn pf pt => by
      letI := labelDecidableEq pn
      letI := labelDecidableEq pf
      letI := labelDecidableEq pt
      exact inferInstanceAs (DecidableEq (Unit ⊕ (Label pn ⊕ (Label pf ⊕ Label pt))))
  | .peek _ pn pf pt => by
      letI := labelDecidableEq pn
      letI := labelDecidableEq pf
      letI := labelDecidableEq pt
      exact inferInstanceAs (DecidableEq (Unit ⊕ (Label pn ⊕ (Label pf ⊕ Label pt))))
  | .seq p q => by
      letI := labelDecidableEq p
      letI := labelDecidableEq q
      exact inferInstanceAs (DecidableEq (Label p ⊕ Label q))
  | .while _ _ p => by
      letI := labelDecidableEq p
      exact inferInstanceAs (DecidableEq (Unit ⊕ Label p))

variable {Q : Type*}

/-- The entry label incorporates empty programs and sequencing at compile time. -/
def entry : (p : Program K) → (Label p → Q) → Q → Q
  | .skip, _, exit => exit
  | .push _ _, label, _ => label ()
  | .pop _ _ _ _, label, _ => label (.inl ())
  | .peek _ _ _ _, label, _ => label (.inl ())
  | .seq p q, label, exit =>
      entry p (fun l => label (.inl l)) (entry q (fun l => label (.inr l)) exit)
  | .while _ _ _, label, _ => label (.inl ())

def branchLabel (pn pf pt : Program K)
    (label : Unit ⊕ (Label pn ⊕ (Label pf ⊕ Label pt)) → Q) :
    (a : Option Bool) → Label (select a pn pf pt) → Q
  | none, l => label (.inr (.inl l))
  | some false, l => label (.inr (.inr (.inl l)))
  | some true, l => label (.inr (.inr (.inr l)))

/-- Instructions for a structured fragment, with an arbitrary continuation
label in the surrounding finite-control machine. -/
def code : (p : Program K) → (Label p → Q) → Q → Label p → Stacks.Instruction K Q
  | .skip, _, _, l => nomatch l
  | .push k b, _, exit, _ => .push k b exit
  | .pop k pn pf pt, label, exit, .inl _ =>
      .pop k (fun a => entry (select a pn pf pt) (branchLabel pn pf pt label a) exit)
  | .pop _ pn _ _, label, exit, .inr (.inl l) =>
      code pn (fun l => label (.inr (.inl l))) exit l
  | .pop _ _ pf _, label, exit, .inr (.inr (.inl l)) =>
      code pf (fun l => label (.inr (.inr (.inl l)))) exit l
  | .pop _ _ _ pt, label, exit, .inr (.inr (.inr l)) =>
      code pt (fun l => label (.inr (.inr (.inr l)))) exit l
  | .peek k pn pf pt, label, exit, .inl _ =>
      .peek k (fun a => entry (select a pn pf pt) (branchLabel pn pf pt label a) exit)
  | .peek _ pn _ _, label, exit, .inr (.inl l) =>
      code pn (fun l => label (.inr (.inl l))) exit l
  | .peek _ _ pf _, label, exit, .inr (.inr (.inl l)) =>
      code pf (fun l => label (.inr (.inr (.inl l)))) exit l
  | .peek _ _ _ pt, label, exit, .inr (.inr (.inr l)) =>
      code pt (fun l => label (.inr (.inr (.inr l)))) exit l
  | .seq p q, label, exit, .inl l =>
      code p (fun l => label (.inl l)) (entry q (fun l => label (.inr l)) exit) l
  | .seq _ q, label, exit, .inr l => code q (fun l => label (.inr l)) exit l
  | .while k test body, label, exit, .inl _ =>
      .peek k (fun a => if test a then entry body (fun l => label (.inr l)) (label (.inl ()))
        else exit)
  | .while _ _ body, label, _, .inr l =>
      code body (fun l => label (.inr l)) (label (.inl ())) l

def active (q : Q) (S : Store K) : Stacks.Config K Q := ⟨.inr q,S⟩

/-- Compilation is exact even inside a larger finite-control machine. The
instruction equations are discharged definitionally by the concrete compiler. -/
theorem Runs.compiled {p : Program K} {S S' : Store K} {t : ℕ}
    (h : Runs p S t S') :
    ∀ {Q : Type*} (M : Stacks.Machine K Q) (label : Label p → Q) (exit : Q),
      (∀ l, M.instruction (label l) = code p label exit l) →
      (Stacks.step M)^[t] (active (entry p label exit) S) = active exit S' := by
  induction h with
  | skip S =>
      intro Q M label exit hcode
      rfl
  | push S k b =>
      intro Q M label exit hcode
      simp only [Function.iterate_one, active, entry, Stacks.step, hcode, code]
  | @pop S S' k pn pf pt t branch ih =>
      intro Q M label exit hcode
      have hb : ∀ l, M.instruction (branchLabel pn pf pt label (S k).head? l) =
          code (select (S k).head? pn pf pt)
            (branchLabel pn pf pt label (S k).head?) exit l := by
        cases ha : (S k).head? with
        | none => intro l; exact hcode (.inr (.inl l))
        | some b => cases b with
          | false => intro l; exact hcode (.inr (.inr (.inl l)))
          | true => intro l; exact hcode (.inr (.inr (.inr l)))
      have hs : Stacks.step M (active (entry (.pop k pn pf pt) label exit) S) =
          active (entry (select (S k).head? pn pf pt)
            (branchLabel pn pf pt label (S k).head?) exit)
            (Function.update S k (S k).tail) := by
        simp only [active, entry, Stacks.step, hcode, code]
      rw [Function.iterate_succ_apply, hs]
      exact ih M _ exit hb
  | @peek S S' k pn pf pt t branch ih =>
      intro Q M label exit hcode
      have hb : ∀ l, M.instruction (branchLabel pn pf pt label (S k).head? l) =
          code (select (S k).head? pn pf pt)
            (branchLabel pn pf pt label (S k).head?) exit l := by
        cases ha : (S k).head? with
        | none => intro l; exact hcode (.inr (.inl l))
        | some b => cases b with
          | false => intro l; exact hcode (.inr (.inr (.inl l)))
          | true => intro l; exact hcode (.inr (.inr (.inr l)))
      have hs : Stacks.step M (active (entry (.peek k pn pf pt) label exit) S) =
          active (entry (select (S k).head? pn pf pt)
            (branchLabel pn pf pt label (S k).head?) exit) S := by
        simp only [active, entry, Stacks.step, hcode, code]
      rw [Function.iterate_succ_apply, hs]
      exact ih M _ exit hb
  | @seq S S' S'' p q t u first second ihp ihq =>
      intro Q M label exit hcode
      have hp : ∀ l, M.instruction (label (.inl l)) =
          code p (fun l => label (.inl l)) (entry q (fun l => label (.inr l)) exit) l :=
        fun l => hcode (.inl l)
      have hq : ∀ l, M.instruction (label (.inr l)) =
          code q (fun l => label (.inr l)) exit l := fun l => hcode (.inr l)
      change (Stacks.step M)^[t+u]
        (active (entry p (fun l => label (.inl l))
          (entry q (fun l => label (.inr l)) exit)) S) = _
      rw [Nat.add_comm t u, Function.iterate_add_apply,
        ihp M _ _ hp]
      exact ihq M _ exit hq
  | @while_false S k test body stop =>
      intro Q M label exit hcode
      simp only [Function.iterate_one, active, entry, Stacks.step, hcode, code,
        stop, Bool.false_eq_true, ↓reduceIte]
  | @while_true S S' S'' k test body t u go first rest ihbody ihrest =>
      intro Q M label exit hcode
      have hb : ∀ l, M.instruction (label (.inr l)) =
          code body (fun l => label (.inr l)) (label (.inl ())) l :=
        fun l => hcode (.inr l)
      have hs : Stacks.step M (active (entry (.while k test body) label exit) S) =
          active (entry body (fun l => label (.inr l)) (label (.inl ()))) S := by
        simp only [active, entry, Stacks.step, hcode, code, go, ↓reduceIte]
      rw [Function.iterate_succ_apply, hs, Nat.add_comm t u, Function.iterate_add_apply,
        ihbody M _ _ hb]
      exact ihrest M label exit hcode

/-- A closed program has one additional halt label. -/
def compile (p : Program K) (result : Bool) : Stacks.Machine K (Label p ⊕ Unit) where
  start := entry p Sum.inl (.inr ())
  instruction
    | .inl l => code p Sum.inl (.inr ()) l
    | .inr _ => .halt result

/-- A closed structured computation takes exactly one further halt step. -/
theorem compile_runs {p : Program K} {S S' : Store K} {t : ℕ}
    (h : Runs p S t S') (result : Bool) :
    (Stacks.step (compile p result))^[t+1]
      (active (compile p result).start S) = ⟨.inl result,S'⟩ := by
  have hc := h.compiled (compile p result) Sum.inl (.inr ()) (fun _ => rfl)
  rw [Function.iterate_succ_apply']
  change Stacks.step (compile p result)
    ((Stacks.step (compile p result))^[t] (active (entry p Sum.inl (.inr ())) S)) = _
  rw [hc]
  rfl

/-- The standard stack-machine input convention is preserved exactly. -/
theorem compile_executes {p : Program K} (input : K) (w : Complexity.BitString)
    {S' : Store K} {t : ℕ}
    (h : Runs p (Function.update (fun _ => []) input w.reverse) t S') (result : Bool) :
    Stacks.execute (compile p result) input w (t+1) = ⟨.inl result,S'⟩ :=
  compile_runs h result

/-- A decision program may inspect one designated output stack before halting.
The final test is a table on three possible top symbols. -/
def compileTest (p : Program K) (output : K) (test : Option Bool → Bool) :
    Stacks.Machine K (Label p ⊕ (Unit ⊕ Bool)) where
  start := entry p Sum.inl (.inr (.inl ()))
  instruction
    | .inl l => code p Sum.inl (.inr (.inl ())) l
    | .inr (.inl _) => .peek output (fun a => .inr (.inr (test a)))
    | .inr (.inr b) => .halt b

theorem compileTest_runs {p : Program K} {S S' : Store K} {t : ℕ}
    (h : Runs p S t S') (output : K) (test : Option Bool → Bool) :
    (Stacks.step (compileTest p output test))^[t+2]
      (active (compileTest p output test).start S) =
        ⟨.inl (test (S' output).head?),S'⟩ := by
  have hc := h.compiled (compileTest p output test) Sum.inl (.inr (.inl ())) (fun _ => rfl)
  rw [Nat.add_comm t 2, Function.iterate_add_apply]
  change (Stacks.step (compileTest p output test))^[2]
    ((Stacks.step (compileTest p output test))^[t]
      (active (entry p Sum.inl (.inr (.inl ()))) S)) = _
  rw [hc]
  rfl

theorem compileTest_executes {p : Program K} (input : K) (w : Complexity.BitString)
    {S' : Store K} {t : ℕ}
    (h : Runs p (Function.update (fun _ => []) input w.reverse) t S')
    (output : K) (test : Option Bool → Bool) :
    Stacks.execute (compileTest p output test) input w (t+2) =
      ⟨.inl (test (S' output).head?),S'⟩ := compileTest_runs h output test

end GroupWL.MachinePrograms.Structured
