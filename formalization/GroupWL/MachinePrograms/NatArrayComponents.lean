import GroupWL.MachinePrograms.NatArraySum

/-! Projection and bounded lifting rules for concrete client composition. -/
namespace GroupWL.MachinePrograms.NatArrayLanguage
variable {R A R' A' : Type*}

def Store.left (S : Store (R⊕R') (A⊕A')) : Store R A :=
  ⟨fun r => S.scalar (.inl r),fun a => S.array (.inl a)⟩
def Store.right (S : Store (R⊕R') (A⊕A')) : Store R' A' :=
  ⟨fun r => S.scalar (.inr r),fun a => S.array (.inr a)⟩

@[simp] theorem Store.left_join (S : Store R A) (T : Store R' A') : (S.join T).left=S := rfl
@[simp] theorem Store.right_join (S : Store R A) (T : Store R' A') : (S.join T).right=T := rfl

theorem Store.join_left_right (S : Store (R⊕R') (A⊕A')) : S.left.join S.right=S := by
  cases S with
  | mk scalar array =>
      dsimp only [Store.left,Store.right,Store.join]
      congr 1 <;> funext x <;> cases x <;> rfl

variable [DecidableEq R] [DecidableEq A] [DecidableEq R'] [DecidableEq A']
  [Fintype R] [Fintype A] [Fintype R'] [Fintype A']

theorem Store.Bounded.left {S : Store (R⊕R') (A⊕A')} {m : ℕ} (h : S.Bounded m) :
    S.left.Bounded m := ⟨fun r => h.1 (.inl r),fun a => h.2.1 (.inl a),fun a => h.2.2 (.inl a)⟩

theorem Store.Bounded.right {S : Store (R⊕R') (A⊕A')} {m : ℕ} (h : S.Bounded m) :
    S.right.Bounded m := ⟨fun r => h.1 (.inr r),fun a => h.2.1 (.inr a),fun a => h.2.2 (.inr a)⟩

theorem Store.Bounded.join {S : Store R A} {T : Store R' A'} {m : ℕ}
    (hS : S.Bounded m) (hT : T.Bounded m) : (S.join T).Bounded m := by
  constructor
  · intro r; cases r with
    | inl r => exact hS.1 r
    | inr r => exact hT.1 r
  constructor
  · intro a; cases a with
    | inl a => exact hS.2.1 a
    | inr a => exact hT.2.1 a
  · intro a x hx; cases a with
    | inl a => exact hS.2.2 a x hx
    | inr a => exact hT.2.2 a x hx

theorem storageBound_sum (m : ℕ) :
    storageBound (R⊕R') (A⊕A') m=storageBound R A m+storageBound R' A' m := by
  simp only [storageBound,Fintype.card_sum]
  ring

theorem Runs.left_bounded {m t : ℕ} {p : Program R A} {S : Store (R⊕R') (A⊕A')} {T : Store R A}
    (run : Runs (storageBound R A m) p S.left t T) (hS : S.Bounded m) :
    Runs (storageBound (R⊕R') (A⊕A') m) (p.map Sum.inl Sum.inl) S t (T.join S.right) := by
  have lifted := run.left S.right
  have bound : storageBound R A m+S.right.size≤storageBound (R⊕R') (A⊕A') m := by
    rw [storageBound_sum]
    exact Nat.add_le_add_left (Store.size_le_of_bounded hS.right) _
  simpa only [Store.join_left_right] using lifted.mono bound

theorem Runs.right_bounded {m t : ℕ} {p : Program R' A'} {S : Store (R⊕R') (A⊕A')} {T : Store R' A'}
    (run : Runs (storageBound R' A' m) p S.right t T) (hS : S.Bounded m) :
    Runs (storageBound (R⊕R') (A⊕A') m) (p.map Sum.inr Sum.inr) S t (S.left.join T) := by
  have lifted := run.right S.left
  have bound : S.left.size+storageBound R' A' m≤storageBound (R⊕R') (A⊕A') m := by
    rw [storageBound_sum]
    exact Nat.add_le_add_right (Store.size_le_of_bounded hS.left) _
  simpa only [Store.join_left_right] using lifted.mono bound

theorem Atom.map_map {R'' A'' : Type*} (p : Atom R A) (r : R→R') (a : A→A')
    (r' : R'→R'') (a' : A'→A'') : (p.map r a).map r' a'=p.map (r'∘r) (a'∘a) := by
  cases p <;> rfl

theorem Program.map_map {R'' A'' : Type*} (p : Program R A) (r : R→R') (a : A→A')
    (r' : R'→R'') (a' : A'→A'') : (p.map r a).map r' a'=p.map (r'∘r) (a'∘a) := by
  induction p with
  | skip => rfl
  | atom p => exact congrArg Program.atom (p.map_map r a r' a')
  | seq p q ihp ihq => simp only [Program.map,ihp,ihq]
  | branch x p q ihp ihq => simp only [Program.map,ihp,ihq,Function.comp_apply]
  | «while» x p ih => simp only [Program.map,ih,Function.comp_apply]

end GroupWL.MachinePrograms.NatArrayLanguage

