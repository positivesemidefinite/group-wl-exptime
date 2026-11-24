import GroupWL.MachinePrograms.NatArrayProofs

/-! Composition of finite-register clients with disjoint auxiliary storage. -/
namespace GroupWL.MachinePrograms.NatArrayLanguage

variable {R A R' A' : Type*}

def Atom.map (r : R → R') (a : A → A') : Atom R A → Atom R' A'
  | .const x n => .const (r x) n
  | .copy x y => .copy (r x) (r y)
  | .binary op x y z => .binary op (r x) (r y) (r z)
  | .arrayLength x y => .arrayLength (r x) (a y)
  | .read x y z => .read (r x) (a y) (r z)
  | .write x y z => .write (a x) (r y) (r z)
  | .allocate x y z => .allocate (a x) (r y) (r z)
  | .copyArray x y => .copyArray (a x) (a y)
  | .clearArray x => .clearArray (a x)
  | .divmod x y z w => .divmod (r x) (r y) (r z) (r w)

def Program.map (r : R → R') (a : A → A') : Program R A → Program R' A'
  | .skip => .skip
  | .atom x => .atom (x.map r a)
  | .seq p q => .seq (p.map r a) (q.map r a)
  | .branch x p q => .branch (r x) (p.map r a) (q.map r a)
  | .while x p => .while (r x) (p.map r a)

def Store.join (S : Store R A) (T : Store R' A') : Store (R⊕R') (A⊕A') where
  scalar := Sum.elim S.scalar T.scalar
  array := Sum.elim S.array T.array

@[simp] theorem Store.join_scalar_left (S : Store R A) (T : Store R' A') (r : R) :
    (S.join T).scalar (.inl r) = S.scalar r := rfl
@[simp] theorem Store.join_scalar_right (S : Store R A) (T : Store R' A') (r : R') :
    (S.join T).scalar (.inr r) = T.scalar r := rfl
@[simp] theorem Store.join_array_left (S : Store R A) (T : Store R' A') (a : A) :
    (S.join T).array (.inl a) = S.array a := rfl
@[simp] theorem Store.join_array_right (S : Store R A) (T : Store R' A') (a : A') :
    (S.join T).array (.inr a) = T.array a := rfl

variable [DecidableEq R] [DecidableEq A] [DecidableEq R'] [DecidableEq A']
  [Fintype R] [Fintype A] [Fintype R'] [Fintype A']

@[simp] theorem Store.join_size (S : Store R A) (T : Store R' A') :
    (S.join T).size = S.size+T.size := by
  simp [Store.size,Store.join,Fintype.sum_sum_type]
  omega

@[simp] theorem Store.join_setScalar_left (S : Store R A) (T : Store R' A') (r : R) (v : ℕ) :
    (S.join T).setScalar (.inl r) v = (S.setScalar r v).join T := by
  apply Store.ext
  · intro x; cases x <;> simp only [Store.setScalar,Store.join,Function.update_apply,
      Sum.elim_inl,Sum.elim_inr,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq,ite_false]
  · intro x; rfl

@[simp] theorem Store.join_setScalar_right (S : Store R A) (T : Store R' A') (r : R') (v : ℕ) :
    (S.join T).setScalar (.inr r) v = S.join (T.setScalar r v) := by
  apply Store.ext
  · intro x; cases x <;> simp only [Store.setScalar,Store.join,Function.update_apply,
      Sum.elim_inl,Sum.elim_inr,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq,ite_false]
  · intro x; rfl

@[simp] theorem Store.join_setArray_left (S : Store R A) (T : Store R' A') (a : A) (xs : List ℕ) :
    (S.join T).setArray (.inl a) xs = (S.setArray a xs).join T := by
  apply Store.ext
  · intro x; rfl
  · intro x; cases x <;> simp only [Store.setArray,Store.join,Function.update_apply,
      Sum.elim_inl,Sum.elim_inr,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq,ite_false]

@[simp] theorem Store.join_setArray_right (S : Store R A) (T : Store R' A') (a : A') (xs : List ℕ) :
    (S.join T).setArray (.inr a) xs = S.join (T.setArray a xs) := by
  apply Store.ext
  · intro x; rfl
  · intro x; cases x <;> simp only [Store.setArray,Store.join,Function.update_apply,
      Sum.elim_inl,Sum.elim_inr,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq,ite_false]

@[simp] theorem Atom.map_left_apply (a : Atom R A) (S : Store R A) (T : Store R' A') :
    (a.map Sum.inl Sum.inl).apply (S.join T) = (a.apply S).join T := by
  cases a <;> simp only [Atom.map,Atom.apply,Store.join_scalar_left,Store.join_array_left,
    Store.join_setScalar_left,Store.join_setArray_left]

@[simp] theorem Atom.map_right_apply (a : Atom R' A') (S : Store R A) (T : Store R' A') :
    (a.map Sum.inr Sum.inr).apply (S.join T) = S.join (a.apply T) := by
  cases a <;> simp only [Atom.map,Atom.apply,Store.join_scalar_right,Store.join_array_right,
    Store.join_setScalar_right,Store.join_setArray_right]

@[simp] theorem Atom.map_left_valid (a : Atom R A) (S : Store R A) (T : Store R' A') :
    (a.map Sum.inl Sum.inl).Valid (S.join T) ↔ a.Valid S := by
  cases a <;> simp [Atom.map,Atom.Valid,Store.join]

@[simp] theorem Atom.map_right_valid (a : Atom R' A') (S : Store R A) (T : Store R' A') :
    (a.map Sum.inr Sum.inr).Valid (S.join T) ↔ a.Valid T := by
  cases a <;> simp [Atom.map,Atom.Valid,Store.join]

theorem Runs.left {B : ℕ} {p : Program R A} {S U : Store R A} {t : ℕ}
    (h : Runs B p S t U) (T : Store R' A') :
    Runs (B+T.size) (p.map Sum.inl Sum.inl) (S.join T) t (U.join T) := by
  induction h with
  | skip hs => exact .skip (by simp; omega)
  | @atom a S hv hb ha =>
      simpa only [Program.map,Atom.map_left_apply] using
        Runs.atom (bound := B+T.size) (a := Atom.map Sum.inl Sum.inl a) (S := Store.join S T)
          (by simpa using hv) (by simp; omega) (by simp; omega)
  | seq hp hq ih ih' => exact .seq ih ih'
  | branch_nonzero hn hp ih => exact .branch_nonzero hn ih
  | branch_zero hz hp ih => exact .branch_zero hz ih
  | while_zero hz hs => exact .while_zero hz (by simp; omega)
  | while_nonzero hn hp hrest ih ih' => exact .while_nonzero hn ih ih'

theorem Runs.right {B : ℕ} {p : Program R' A'} {T U : Store R' A'} {t : ℕ}
    (h : Runs B p T t U) (S : Store R A) :
    Runs (S.size+B) (p.map Sum.inr Sum.inr) (S.join T) t (S.join U) := by
  induction h with
  | skip hs => exact .skip (by simp; omega)
  | @atom a T hv hb ha =>
      simpa only [Program.map,Atom.map_right_apply] using
        Runs.atom (bound := S.size+B) (a := Atom.map Sum.inr Sum.inr a) (S := Store.join S T)
          (by simpa using hv) (by simp; omega) (by simp; omega)
  | seq hp hq ih ih' => exact .seq ih ih'
  | branch_nonzero hn hp ih => exact .branch_nonzero hn ih
  | branch_zero hz hp ih => exact .branch_zero hz ih
  | while_zero hz hs => exact .while_zero hz (by simp; omega)
  | while_nonzero hn hp hrest ih ih' => exact .while_nonzero hn ih ih'

end GroupWL.MachinePrograms.NatArrayLanguage
