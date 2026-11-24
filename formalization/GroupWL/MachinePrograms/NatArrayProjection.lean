import GroupWL.MachinePrograms.NatArrayComponents

namespace GroupWL.MachinePrograms.NatArrayLanguage
variable {R A R' A' : Type*} [DecidableEq R] [DecidableEq A] [DecidableEq R'] [DecidableEq A']
  [Fintype R] [Fintype A] [Fintype R'] [Fintype A']

@[simp] theorem Store.left_setScalar_inl (S : Store (R⊕R') (A⊕A')) (r : R) (v : ℕ) :
    (S.setScalar (.inl r) v).left=S.left.setScalar r v := by
  apply Store.ext
  · intro x; simp [Store.left,Store.setScalar,Function.comp_def]
  · intro a; rfl
@[simp] theorem Store.left_setScalar_inr (S : Store (R⊕R') (A⊕A')) (r : R') (v : ℕ) :
    (S.setScalar (.inr r) v).left=S.left := by
  apply Store.ext
  · intro x; simp [Store.left,Store.setScalar,Function.comp_def]
  · intro a; rfl
@[simp] theorem Store.right_setScalar_inl (S : Store (R⊕R') (A⊕A')) (r : R) (v : ℕ) :
    (S.setScalar (.inl r) v).right=S.right := by
  apply Store.ext
  · intro x; simp [Store.right,Store.setScalar,Function.comp_def]
  · intro a; rfl
@[simp] theorem Store.right_setScalar_inr (S : Store (R⊕R') (A⊕A')) (r : R') (v : ℕ) :
    (S.setScalar (.inr r) v).right=S.right.setScalar r v := by
  apply Store.ext
  · intro x; simp [Store.right,Store.setScalar,Function.comp_def]
  · intro a; rfl

end GroupWL.MachinePrograms.NatArrayLanguage
