import GroupWL.MachinePrograms.NatArrayLoops

/-! Proof rules for primitive sequences. Every rule produces the same
bounded operational traces consumed by the concrete stack lowering. -/
namespace GroupWL.MachinePrograms.NatArrayLanguage
variable {Reg Arr : Type*} [DecidableEq Reg] [DecidableEq Arr] [Fintype Reg] [Fintype Arr]

@[ext] theorem Store.ext {S T : Store Reg Arr}
    (hs : ∀ r,S.scalar r=T.scalar r) (ha : ∀ a,S.array a=T.array a) : S=T := by
  cases S; cases T
  congr <;> funext x
  · exact hs x
  · exact ha x

@[simp] theorem Store.setScalar_same (S : Store Reg Arr) (r : Reg) (v : ℕ) :
    (S.setScalar r v).scalar r=v := by simp [Store.setScalar]
@[simp] theorem Store.setScalar_other (S : Store Reg Arr) (r s : Reg) (v : ℕ) (h : s≠r) :
    (S.setScalar r v).scalar s=S.scalar s := by simp [Store.setScalar,h]
@[simp] theorem Store.setScalar_array (S : Store Reg Arr) (r : Reg) (v : ℕ) (a : Arr) :
    (S.setScalar r v).array a=S.array a := rfl
@[simp] theorem Store.setArray_same (S : Store Reg Arr) (a : Arr) (xs : List ℕ) :
    (S.setArray a xs).array a=xs := by simp [Store.setArray]
@[simp] theorem Store.setArray_other (S : Store Reg Arr) (a b : Arr) (xs : List ℕ) (h : b≠a) :
    (S.setArray a xs).array b=S.array b := by simp [Store.setArray,h]
@[simp] theorem Store.setArray_scalar (S : Store Reg Arr) (a : Arr) (xs : List ℕ) (r : Reg) :
    (S.setArray a xs).scalar r=S.scalar r := rfl

theorem Store.Bounded.setScalar {S : Store Reg Arr} {m v : ℕ} (h : S.Bounded m)
    (r : Reg) (hv : v≤m) : (S.setScalar r v).Bounded m := by
  refine ⟨?_,h.2.1,h.2.2⟩
  intro s
  by_cases hs : s=r
  · subst s; simpa using hv
  · simpa [hs] using h.1 s

theorem Store.Bounded.setArray {S : Store Reg Arr} {m : ℕ} (h : S.Bounded m)
    (a : Arr) (xs : List ℕ) (hl : xs.length≤m) (hv : ∀x∈xs,x≤m) :
    (S.setArray a xs).Bounded m := by
  refine ⟨h.1,?_,?_⟩
  · intro b
    by_cases hb : b=a
    · subst b; simpa using hl
    · simpa [hb] using h.2.1 b
  · intro b x hx
    by_cases hb : b=a
    · subst b; exact hv x (by simpa using hx)
    · exact h.2.2 b x (by simpa [hb] using hx)

theorem Store.Bounded.read {S : Store Reg Arr} {m : ℕ} (h : S.Bounded m)
    (a : Arr) (i : ℕ) : (S.array a)[i]?.getD 0≤m := by
  cases hx : (S.array a)[i]? with
  | none => simp
  | some x =>
      simp only [Option.getD_some]
      exact h.2.2 a x (List.mem_of_getElem? hx)

/-- The only primitive results that may exceed the existing store bound
are a literal or an arithmetic result. Array allocation uses already
bounded scalar values. -/
def Atom.SmallResult (m : ℕ) (a : Atom Reg Arr) (S : Store Reg Arr) : Prop :=
  match a with
  | .const _ v => v≤m
  | .binary op _ left right => op.eval (S.scalar left) (S.scalar right)≤m
  | _ => True

theorem Atom.apply_bounded {S : Store Reg Arr} {m : ℕ} (h : S.Bounded m)
    (a : Atom Reg Arr) (small : a.SmallResult m S) : (a.apply S).Bounded m := by
  cases a with
  | const r v => exact h.setScalar r small
  | copy r s => exact h.setScalar r (h.1 s)
  | binary op r l s => exact h.setScalar r small
  | arrayLength r a => exact h.setScalar r (h.2.1 a)
  | read r a i => exact h.setScalar r (h.read a _)
  | write a i v =>
      apply h.setArray a _ (by simpa using h.2.1 a)
      intro x hx
      rcases List.mem_or_eq_of_mem_set hx with hx | hx
      · exact h.2.2 a x hx
      · subst x; exact h.1 v
  | allocate a len v =>
      apply h.setArray a _ (by simpa using h.1 len)
      intro x hx
      have hx' := List.mem_replicate.mp hx
      exact hx'.2 ▸ h.1 v
  | copyArray a b => exact h.setArray a _ (h.2.1 b) (h.2.2 b)
  | clearArray a => exact h.setArray a _ (by simp) (by simp)
  | divmod q r a b =>
      exact (h.setScalar q ((Nat.div_le_self _ _).trans (h.1 a))).setScalar r
        ((Nat.mod_le _ _).trans (h.1 a))

def storageBound (Reg Arr : Type*) [Fintype Reg] [Fintype Arr] (m : ℕ) : ℕ :=
  (Fintype.card Reg+3*Fintype.card Arr)*(m+1)^2

theorem atom_runs {S : Store Reg Arr} {m : ℕ} (h : S.Bounded m)
    (a : Atom Reg Arr) (valid : a.Valid S) (small : a.SmallResult m S) :
    Runs (storageBound Reg Arr m) (.atom a) S 1 (a.apply S) :=
  .atom valid (Store.size_le_of_bounded h) (Store.size_le_of_bounded (a.apply_bounded h small))

/-- A sequence of atoms has exactly its list length in abstract steps. -/
def atoms (as : List (Atom Reg Arr)) : Program Reg Arr := sequence (as.map .atom)

def applyAtoms (as : List (Atom Reg Arr)) (S : Store Reg Arr) : Store Reg Arr :=
  as.foldl (fun T a => a.apply T) S

def ValidAtoms (m : ℕ) : List (Atom Reg Arr) → Store Reg Arr → Prop
  | [],_ => True
  | a::as,S => a.Valid S ∧ a.SmallResult m S ∧ ValidAtoms m as (a.apply S)

theorem atoms_runs {S : Store Reg Arr} {m : ℕ} (h : S.Bounded m)
    (as : List (Atom Reg Arr)) (valid : ValidAtoms m as S) :
    Runs (storageBound Reg Arr m) (atoms as) S as.length (applyAtoms as S) ∧
      (applyAtoms as S).Bounded m := by
  induction as generalizing S with
  | nil => exact ⟨.skip (Store.size_le_of_bounded h),h⟩
  | cons a as ih =>
      obtain ⟨ht,hb⟩ := ih (a.apply_bounded h valid.2.1) valid.2.2
      refine ⟨?_,hb⟩
      simpa only [atoms,List.map_cons,sequence,List.length_cons,applyAtoms,List.foldl_cons,
        Nat.add_comm] using Runs.seq (atom_runs h a valid.1 valid.2.1) ht

theorem sequence_append_runs (ps qs : List (Program Reg Arr))
    {B S T U t s} (first : Runs B (sequence ps) S t T)
    (second : Runs B (sequence qs) T s U) :
    Runs B (sequence (ps++qs)) S (t+s) U := by
  induction ps generalizing S t with
  | nil => cases first; simpa [sequence] using second
  | cons p ps ih =>
      cases first with
      | seq hp hps =>
          simpa only [List.cons_append,sequence,Nat.add_assoc] using Runs.seq hp (ih hps)

end GroupWL.MachinePrograms.NatArrayLanguage

