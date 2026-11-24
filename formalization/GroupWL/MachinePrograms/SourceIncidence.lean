import GroupWL.MachinePrograms.NatArrayProofs

/-! Actual finite-register scope-membership evaluation from source square
metadata. Incidence is retained even when its coefficient is zero. -/
namespace GroupWL.MachinePrograms.SourceIncidence

open NatArrayLanguage
set_option maxHeartbeats 1000000

inductive Reg where
  | block | horizontal | readout | square | left | right | after | before
  | leftFlag | rightFlag | afterFlag | beforeFlag | total | zero | site | result
  deriving DecidableEq, Fintype
inductive Arr where | left | right | after | before deriving DecidableEq, Fintype
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def read (S : State) (a : Arr) (i : ℕ) : ℕ := (S.array a)[i]?.getD 0

def incidence (S : State) : ℕ :=
  if S.scalar .block < S.scalar .horizontal then
    if S.scalar .block = S.scalar .readout then 1 else 0
  else
    if S.scalar .readout = read S .left (S.scalar .block-S.scalar .horizontal) ∨
       S.scalar .readout = read S .right (S.scalar .block-S.scalar .horizontal) ∨
       S.scalar .readout = read S .after (S.scalar .block-S.scalar .horizontal) ∨
       S.scalar .readout = read S .before (S.scalar .block-S.scalar .horizontal) then 1 else 0

def squareAtoms : List (Atom Reg Arr) := [
  .binary .sub .square .block .horizontal,
  .read .left .left .square,.read .right .right .square,
  .read .after .after .square,.read .before .before .square,
  .binary .eq .leftFlag .readout .left,.binary .eq .rightFlag .readout .right,
  .binary .eq .afterFlag .readout .after,.binary .eq .beforeFlag .readout .before,
  .binary .add .total .leftFlag .rightFlag,
  .binary .add .total .total .afterFlag,
  .binary .add .total .total .beforeFlag,
  .const .zero 0,.binary .lt .result .zero .total]

def program : Code := .seq (.atom (.binary .lt .site .block .horizontal))
  (.branch .site (.atom (.binary .eq .result .block .readout)) (atoms squareAtoms))

def prelude (S : State) : State := (Atom.binary .lt .site .block .horizontal).apply S

def resultStore (S : State) : State :=
  if S.scalar .block < S.scalar .horizontal then
    (Atom.binary .eq .result .block .readout).apply (prelude S)
  else applyAtoms squareAtoms (prelude S)

theorem square_valid (S : State) (M : ℕ) (hS : S.Bounded M) (hM : 4 ≤ M)
    (hi : ∀ a : Arr, S.scalar .block-S.scalar .horizontal < (S.array a).length) :
    ValidAtoms M squareAtoms S := by
  have hb := hS.1 Reg.block
  have hsub : S.scalar .block-S.scalar .horizontal ≤ M := (Nat.sub_le _ _).trans hb
  have hl := hi Arr.left
  have hr := hi Arr.right
  have ha := hi Arr.after
  have hbef := hi Arr.before
  simp [squareAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
    Store.setScalar,Function.update_apply]
  split_ifs <;> omega

theorem program_runs (S : State) (M : ℕ) (hS : S.Bounded M) (hM : 4 ≤ M)
    (hi : S.scalar .horizontal ≤ S.scalar .block →
      ∀ a : Arr, S.scalar .block-S.scalar .horizontal < (S.array a).length) :
    ∃ time ≤ 16, Runs (storageBound Reg Arr M) program S time (resultStore S) ∧
      (resultStore S).Bounded M ∧ (resultStore S).scalar .result = incidence S := by
  have hsmall : (Atom.binary BinaryOp.lt Reg.site Reg.block Reg.horizontal : Atom Reg Arr).SmallResult M S := by
    simp [Atom.SmallResult,BinaryOp.eval]
    split_ifs <;> omega
  have first := atom_runs hS (Atom.binary BinaryOp.lt Reg.site Reg.block Reg.horizontal) trivial hsmall
  have hpre : (prelude S).Bounded M := Atom.apply_bounded hS _ hsmall
  by_cases h : S.scalar .block < S.scalar .horizontal
  · have hs : (prelude S).scalar .site ≠ 0 := by simp [prelude,Atom.apply,BinaryOp.eval,Store.setScalar,h]
    have hlast : (Atom.binary BinaryOp.eq Reg.result Reg.block Reg.readout : Atom Reg Arr).SmallResult M (prelude S) := by
      simp [Atom.SmallResult,BinaryOp.eval,prelude,Atom.apply,Store.setScalar]
      split_ifs <;> omega
    have last := atom_runs hpre (Atom.binary BinaryOp.eq Reg.result Reg.block Reg.readout) trivial hlast
    have hb := Atom.apply_bounded hpre _ hlast
    refine ⟨3,by omega,?_,?_,?_⟩
    · simpa [program,resultStore,h] using first.seq (Runs.branch_nonzero hs last)
    · simpa [resultStore,h] using hb
    · simp [resultStore,incidence,h,prelude,Atom.apply,BinaryOp.eval,Store.setScalar]
  · have hs : (prelude S).scalar .site = 0 := by simp [prelude,Atom.apply,BinaryOp.eval,Store.setScalar,h]
    have hv : ValidAtoms M squareAtoms (prelude S) := square_valid (prelude S) M hpre hM
      (by simpa [prelude,Atom.apply,Store.setScalar] using hi (by omega))
    obtain ⟨last,hb⟩ := atoms_runs hpre squareAtoms hv
    refine ⟨16,by omega,?_,?_,?_⟩
    · simpa [program,resultStore,h,squareAtoms] using first.seq (Runs.branch_zero hs last)
    · simpa [resultStore,h] using hb
    · simp [resultStore,incidence,h,squareAtoms,applyAtoms,prelude,Atom.apply,BinaryOp.eval,
        Store.setScalar,Function.update_apply,read]
      split_ifs <;> omega

theorem resultStore_preserves (S : State) :
    (resultStore S).scalar .block = S.scalar .block ∧
    (resultStore S).scalar .horizontal = S.scalar .horizontal ∧
    (resultStore S).scalar .readout = S.scalar .readout ∧ (resultStore S).array = S.array := by
  simp only [resultStore]
  split <;> simp [squareAtoms,applyAtoms,prelude,Atom.apply,BinaryOp.eval,Store.setScalar,Function.update_apply]

end GroupWL.MachinePrograms.SourceIncidence
