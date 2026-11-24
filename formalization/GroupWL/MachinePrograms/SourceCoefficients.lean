import GroupWL.MachinePrograms.NatArrayProofs

/-! Primitive execution of the signed source-square matrix entries. -/
namespace GroupWL.MachinePrograms.SourceCoefficients

open NatArrayLanguage
set_option maxHeartbeats 1500000

inductive Reg where
  | block | horizontal | readout | coordinate | modulus | square | index
  | left | right | after | before | leftValue | rightValue
  | leftFlag | rightFlag | afterFlag | beforeFlag | coordinateFlag
  | two | zero | site | quotient | result
  deriving DecidableEq, Fintype
inductive Arr where
  | left | right | after | before | leftForm | rightForm
  deriving DecidableEq, Fintype
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def read (S : State) (a : Arr) (i : ℕ) : ℕ := (S.array a)[i]?.getD 0

def delta (x y : ℕ) : ℕ := if x=y then 1 else 0

def coefficient (S : State) : ℕ :=
  if S.scalar .block < S.scalar .horizontal then 0 else
    let s := S.scalar .block-S.scalar .horizontal
    let k := 2*s+S.scalar .coordinate
    let l := read S .leftForm k*delta (S.scalar .readout) (read S .left s)
    let t := read S .rightForm k*delta (S.scalar .readout) (read S .right s)
    let a := delta (S.scalar .readout) (read S .after s)*delta (S.scalar .coordinate) 0
    let b := delta (S.scalar .readout) (read S .before s)*delta (S.scalar .coordinate) 0
    ((l+S.scalar .modulus-t+a)+S.scalar .modulus-b)%S.scalar .modulus

def squareAtoms : List (Atom Reg Arr) := [
  .const .two 2,.const .zero 0,
  .binary .sub .square .block .horizontal,
  .binary .mul .index .square .two,.binary .add .index .index .coordinate,
  .read .leftValue .leftForm .index,.read .rightValue .rightForm .index,
  .read .left .left .square,.read .right .right .square,
  .read .after .after .square,.read .before .before .square,
  .binary .eq .leftFlag .readout .left,.binary .eq .rightFlag .readout .right,
  .binary .eq .afterFlag .readout .after,.binary .eq .beforeFlag .readout .before,
  .binary .eq .coordinateFlag .coordinate .zero,
  .binary .mul .leftValue .leftValue .leftFlag,.binary .mul .rightValue .rightValue .rightFlag,
  .binary .mul .afterFlag .afterFlag .coordinateFlag,
  .binary .mul .beforeFlag .beforeFlag .coordinateFlag,
  .binary .add .result .leftValue .modulus,.binary .sub .result .result .rightValue,
  .binary .add .result .result .afterFlag,.binary .add .result .result .modulus,
  .binary .sub .result .result .beforeFlag,.divmod .quotient .result .result .modulus]

def program : Code := .seq (.atom (.binary .lt .site .block .horizontal))
  (.branch .site (.atom (.const .result 0)) (atoms squareAtoms))

def prelude (S : State) : State := (Atom.binary .lt .site .block .horizontal).apply S

def resultStore (S : State) : State :=
  if S.scalar .block < S.scalar .horizontal then
    (Atom.const .result 0).apply (prelude S)
  else applyAtoms squareAtoms (prelude S)

def SquareValid (S : State) : Prop :=
  0 < S.scalar .modulus ∧
  (∀ a : Arr, a ≠ .leftForm → a ≠ .rightForm →
    S.scalar .block-S.scalar .horizontal < (S.array a).length) ∧
  (∀ a : Arr, a = .leftForm ∨ a = .rightForm →
    2*(S.scalar .block-S.scalar .horizontal)+S.scalar .coordinate < (S.array a).length ∧
    read S a (2*(S.scalar .block-S.scalar .horizontal)+S.scalar .coordinate) < S.scalar .modulus)

theorem square_valid (S : State) (M : ℕ) (hS : S.Bounded M)
    (hM : 6*S.scalar .modulus+4 ≤ M) (hv : SquareValid S) :
    ValidAtoms M squareAtoms S := by
  have hb := hS.1 Reg.block
  have hsub : S.scalar .block-S.scalar .horizontal ≤ M := (Nat.sub_le _ _).trans hb
  have hl := hv.2.1 Arr.left (by decide) (by decide)
  have hr := hv.2.1 Arr.right (by decide) (by decide)
  have ha := hv.2.1 Arr.after (by decide) (by decide)
  have hbef := hv.2.1 Arr.before (by decide) (by decide)
  have hfl := hv.2.2 Arr.leftForm (Or.inl rfl)
  have hfr := hv.2.2 Arr.rightForm (Or.inr rfl)
  have hlen := hS.2.1 Arr.leftForm
  have hidx : (S.scalar .block-S.scalar .horizontal)*2+S.scalar .coordinate ≤ M := by omega
  have hmul : (S.scalar .block-S.scalar .horizontal)*2 ≤ M := by omega
  have hp := hv.1
  dsimp [read] at hfl hfr
  simp [squareAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
    Store.setScalar,Nat.mul_comm] 
  split_ifs <;> omega

theorem program_runs (S : State) (M : ℕ) (hS : S.Bounded M)
    (hM : 6*S.scalar .modulus+4 ≤ M)
    (hv : S.scalar .horizontal ≤ S.scalar .block → SquareValid S) :
    ∃ time ≤ 28, Runs (storageBound Reg Arr M) program S time (resultStore S) ∧
      (resultStore S).Bounded M ∧ (resultStore S).scalar .result = coefficient S := by
  have hsmall : (Atom.binary BinaryOp.lt Reg.site Reg.block Reg.horizontal : Atom Reg Arr).SmallResult M S := by
    simp [Atom.SmallResult,BinaryOp.eval]
    split_ifs <;> omega
  have first := atom_runs hS (Atom.binary BinaryOp.lt Reg.site Reg.block Reg.horizontal) trivial hsmall
  have hpre : (prelude S).Bounded M := Atom.apply_bounded hS _ hsmall
  by_cases h : S.scalar .block < S.scalar .horizontal
  · have hs : (prelude S).scalar .site ≠ 0 := by simp [prelude,Atom.apply,BinaryOp.eval,Store.setScalar,h]
    have hlast : (Atom.const Reg.result 0 : Atom Reg Arr).SmallResult M (prelude S) := by simp [Atom.SmallResult]
    have last := atom_runs hpre (Atom.const Reg.result 0) trivial hlast
    have hb := Atom.apply_bounded hpre _ hlast
    refine ⟨3,by omega,?_,?_,?_⟩
    · simpa [program,resultStore,h] using first.seq (Runs.branch_nonzero hs last)
    · simpa [resultStore,h] using hb
    · simp [resultStore,coefficient,h,prelude,Atom.apply,Store.setScalar]
  · have hs : (prelude S).scalar .site = 0 := by simp [prelude,Atom.apply,BinaryOp.eval,Store.setScalar,h]
    have hpreM : 6*(prelude S).scalar .modulus+4 ≤ M := by
      simpa [prelude,Atom.apply,Store.setScalar] using hM
    have hv' : SquareValid (prelude S) := by
      simpa [SquareValid,prelude,Atom.apply,Store.setScalar,read] using hv (by omega)
    obtain ⟨last,hb⟩ := atoms_runs hpre squareAtoms (square_valid (prelude S) M hpre hpreM hv')
    refine ⟨28,by omega,?_,?_,?_⟩
    · simpa [program,resultStore,h,squareAtoms] using first.seq (Runs.branch_zero hs last)
    · simpa [resultStore,h] using hb
    · simp [resultStore,coefficient,h,squareAtoms,applyAtoms,prelude,Atom.apply,BinaryOp.eval,
        Store.setScalar,read,delta,Nat.mul_comm]
      split_ifs <;> rfl

theorem resultStore_preserves (S : State) :
    (resultStore S).scalar .block = S.scalar .block ∧
    (resultStore S).scalar .horizontal = S.scalar .horizontal ∧
    (resultStore S).scalar .readout = S.scalar .readout ∧
    (resultStore S).scalar .coordinate = S.scalar .coordinate ∧
    (resultStore S).scalar .modulus = S.scalar .modulus ∧ (resultStore S).array = S.array := by
  simp only [resultStore]
  split <;> simp [squareAtoms,applyAtoms,prelude,Atom.apply,Store.setScalar]

end GroupWL.MachinePrograms.SourceCoefficients
