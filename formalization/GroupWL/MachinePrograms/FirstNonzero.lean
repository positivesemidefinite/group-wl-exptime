import GroupWL.MachinePrograms.NatArrayFrames
import GroupWL.MachinePrograms.NatArrayCountedLoops

/-! Bounded first-match search in a materialized array interval. -/
namespace GroupWL.MachinePrograms.FirstNonzero

open NatArrayLanguage
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
set_option linter.unusedSimpArgs false

inductive Reg where
  | base | length | fallback | one | index | todo | cell | flag | found | result
  deriving DecidableEq, Fintype
inductive Arr where
  | input
  deriving DecidableEq, Fintype
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def hit (xs : List ℕ) (base i : ℕ) : Option ℕ :=
  (List.range i).find? (fun j => xs[base+j]?.getD 0 != 0)

@[simp] theorem hit_zero (xs : List ℕ) (base : ℕ) : hit xs base 0=none := rfl

theorem hit_succ (xs : List ℕ) (base i : ℕ) :
    hit xs base (i+1)=(hit xs base i).or
      (if xs[base+i]?.getD 0=0 then none else some i) := by
  simp [hit,List.range_succ]

theorem hit_lt {xs : List ℕ} {base n i : ℕ} (h : hit xs base n=some i) : i<n :=
  List.mem_range.mp (List.mem_of_find?_eq_some h)

theorem hit_getD_lt (xs : List ℕ) (base n default : ℕ) (hdefault : default<n) :
    (hit xs base n).getD default<n := by
  cases h : hit xs base n with
  | none => exact hdefault
  | some i => exact hit_lt h

theorem hit_eq_some_of_unique (xs : List ℕ) (base n value : ℕ) (hvalue : value<n)
    (hmem : xs[base+value]?.getD 0≠0)
    (hunique : ∀ i<n,xs[base+i]?.getD 0≠0 → i=value) : hit xs base n=some value := by
  cases h : hit xs base n with
  | none =>
    have hnot := List.find?_eq_none.mp h value (List.mem_range.mpr hvalue)
    simp [hmem] at hnot
  | some i =>
    have hi := List.find?_some h
    have he := hunique i (hit_lt h) (by simpa using hi)
    exact congrArg some he

def readAtoms : List (Atom Reg Arr) := [
  .binary .add .cell .base .index,.read .flag .input .cell]
def body : Code := .seq (atoms readAtoms)
  (.branch .flag (.branch .found .skip
    (atoms [.copy .result .index,.const .found 1])) .skip)
def prelude : List (Atom Reg Arr) := [.const .one 1,.const .found 0,.copy .result .fallback]
def search : Code := .seq (atoms prelude) (countedLoop .index .todo .length .one body)

theorem body_runs (S : State) (M base i default : ℕ)
    (hb : S.Bounded M) (hbase : S.scalar .base=base) (hi : S.scalar .index=i)
    (hbound : base+i<(S.array .input).length) (hM : 1≤M)
    (hfound : S.scalar .found=if (hit (S.array .input) base i).isSome then 1 else 0)
    (hresult : S.scalar .result=(hit (S.array .input) base i).getD default) :
    ∃ t≤6,∃ T,Runs (storageBound Reg Arr M) body S t T ∧ T.Bounded M ∧
      T.scalar .found=(if (hit (S.array .input) base (i+1)).isSome then 1 else 0) ∧
      T.scalar .result=(hit (S.array .input) base (i+1)).getD default := by
  have hlen := hb.2.1 Arr.input
  have hvalid : ValidAtoms M readAtoms S := by
    simp [readAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,hbase,hi]
    exact ⟨by omega,hbound⟩
  obtain ⟨pre,hU⟩ := atoms_runs hb readAtoms hvalid
  let U := applyAtoms readAtoms S
  have hflag : U.scalar .flag=(S.array .input)[base+i]?.getD 0 := by
    simp [U,applyAtoms,readAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,hbase,hi]
  have hfu : U.scalar .found=S.scalar .found := by simp [U,applyAtoms,readAtoms,Atom.apply,Store.setScalar]
  have hru : U.scalar .result=S.scalar .result := by simp [U,applyAtoms,readAtoms,Atom.apply,Store.setScalar]
  have hiu : U.scalar .index=i := by simp [U,applyAtoms,readAtoms,Atom.apply,Store.setScalar,hi]
  by_cases hz : (S.array .input)[base+i]?.getD 0=0
  · refine ⟨3,by omega,U,.seq pre (.branch_zero (hflag.trans hz)
      (.skip (Store.size_le_of_bounded hU))),hU,?_,?_⟩
    · simpa [hit_succ,hz,hfu] using hfound
    · simpa [hit_succ,hz,hru] using hresult
  · cases hh : hit (S.array .input) base i with
    | none =>
      have hzero : U.scalar .found=0 := by simp [hfu,hfound,hh]
      have hv : ValidAtoms M [.copy Reg.result Reg.index,.const .found 1] U := by
        simp [ValidAtoms,Atom.Valid,Atom.SmallResult,hM]
      obtain ⟨write,hV⟩ := atoms_runs hU _ hv
      let V := applyAtoms [.copy Reg.result Reg.index,.const .found 1] U
      refine ⟨6,le_rfl,V,.seq pre (.branch_nonzero (by rwa [hflag])
        (.branch_zero hzero write)),hV,?_,?_⟩
      · simp [V,applyAtoms,Atom.apply,Store.setScalar,hit_succ,hh,hz]
      · simp [V,applyAtoms,Atom.apply,Store.setScalar,hit_succ,hh,hz,hiu]
    | some j =>
      have hnonzero : U.scalar .found≠0 := by simp [hfu,hfound,hh]
      refine ⟨4,by omega,U,.seq pre (.branch_nonzero (by rwa [hflag])
        (.branch_nonzero hnonzero (.skip (Store.size_le_of_bounded hU)))),hU,?_,?_⟩
      · simp [hit_succ,hh,hfu,hfound]
      · simpa [hit_succ,hh,hru] using hresult

end GroupWL.MachinePrograms.FirstNonzero
