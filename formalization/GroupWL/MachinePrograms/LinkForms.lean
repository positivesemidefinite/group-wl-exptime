import GroupWL.MachinePrograms.ArrayTabulate
import GroupWL.MachinePrograms.NatArrayFrames

/-! Padded coefficients of the left and right private-wire endpoint forms. -/
namespace GroupWL.MachinePrograms.LinkForms
open NatArrayLanguage
set_option maxHeartbeats 2000000

inductive Reg where
  | comparisons | length | cutoff | twiceCutoff | count | index | todo | one | two | zero
  | link | coordinate | flag | position | value
  deriving DecidableEq,Fintype
inductive Arr where
  | forms | output
  deriving DecidableEq,Fintype
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def cutoff (right : Bool) (e L : ℕ) : ℕ := if right then e+e*L else e
def entry (right : Bool) (xs : List ℕ) (e L i : ℕ) : ℕ :=
  if i/2<cutoff right e L then
    if right then (if i%2=0 then 1 else 0) else xs[i]?.getD 0
  else if right then xs[i-2*cutoff right e L]?.getD 0 else (if i%2=0 then 1 else 0)
def splitAtoms : List (Atom Reg Arr) := [
  .divmod .link .coordinate .index .two,.binary .lt .flag .link .cutoff]
def readAtoms (right : Bool) : List (Atom Reg Arr) := [
  if right then .binary .sub .position .index .twiceCutoff else .copy .position .index,
  .read .value .forms .position]
def delta : Code := .atom (.binary .eq .value .coordinate .zero)
def point (right : Bool) : Code := .seq (atoms splitAtoms)
  (.branch .flag (if right then delta else atoms (readAtoms right))
    (if right then atoms (readAtoms right) else delta))
def prelude (right : Bool) : List (Atom Reg Arr) := [
  .const .one 1,.const .two 2,.const .zero 0,
  .binary .mul .count .comparisons .length,.binary .add .count .count .comparisons,
  if right then .copy .cutoff .count else .copy .cutoff .comparisons,
  .binary .mul .twiceCutoff .cutoff .two,
  .binary .add .count .count .comparisons,.binary .mul .count .count .two]
def program (right : Bool) : Code := .seq (atoms (prelude right))
  (ArrayTabulate.tabulate .index .todo .count .one .zero .value .output (point right))

theorem point_runs (right : Bool) (S : State) (M e L : ℕ) (bounded : S.Bounded M)
    (one : 1≤M) (two : S.scalar .two=2) (zero : S.scalar .zero=0)
    (cut : S.scalar .cutoff=cutoff right e L) (twice : S.scalar .twiceCutoff=2*cutoff right e L)
    (length : (S.array .forms).length=2*e) (index : S.scalar .index<(e+e*L+e)*2) :
    ∃ t≤5,∃ T,Runs (storageBound Reg Arr M) (point right) S t T ∧ T.Bounded M ∧
      T.scalar .value=entry right (S.array .forms) e L (S.scalar .index) := by
  have valid : ValidAtoms M splitAtoms S := by
    simp [splitAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar,two]
    split_ifs <;> omega
  obtain ⟨pre,hU⟩ := atoms_runs bounded splitAtoms valid
  let U := applyAtoms splitAtoms S
  have uf : U.scalar .flag=if S.scalar .index/2<cutoff right e L then 1 else 0 := by
    simp [U,applyAtoms,splitAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,two,cut]
  have ucoordinate : U.scalar .coordinate=S.scalar .index%2 := by
    simp [U,applyAtoms,splitAtoms,Atom.apply,Store.setScalar,two]
  have uzero : U.scalar .zero=0 := by simpa [U,applyAtoms,splitAtoms,Atom.apply,Store.setScalar] using zero
  have drun : ∃T,Runs (storageBound Reg Arr M) delta U 1 T ∧ T.Bounded M ∧
      T.scalar .value=if S.scalar .index%2=0 then 1 else 0 := by
    let a : Atom Reg Arr := .binary .eq .value .coordinate .zero
    have hs : a.SmallResult M U := by simp [a,Atom.SmallResult,BinaryOp.eval]; split_ifs <;> omega
    exact ⟨a.apply U,atom_runs hU a trivial hs,a.apply_bounded hU hs,
      by simp [a,Atom.apply,BinaryOp.eval,ucoordinate,uzero]⟩
  have readRun (hread : (if right then S.scalar .index-2*cutoff right e L else S.scalar .index)<2*e) :
      ∃ T,Runs (storageBound Reg Arr M) (atoms (readAtoms right)) U 2 T ∧ T.Bounded M ∧
        T.scalar .value=(S.array .forms)[if right then S.scalar .index-2*cutoff right e L else S.scalar .index]?.getD 0 := by
    have hindex := bounded.1 Reg.index
    have hv : ValidAtoms M (readAtoms right) U := by
      cases right <;>
        simp [readAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
          Store.setScalar,U,applyAtoms,splitAtoms,length,twice] at hread ⊢ <;> omega
    obtain ⟨run,hT⟩ := atoms_runs hU (readAtoms right) hv
    refine ⟨applyAtoms (readAtoms right) U,run,hT,?_⟩
    cases right <;> simp [applyAtoms,readAtoms,U,splitAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,twice]
  cases right with
  | false =>
      by_cases h : S.scalar .index/2<e
      · obtain ⟨T,run,hT,hv⟩ := readRun (by simpa using (show S.scalar .index<2*e by omega))
        refine ⟨5,by omega,T,.seq pre (.branch_nonzero (by rw [uf]; simp [cutoff,h]) run),hT,?_⟩
        simpa [entry,cutoff,h] using hv
      · obtain ⟨T,run,hT,hv⟩ := drun
        refine ⟨4,by omega,T,.seq pre (.branch_zero (by rw [uf]; simp [cutoff,h]) run),hT,?_⟩
        simpa [entry,cutoff,h] using hv
  | true =>
      by_cases h : S.scalar .index/2<e+e*L
      · obtain ⟨T,run,hT,hv⟩ := drun
        refine ⟨4,by omega,T,.seq pre (.branch_nonzero (by rw [uf]; simp [cutoff,h]) run),hT,?_⟩
        simpa [entry,cutoff,h] using hv
      · obtain ⟨T,run,hT,hv⟩ := readRun (by simp [cutoff]; omega)
        refine ⟨5,by omega,T,.seq pre (.branch_zero (by rw [uf]; simp [cutoff,h]) run),hT,?_⟩
        simpa [entry,cutoff,h] using hv

structure Context (right : Bool) (e L : ℕ) (xs : List ℕ) (S : State) : Prop where
  comparisons : S.scalar .comparisons=e
  length : S.scalar .length=L
  cutoff : S.scalar .cutoff=cutoff right e L
  twiceCutoff : S.scalar .twiceCutoff=2*LinkForms.cutoff right e L
  two : S.scalar .two=2
  zero : S.scalar .zero=0
  forms : S.array .forms=xs

theorem program_runs (right : Bool) (S : State) (M : ℕ) (bounded : S.Bounded M)
    (room : 2≤M)
    (size : (S.scalar .comparisons+S.scalar .comparisons*S.scalar .length+S.scalar .comparisons)*2≤M)
    (input : (S.array .forms).length=2*S.scalar .comparisons) :
    ∃ t≤9*((S.scalar .comparisons+S.scalar .comparisons*S.scalar .length+S.scalar .comparisons)*2)+13,∃ T,
      Runs (storageBound Reg Arr M) (program right) S t T ∧ T.Bounded M ∧
      T.array .output=List.ofFn (fun i : Fin ((S.scalar .comparisons+S.scalar .comparisons*S.scalar .length+S.scalar .comparisons)*2) =>
        entry right (S.array .forms) (S.scalar .comparisons) (S.scalar .length) i) := by
  let P := Context right (S.scalar .comparisons) (S.scalar .length) (S.array .forms)
  have pi : ∀ T x,P T → P (T.setScalar .index x) := by
    intro T x h
    exact ⟨by simpa using h.comparisons,by simpa using h.length,by simpa using h.cutoff,
      by simpa using h.twiceCutoff,by simpa using h.two,by simpa using h.zero,h.forms⟩
  have pt : ∀ T x,P T → P (T.setScalar .todo x) := by
    intro T x h
    exact ⟨by simpa using h.comparisons,by simpa using h.length,by simpa using h.cutoff,
      by simpa using h.twiceCutoff,by simpa using h.two,by simpa using h.zero,h.forms⟩
  have po : ∀ T xs,P T → P (T.setArray .output xs) := by
    intro T xs h
    exact ⟨h.comparisons,h.length,h.cutoff,h.twiceCutoff,h.two,h.zero,by simpa using h.forms⟩
  let N := (S.scalar .comparisons+S.scalar .comparisons*S.scalar .length+S.scalar .comparisons)*2
  have body : ∀ i : Fin N,∀ T,P T → T.Bounded M → T.scalar .index=i.val →
      T.scalar .todo=N-i.val → T.scalar .one=1 → ∃ t≤5,∃ U,
        Runs (storageBound Reg Arr M) (point right) T t U ∧ U.Bounded M ∧ P U ∧
        U.scalar .index=i.val ∧ U.scalar .todo=N-i.val ∧ U.scalar .one=1 ∧
        U.scalar .value=entry right (S.array .forms) (S.scalar .comparisons) (S.scalar .length) i ∧
        U.array .output=T.array .output := by
    intro i T hT hb hi ht ho
    obtain ⟨t,htime,U,run,hU,hv⟩ := point_runs right T M (S.scalar .comparisons)
      (S.scalar .length) hb (by omega) hT.two hT.zero hT.cutoff hT.twiceCutoff
      (by rwa [hT.forms]) (by rw [hi]; exact i.isLt)
    have hu : P U := by
      refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
      all_goals first
      | exact (run.scalar_eq_of_not_mem _ (by cases right <;> decide)).trans hT.comparisons
      | exact (run.scalar_eq_of_not_mem _ (by cases right <;> decide)).trans hT.length
      | exact (run.scalar_eq_of_not_mem _ (by cases right <;> decide)).trans hT.cutoff
      | exact (run.scalar_eq_of_not_mem _ (by cases right <;> decide)).trans hT.twiceCutoff
      | exact (run.scalar_eq_of_not_mem _ (by cases right <;> decide)).trans hT.two
      | exact (run.scalar_eq_of_not_mem _ (by cases right <;> decide)).trans hT.zero
      | exact (run.array_eq_of_not_mem _ (by cases right <;> decide)).trans hT.forms
    exact ⟨t,htime,U,run,hU,hu,(run.scalar_eq_of_not_mem .index (by cases right <;> decide)).trans hi,
      (run.scalar_eq_of_not_mem .todo (by cases right <;> decide)).trans ht,
      (run.scalar_eq_of_not_mem .one (by cases right <;> decide)).trans ho,
      by simpa only [hT.forms,hi] using hv,
      run.array_eq_of_not_mem .output (by cases right <;> decide)⟩
  have valid : ValidAtoms M (prelude right) S := by
    cases right <;>
      simp [prelude,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar]
    all_goals omega
  obtain ⟨preRun,hU⟩ := atoms_runs bounded (prelude right) valid
  let U := applyAtoms (prelude right) S
  have hu : P U := by
    refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> cases right <;>
      simp [U,prelude,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,cutoff,Nat.mul_comm,Nat.add_comm]
  obtain ⟨t,ht,T,run,hT,_,hout⟩ := ArrayTabulate.tabulate_runs
    Reg.index Reg.todo Reg.count Reg.one Reg.zero Reg.value Arr.output (point right)
    (fun i : Fin N => entry right (S.array .forms) (S.scalar .comparisons) (S.scalar .length) i)
    P M 5 pi pt po (by decide) (by decide) (by decide) body U hU hu
    (by cases right <;> simp [U,prelude,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,N,Nat.add_comm])
    (by cases right <;> simp [U,prelude,applyAtoms,Atom.apply,Store.setScalar])
    (by cases right <;> simp [U,prelude,applyAtoms,Atom.apply,Store.setScalar])
  refine ⟨9+t,by omega,T,?_,hT,hout⟩
  simpa only [prelude,List.length_cons,List.length_nil] using Runs.seq preRun run

end GroupWL.MachinePrograms.LinkForms
