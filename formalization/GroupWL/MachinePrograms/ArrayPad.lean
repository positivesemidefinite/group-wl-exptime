import GroupWL.MachinePrograms.ArrayTabulate
import GroupWL.MachinePrograms.NatArrayFrames

/-! Copy an array into a longer array, filling the added entries by a constant. -/
namespace GroupWL.MachinePrograms.ArrayPad
open NatArrayLanguage
set_option maxHeartbeats 1000000
inductive Reg where
  | length | count | padding | index | todo | one | zero | flag | value
  deriving DecidableEq,Fintype
inductive Arr where
  | input | output
  deriving DecidableEq,Fintype
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def entry (xs : List ℕ) (padding i : ℕ) : ℕ := if i<xs.length then xs[i]?.getD 0 else padding
def point : Code := .seq (.atom (.binary .lt .flag .index .length))
  (.branch .flag (.atom (.read .value .input .index)) (.atom (.copy .value .padding)))
def prelude : List (Atom Reg Arr) := [.const .one 1,.const .zero 0,.arrayLength .length .input]
def program : Code := .seq (atoms prelude)
  (ArrayTabulate.tabulate .index .todo .count .one .zero .value .output point)

theorem point_runs (S : State) (M : ℕ) (bounded : S.Bounded M) (room : 1≤M)
    (length : S.scalar .length=(S.array .input).length) :
    ∃ T,Runs (storageBound Reg Arr M) point S 3 T ∧ T.Bounded M ∧
      T.scalar .value=entry (S.array .input) (S.scalar .padding) (S.scalar .index) := by
  let a : Atom Reg Arr := .binary .lt .flag .index .length
  have small : a.SmallResult M S := by simp [a,Atom.SmallResult,BinaryOp.eval]; split_ifs <;> omega
  have run := atom_runs bounded a trivial small
  let U := a.apply S
  have hU := a.apply_bounded bounded small
  by_cases h : S.scalar .index<(S.array .input).length
  · let b : Atom Reg Arr := .read .value .input .index
    have vb : b.Valid U := by simpa [b,U,a,Atom.Valid,Atom.apply,Store.setScalar] using h
    have sb : b.SmallResult M U := by simp [b,Atom.SmallResult]
    refine ⟨b.apply U,.seq run (.branch_nonzero ?_ (atom_runs hU b vb sb)),b.apply_bounded hU sb,?_⟩
    · simp [U,a,Atom.apply,BinaryOp.eval,Store.setScalar,length,h]
    · simp [b,U,a,Atom.apply,Store.setScalar,entry,h]
  · let b : Atom Reg Arr := .copy .value .padding
    have sb : b.SmallResult M U := by simpa [b,U,a,Atom.SmallResult,Atom.apply,Store.setScalar] using bounded.1 Reg.padding
    refine ⟨b.apply U,.seq run (.branch_zero ?_ (atom_runs hU b trivial sb)),b.apply_bounded hU sb,?_⟩
    · simp [U,a,Atom.apply,BinaryOp.eval,Store.setScalar,length,h]
    · simp [b,U,a,Atom.apply,Store.setScalar,entry,h]

structure Context (xs : List ℕ) (padding : ℕ) (S : State) : Prop where
  length : S.scalar .length=xs.length
  padding_eq : S.scalar .padding=padding
  input : S.array .input=xs

theorem program_runs (S : State) (M : ℕ) (bounded : S.Bounded M) (room : 1≤M) :
    ∃ t≤7*S.scalar .count+7,∃ T,Runs (storageBound Reg Arr M) program S t T ∧
      T.Bounded M ∧ T.array .output=List.ofFn (fun i : Fin (S.scalar .count) => entry (S.array .input) (S.scalar .padding) i) := by
  let P := Context (S.array .input) (S.scalar .padding)
  have pi : ∀ T x,P T → P (T.setScalar .index x) := by
    intro T x h; exact ⟨by simpa using h.length,by simpa using h.padding_eq,h.input⟩
  have pt : ∀ T x,P T → P (T.setScalar .todo x) := by
    intro T x h; exact ⟨by simpa using h.length,by simpa using h.padding_eq,h.input⟩
  have po : ∀ T xs,P T → P (T.setArray .output xs) := by
    intro T xs h; exact ⟨h.length,h.padding_eq,by simpa using h.input⟩
  have body : ∀ i : Fin (S.scalar .count),∀ T,P T → T.Bounded M → T.scalar .index=i.val →
      T.scalar .todo=S.scalar .count-i.val → T.scalar .one=1 → ∃ t≤3,∃ U,
        Runs (storageBound Reg Arr M) point T t U ∧ U.Bounded M ∧ P U ∧
        U.scalar .index=i.val ∧ U.scalar .todo=S.scalar .count-i.val ∧ U.scalar .one=1 ∧
        U.scalar .value=entry (S.array .input) (S.scalar .padding) i ∧ U.array .output=T.array .output := by
    intro i T hT hb hi ht ho
    obtain ⟨U,run,hU,hv⟩ := point_runs T M hb room (by rw [hT.length,hT.input])
    exact ⟨3,by omega,U,run,hU,
      ⟨(run.scalar_eq_of_not_mem .length (by decide)).trans hT.length,
       (run.scalar_eq_of_not_mem .padding (by decide)).trans hT.padding_eq,
       (run.array_eq_of_not_mem .input (by decide)).trans hT.input⟩,
      (run.scalar_eq_of_not_mem .index (by decide)).trans hi,
      (run.scalar_eq_of_not_mem .todo (by decide)).trans ht,
      (run.scalar_eq_of_not_mem .one (by decide)).trans ho,
      by simpa only [hT.input,hT.padding_eq,hi] using hv,
      run.array_eq_of_not_mem .output (by decide)⟩
  have valid : ValidAtoms M prelude S := by
    simpa [prelude,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,Store.setScalar] using
      room
  obtain ⟨preRun,hU⟩ := atoms_runs bounded prelude valid
  let U := applyAtoms prelude S
  have hu : P U := by refine ⟨?_,?_,?_⟩ <;> simp [U,prelude,applyAtoms,Atom.apply,Store.setScalar]
  obtain ⟨t,ht,T,run,hT,_,hout⟩ := ArrayTabulate.tabulate_runs
    Reg.index Reg.todo Reg.count Reg.one Reg.zero Reg.value Arr.output point
    (fun i : Fin (S.scalar .count) => entry (S.array .input) (S.scalar .padding) i)
    P M 3 pi pt po (by decide) (by decide) (by decide) body U hU hu
    (by simp [U,prelude,applyAtoms,Atom.apply,Store.setScalar])
    (by simp [U,prelude,applyAtoms,Atom.apply,Store.setScalar])
    (by simp [U,prelude,applyAtoms,Atom.apply,Store.setScalar])
  exact ⟨3+t,by omega,T,.seq preRun run,hT,hout⟩

end GroupWL.MachinePrograms.ArrayPad
