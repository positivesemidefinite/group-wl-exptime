import GroupWL.MachinePrograms.ArrayTabulate
import GroupWL.MachinePrograms.NatArrayFrames

/-! Unit charge on the last coordinate of one specified link. -/
namespace GroupWL.MachinePrograms.SquareCharges
open NatArrayLanguage
set_option maxHeartbeats 1500000
inductive Reg where
  | links | width | special | count | index | todo | one | four | zero
  | quotient | remainder | link | coordinate | next | firstFlag | lastFlag | value
  deriving DecidableEq,Fintype
inductive Arr where | output deriving DecidableEq,Fintype
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def entry (width special index : ℕ) : ℕ :=
  if index/4/width=special ∧ index/4%width+1=width then 1 else 0
def pointAtoms : List (Atom Reg Arr) := [
  .divmod .quotient .remainder .index .four,
  .divmod .link .coordinate .quotient .width,
  .binary .add .next .coordinate .one,
  .binary .eq .firstFlag .link .special,
  .binary .eq .lastFlag .next .width,
  .binary .mul .value .firstFlag .lastFlag]
def point : Code := atoms pointAtoms
def prelude : List (Atom Reg Arr) := [
  .const .one 1,.const .four 4,.const .zero 0,
  .binary .mul .count .links .width,.binary .mul .count .count .four]
def program : Code := .seq (atoms prelude)
  (ArrayTabulate.tabulate .index .todo .count .one .zero .value .output point)

theorem point_runs (S : State) (M : ℕ) (bounded : S.Bounded M) (room : 1≤M)
    (one : S.scalar .one=1) (four : S.scalar .four=4) (width : 0<S.scalar .width) :
    ∃ T,Runs (storageBound Reg Arr M) point S 6 T ∧ T.Bounded M ∧
      T.scalar .value=entry (S.scalar .width) (S.scalar .special) (S.scalar .index) := by
  have hi := bounded.1 Reg.index
  have hw := bounded.1 Reg.width
  have hdiv := Nat.div_le_self (S.scalar .index) 4
  have hdiv2 := Nat.div_le_self (S.scalar .index/4) (S.scalar .width)
  have hm := Nat.mod_lt (S.scalar .index/4) width
  have valid : ValidAtoms M pointAtoms S := by
    simp [pointAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar,one,four]
    split_ifs <;> omega
  obtain ⟨run,hT⟩ := atoms_runs bounded pointAtoms valid
  refine ⟨applyAtoms pointAtoms S,run,hT,?_⟩
  simp [entry,pointAtoms,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,one,four]
  split_ifs <;> simp_all

structure Context (w s : ℕ) (S : State) : Prop where
  width : S.scalar .width=w
  special : S.scalar .special=s
  four : S.scalar .four=4

theorem program_runs (S : State) (M : ℕ) (bounded : S.Bounded M) (room : 4≤M)
    (width : 0<S.scalar .width) (size : S.scalar .links*S.scalar .width*4≤M) :
    ∃ t≤10*(S.scalar .links*S.scalar .width*4)+9,∃ T,
      Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧
      T.array .output=List.ofFn (fun i : Fin (S.scalar .links*S.scalar .width*4) =>
        entry (S.scalar .width) (S.scalar .special) i) := by
  let P := Context (S.scalar .width) (S.scalar .special)
  have pi : ∀ T x,P T → P (T.setScalar .index x) := by
    intro T x h; exact ⟨by simpa using h.width,by simpa using h.special,by simpa using h.four⟩
  have pt : ∀ T x,P T → P (T.setScalar .todo x) := by
    intro T x h; exact ⟨by simpa using h.width,by simpa using h.special,by simpa using h.four⟩
  have po : ∀ T xs,P T → P (T.setArray .output xs) := by
    intro T xs h; exact ⟨h.width,h.special,h.four⟩
  let N := S.scalar .links*S.scalar .width*4
  have body : ∀ i : Fin N,∀ T,P T → T.Bounded M → T.scalar .index=i.val →
      T.scalar .todo=N-i.val → T.scalar .one=1 → ∃ t≤6,∃ U,
        Runs (storageBound Reg Arr M) point T t U ∧ U.Bounded M ∧ P U ∧
        U.scalar .index=i.val ∧ U.scalar .todo=N-i.val ∧ U.scalar .one=1 ∧
        U.scalar .value=entry (S.scalar .width) (S.scalar .special) i ∧ U.array .output=T.array .output := by
    intro i T hT hb hi ht ho
    obtain ⟨U,run,hU,hv⟩ := point_runs T M hb (by omega) ho hT.four (by rwa [hT.width])
    exact ⟨6,by omega,U,run,hU,
      ⟨(run.scalar_eq_of_not_mem .width (by decide)).trans hT.width,
       (run.scalar_eq_of_not_mem .special (by decide)).trans hT.special,
       (run.scalar_eq_of_not_mem .four (by decide)).trans hT.four⟩,
      (run.scalar_eq_of_not_mem .index (by decide)).trans hi,
      (run.scalar_eq_of_not_mem .todo (by decide)).trans ht,
      (run.scalar_eq_of_not_mem .one (by decide)).trans ho,
      by simpa only [hT.width,hT.special,hi] using hv,
      run.array_eq_of_not_mem .output (by decide)⟩
  have valid : ValidAtoms M prelude S := by
    simp [prelude,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar]
    omega
  obtain ⟨preRun,hU⟩ := atoms_runs bounded prelude valid
  let U := applyAtoms prelude S
  have hu : P U := by refine ⟨?_,?_,?_⟩ <;> simp [U,prelude,applyAtoms,Atom.apply,Store.setScalar]
  obtain ⟨t,ht,T,run,hT,_,hout⟩ := ArrayTabulate.tabulate_runs
    Reg.index Reg.todo Reg.count Reg.one Reg.zero Reg.value Arr.output point
    (fun i : Fin N => entry (S.scalar .width) (S.scalar .special) i)
    P M 6 pi pt po (by decide) (by decide) (by decide) body U hU hu
    (by simp [U,prelude,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,N])
    (by simp [U,prelude,applyAtoms,Atom.apply,Store.setScalar])
    (by simp [U,prelude,applyAtoms,Atom.apply,Store.setScalar])
  exact ⟨5+t,by omega,T,.seq preRun run,hT,hout⟩

end GroupWL.MachinePrograms.SquareCharges
