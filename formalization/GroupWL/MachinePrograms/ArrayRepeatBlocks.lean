import GroupWL.MachinePrograms.ArrayTabulate
import GroupWL.MachinePrograms.NatArrayFrames

/-! Repeat each fixed-width block of an array a specified number of times. -/
namespace GroupWL.MachinePrograms.ArrayRepeatBlocks
open NatArrayLanguage
set_option maxHeartbeats 1500000

inductive Reg where
  | blocks | width | repeats | inputSize | count | index | todo | one | zero
  | quotient | remainder | block | unused | position | value
  deriving DecidableEq,Fintype
inductive Arr where
  | input | output
  deriving DecidableEq,Fintype
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def entry (xs : List ℕ) (width repeats index : ℕ) : ℕ :=
  xs[(index/width/repeats)*width+index%width]?.getD 0
def pointAtoms : List (Atom Reg Arr) := [
  .divmod .quotient .remainder .index .width,
  .divmod .block .unused .quotient .repeats,
  .binary .mul .position .block .width,
  .binary .add .position .position .remainder,
  .read .value .input .position]
def point : Code := atoms pointAtoms
def prelude : List (Atom Reg Arr) := [
  .const .one 1,.const .zero 0,.binary .mul .inputSize .blocks .width,
  .binary .mul .count .inputSize .repeats]
def program : Code := .seq (atoms prelude)
  (ArrayTabulate.tabulate .index .todo .count .one .zero .value .output point)

theorem point_runs (S : State) (M : ℕ) (bounded : S.Bounded M)
    (input : (S.array .input).length=S.scalar .blocks*S.scalar .width)
    (index : S.scalar .index<S.scalar .blocks*S.scalar .width*S.scalar .repeats) :
    ∃ T,Runs (storageBound Reg Arr M) point S 5 T ∧ T.Bounded M ∧
      T.scalar .value=entry (S.array .input) (S.scalar .width) (S.scalar .repeats) (S.scalar .index) := by
  have width : 0<S.scalar .width := by
    by_contra h
    have hz : S.scalar .width=0 := by omega
    simp [hz] at index
  have repeats : 0<S.scalar .repeats := by
    by_contra h
    have hz : S.scalar .repeats=0 := by omega
    simp [hz] at index
  have hdiv : S.scalar .index/S.scalar .width<S.scalar .blocks*S.scalar .repeats := by
    apply (Nat.div_lt_iff_lt_mul width).2
    nlinarith [index]
  have hblock : S.scalar .index/S.scalar .width/S.scalar .repeats<S.scalar .blocks :=
    (Nat.div_lt_iff_lt_mul repeats).2 hdiv
  have hmod := Nat.mod_lt (S.scalar .index) width
  have haddr : S.scalar .index/S.scalar .width/S.scalar .repeats*S.scalar .width+
      S.scalar .index%S.scalar .width<(S.array .input).length := by
    rw [input]
    have := Nat.mul_le_mul_right (S.scalar .width) (show S.scalar .index/S.scalar .width/S.scalar .repeats+1≤S.scalar .blocks by omega)
    nlinarith
  have hi := bounded.1 Reg.index
  have hq := Nat.div_le_self (S.scalar .index) (S.scalar .width)
  have hb := Nat.div_le_self (S.scalar .index/S.scalar .width) (S.scalar .repeats)
  have hm := Nat.mod_le (S.scalar .index/S.scalar .width) (S.scalar .repeats)
  have hl := bounded.2.1 Arr.input
  have valid : ValidAtoms M pointAtoms S := by
    simp [pointAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar]
    omega
  obtain ⟨run,hT⟩ := atoms_runs bounded pointAtoms valid
  exact ⟨applyAtoms pointAtoms S,run,hT,by simp [entry,applyAtoms,pointAtoms,Atom.apply,BinaryOp.eval,Store.setScalar]⟩

structure Context (b w r : ℕ) (xs : List ℕ) (S : State) : Prop where
  blocks : S.scalar .blocks=b
  width : S.scalar .width=w
  repeats : S.scalar .repeats=r
  input : S.array .input=xs

theorem program_runs (S : State) (M : ℕ) (bounded : S.Bounded M) (room : 1≤M)
    (input : (S.array .input).length=S.scalar .blocks*S.scalar .width)
    (size : S.scalar .blocks*S.scalar .width*S.scalar .repeats≤M) :
    ∃ t≤9*(S.scalar .blocks*S.scalar .width*S.scalar .repeats)+8,∃ T,
      Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧
      T.array .output=List.ofFn (fun i : Fin (S.scalar .blocks*S.scalar .width*S.scalar .repeats) =>
        entry (S.array .input) (S.scalar .width) (S.scalar .repeats) i) := by
  let P := Context (S.scalar .blocks) (S.scalar .width) (S.scalar .repeats) (S.array .input)
  have pi : ∀ T x,P T → P (T.setScalar .index x) := by
    intro T x h; exact ⟨by simpa using h.blocks,by simpa using h.width,by simpa using h.repeats,h.input⟩
  have pt : ∀ T x,P T → P (T.setScalar .todo x) := by
    intro T x h; exact ⟨by simpa using h.blocks,by simpa using h.width,by simpa using h.repeats,h.input⟩
  have po : ∀ T xs,P T → P (T.setArray .output xs) := by
    intro T xs h; exact ⟨h.blocks,h.width,h.repeats,by simpa using h.input⟩
  let N := S.scalar .blocks*S.scalar .width*S.scalar .repeats
  have body : ∀ i : Fin N,∀ T,P T → T.Bounded M → T.scalar .index=i.val →
      T.scalar .todo=N-i.val → T.scalar .one=1 → ∃ t≤5,∃ U,
        Runs (storageBound Reg Arr M) point T t U ∧ U.Bounded M ∧ P U ∧
        U.scalar .index=i.val ∧ U.scalar .todo=N-i.val ∧ U.scalar .one=1 ∧
        U.scalar .value=entry (S.array .input) (S.scalar .width) (S.scalar .repeats) i ∧
        U.array .output=T.array .output := by
    intro i T hT hb hi ht ho
    obtain ⟨U,run,hU,hv⟩ := point_runs T M hb (by rwa [hT.input,hT.blocks,hT.width])
      (by rw [hi,hT.blocks,hT.width,hT.repeats]; exact i.isLt)
    have hu : P U := ⟨(run.scalar_eq_of_not_mem .blocks (by decide)).trans hT.blocks,
      (run.scalar_eq_of_not_mem .width (by decide)).trans hT.width,
      (run.scalar_eq_of_not_mem .repeats (by decide)).trans hT.repeats,
      (run.array_eq_of_not_mem .input (by decide)).trans hT.input⟩
    exact ⟨5,by omega,U,run,hU,hu,(run.scalar_eq_of_not_mem .index (by decide)).trans hi,
      (run.scalar_eq_of_not_mem .todo (by decide)).trans ht,
      (run.scalar_eq_of_not_mem .one (by decide)).trans ho,
      by simpa only [hT.input,hT.width,hT.repeats,hi] using hv,
      run.array_eq_of_not_mem .output (by decide)⟩
  have inBound : S.scalar .blocks*S.scalar .width≤M := by
    rw [← input]; exact bounded.2.1 Arr.input
  have valid : ValidAtoms M prelude S := by
    simpa [prelude,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar] using
      (show 1≤M ∧ S.scalar .blocks*S.scalar .width≤M ∧ S.scalar .blocks*S.scalar .width*S.scalar .repeats≤M from ⟨room,inBound,size⟩)
  obtain ⟨preRun,hU⟩ := atoms_runs bounded prelude valid
  let U := applyAtoms prelude S
  have hu : P U := by refine ⟨?_,?_,?_,?_⟩ <;> simp [U,prelude,applyAtoms,Atom.apply,Store.setScalar]
  obtain ⟨t,ht,T,run,hT,_,hout⟩ := ArrayTabulate.tabulate_runs
    Reg.index Reg.todo Reg.count Reg.one Reg.zero Reg.value Arr.output point
    (fun i : Fin N => entry (S.array .input) (S.scalar .width) (S.scalar .repeats) i)
    P M 5 pi pt po (by decide) (by decide) (by decide) body U hU hu
    (by simp [U,prelude,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,N])
    (by simp [U,prelude,applyAtoms,Atom.apply,Store.setScalar])
    (by simp [U,prelude,applyAtoms,Atom.apply,Store.setScalar])
  exact ⟨4+t,by omega,T,.seq preRun run,hT,hout⟩

end GroupWL.MachinePrograms.ArrayRepeatBlocks
