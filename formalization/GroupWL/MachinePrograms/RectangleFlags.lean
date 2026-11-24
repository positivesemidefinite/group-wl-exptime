import GroupWL.MachinePrograms.ArrayTabulation
import GroupWL.MachinePrograms.NatArrayCountedLoops
import GroupWL.MachinePrograms.NatArrayFrames
import GroupWL.MachinePrograms.ArrayTabulate

/-! Enumerate pairs of permitted Boolean labels at consecutive cyclic coordinates. -/
namespace GroupWL.MachinePrograms.RectangleFlags
open NatArrayLanguage
set_option maxHeartbeats 2000000

inductive Reg where
  | rows | width | total | index | todo | one | two | four | zero
  | pair | bits | row | coordinate | a | b | next | quotient | base | position | left | right | value
  deriving DecidableEq,Fintype
inductive Arr where
  | labels | output
  deriving DecidableEq,Fintype
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def entry (xs : List ℕ) (width index : ℕ) : ℕ :=
  let row := index/4/width
  let coordinate := index/4%width
  (xs[2*(row*width+coordinate)+(index%4)/2]?).getD 0 *
    (xs[2*(row*width+(coordinate+1)%width)+(index%4)%2]?).getD 0

def pointAtoms : List (Atom Reg Arr) := [
  .divmod .pair .bits .index .four,.divmod .row .coordinate .pair .width,
  .divmod .a .b .bits .two,.binary .add .next .coordinate .one,
  .divmod .quotient .next .next .width,.binary .mul .base .row .width,
  .binary .add .position .base .coordinate,.binary .mul .position .position .two,
  .binary .add .position .position .a,.read .left .labels .position,
  .binary .add .position .base .next,.binary .mul .position .position .two,
  .binary .add .position .position .b,.read .right .labels .position,
  .binary .mul .value .left .right]
def point : Code := atoms pointAtoms
def program : Code := .seq (atoms [
  .const .one 1,.const .two 2,.const .four 4,.const .zero 0,
  .binary .mul .total .rows .width,.binary .mul .total .total .four])
  (ArrayTabulate.tabulate .index .todo .total .one .zero .value .output point)

theorem read_small {xs : List ℕ} (h : ∀x∈xs,x≤1) (i : ℕ) : (xs[i]?).getD 0≤1 := by
  cases he : xs[i]? with
  | none => simp
  | some x => exact h x (List.mem_of_getElem? he)

theorem entry_small {xs : List ℕ} (h : ∀x∈xs,x≤1) (w i : ℕ) : entry xs w i≤1 := by
  unfold entry
  have h₁ := read_small h (2*(i/4/w*w+i/4%w)+i%4/2)
  have h₂ := read_small h (2*(i/4/w*w+(i/4%w+1)%w)+i%4%2)
  nlinarith

theorem point_runs (S : State) (M : ℕ) (bounded : S.Bounded M)
    (one : S.scalar .one=1) (two : S.scalar .two=2) (four : S.scalar .four=4)
    (input : (S.array .labels).length=2*(S.scalar .rows*S.scalar .width))
    (index : S.scalar .index<S.scalar .rows*S.scalar .width*4)
    (values : ∀x∈S.array .labels,x≤1) :
    Runs (storageBound Reg Arr M) point S 15 (applyAtoms pointAtoms S) ∧
      (applyAtoms pointAtoms S).Bounded M ∧
      (applyAtoms pointAtoms S).scalar .value=entry (S.array .labels) (S.scalar .width) (S.scalar .index) ∧
      (applyAtoms pointAtoms S).array .output=S.array .output := by
  have hrw : 0<S.scalar .rows*S.scalar .width := by nlinarith
  have hw : 0<S.scalar .width := Nat.pos_of_mul_pos_left hrw
  have hq : S.scalar .index/4<S.scalar .rows*S.scalar .width :=
    (Nat.div_lt_iff_lt_mul (by decide : 0<4)).mpr index
  have hr : S.scalar .index/4/S.scalar .width<S.scalar .rows :=
    (Nat.div_lt_iff_lt_mul hw).mpr hq
  have hc := Nat.mod_lt (S.scalar .index/4) hw
  have hn := Nat.mod_lt (S.scalar .index/4%S.scalar .width+1) hw
  have ha : S.scalar .index%4/2<2 := by omega
  have hb : S.scalar .index%4%2<2 := by omega
  have hrow := Nat.mul_le_mul_right (S.scalar .width) (show S.scalar .index/4/S.scalar .width+1≤S.scalar .rows by omega)
  have hl : 2*(S.scalar .index/4/S.scalar .width*S.scalar .width+S.scalar .index/4%S.scalar .width)+S.scalar .index%4/2<(S.array .labels).length := by
    rw [input]; nlinarith
  have ht : 2*(S.scalar .index/4/S.scalar .width*S.scalar .width+(S.scalar .index/4%S.scalar .width+1)%S.scalar .width)+S.scalar .index%4%2<(S.array .labels).length := by
    rw [input]; nlinarith
  have hlen := bounded.2.1 Arr.labels
  have hwidth := bounded.1 Reg.width
  have h1 : 1≤M := by have := bounded.1 Reg.one; omega
  have hleft := read_small values (2*(S.scalar .index/4/S.scalar .width*S.scalar .width+S.scalar .index/4%S.scalar .width)+S.scalar .index%4/2)
  have hright := read_small values (2*(S.scalar .index/4/S.scalar .width*S.scalar .width+(S.scalar .index/4%S.scalar .width+1)%S.scalar .width)+S.scalar .index%4%2)
  simp [Nat.mul_comm] at hl ht hleft hright hn
  have valid : ValidAtoms M pointAtoms S := by
    simp [pointAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,one,two,four,Nat.mul_comm]
    exact ⟨hw,by omega,hw,by nlinarith,by nlinarith,by nlinarith,
      by omega,by simpa [Nat.mul_comm] using hl,by nlinarith,by nlinarith,
      by omega,by simpa [Nat.mul_comm] using ht,by nlinarith⟩
  obtain ⟨run,hT⟩ := atoms_runs bounded pointAtoms valid
  exact ⟨run,hT,by simp [applyAtoms,pointAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,
    one,two,four,entry,Nat.mul_comm],rfl⟩

structure Context (n r : ℕ) (xs : List ℕ) (S : State) : Prop where
  rows : S.scalar .rows=n
  width : S.scalar .width=r
  two : S.scalar .two=2
  four : S.scalar .four=4
  labels : S.array .labels=xs

theorem program_runs (S : State) (M : ℕ) (bounded : S.Bounded M)
    (room : 4≤M) (size : S.scalar .rows*S.scalar .width*4≤M)
    (input : (S.array .labels).length=2*(S.scalar .rows*S.scalar .width))
    (values : ∀x∈S.array .labels,x≤1) :
    ∃ t≤19*(S.scalar .rows*S.scalar .width*4)+10,∃ T,
      Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧
      T.array .output=List.ofFn (fun i : Fin (S.scalar .rows*S.scalar .width*4) =>
        entry (S.array .labels) (S.scalar .width) i) := by
  let P := Context (S.scalar .rows) (S.scalar .width) (S.array .labels)
  have pi : ∀ T x,P T → P (T.setScalar .index x) := by
    intro T x h
    exact ⟨by simpa using h.rows,by simpa using h.width,by simpa using h.two,
      by simpa using h.four,h.labels⟩
  have pt : ∀ T x,P T → P (T.setScalar .todo x) := by
    intro T x h
    exact ⟨by simpa using h.rows,by simpa using h.width,by simpa using h.two,
      by simpa using h.four,h.labels⟩
  have po : ∀ T xs,P T → P (T.setArray .output xs) := by
    intro T xs h
    exact ⟨h.rows,h.width,h.two,h.four,by simpa using h.labels⟩
  have body : ∀ i : Fin (S.scalar .rows*S.scalar .width*4),∀ T,P T → T.Bounded M →
      T.scalar .index=i.val → T.scalar .todo=S.scalar .rows*S.scalar .width*4-i.val →
      T.scalar .one=1 → ∃ t≤15,∃ U,Runs (storageBound Reg Arr M) point T t U ∧
        U.Bounded M ∧ P U ∧ U.scalar .index=i.val ∧
        U.scalar .todo=S.scalar .rows*S.scalar .width*4-i.val ∧ U.scalar .one=1 ∧
        U.scalar .value=entry (S.array .labels) (S.scalar .width) i ∧ U.array .output=T.array .output := by
    intro i T hT hb hi ht ho
    obtain ⟨run,hU,hv,ha⟩ := point_runs T M hb ho hT.two hT.four
      (by rwa [hT.labels,hT.rows,hT.width]) (by rw [hi,hT.rows,hT.width]; exact i.isLt)
      (by rwa [hT.labels])
    let U := applyAtoms pointAtoms T
    have hu : P U := ⟨(run.scalar_eq_of_not_mem .rows (by decide)).trans hT.rows,
      (run.scalar_eq_of_not_mem .width (by decide)).trans hT.width,
      (run.scalar_eq_of_not_mem .two (by decide)).trans hT.two,
      (run.scalar_eq_of_not_mem .four (by decide)).trans hT.four,
      (run.array_eq_of_not_mem .labels (by decide)).trans hT.labels⟩
    exact ⟨15,le_rfl,U,run,hU,hu,(run.scalar_eq_of_not_mem .index (by decide)).trans hi,
      (run.scalar_eq_of_not_mem .todo (by decide)).trans ht,
      (run.scalar_eq_of_not_mem .one (by decide)).trans ho,
      by simpa only [hT.labels,hT.width,hi] using hv,ha⟩
  let pre : List (Atom Reg Arr) := [.const .one 1,.const .two 2,.const .four 4,.const .zero 0,
    .binary .mul .total .rows .width,.binary .mul .total .total .four]
  have valid : ValidAtoms M pre S := by
    simp [pre,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar]
    exact ⟨by omega,by omega,room,by omega,size⟩
  obtain ⟨preRun,hU⟩ := atoms_runs bounded pre valid
  let U := applyAtoms pre S
  have hu : P U := by
    refine ⟨?_,?_,?_,?_,?_⟩ <;> simp [U,pre,applyAtoms,Atom.apply,Store.setScalar]
  obtain ⟨t,ht,T,run,hT,_,hout⟩ := ArrayTabulate.tabulate_runs
    Reg.index Reg.todo Reg.total Reg.one Reg.zero Reg.value Arr.output point
    (fun i : Fin (S.scalar .rows*S.scalar .width*4) => entry (S.array .labels) (S.scalar .width) i)
    P M 15 pi pt po (by decide) (by decide) (by decide) body U hU hu
    (by simp [U,pre,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar])
    (by simp [U,pre,applyAtoms,Atom.apply,Store.setScalar])
    (by simp [U,pre,applyAtoms,Atom.apply,Store.setScalar])
  exact ⟨6+t,by omega,T,.seq preRun run,hT,hout⟩

end GroupWL.MachinePrograms.RectangleFlags
