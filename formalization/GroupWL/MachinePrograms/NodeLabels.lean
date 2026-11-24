import GroupWL.MachinePrograms.ArrayTabulate
import GroupWL.MachinePrograms.NatArrayFrames

/-! Expand comparison domains to the real and private-wire node label table. -/
namespace GroupWL.MachinePrograms.NodeLabels
open NatArrayLanguage
set_option maxHeartbeats 2000000

inductive Reg where
  | types | comparisons | width | wireSteps | nodes | total | index | todo | one | two | zero
  | pair | a | node | coordinate | flag | comparison | quotient | position | value
  deriving DecidableEq,Fintype
inductive Arr where
  | domain | output
  deriving DecidableEq,Fintype
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def entry (xs : List ℕ) (types width wireSteps index : ℕ) : ℕ :=
  let node := index/2/width
  if node<types then 1 else
    xs[2*((node-types)/wireSteps*width+index/2%width)+index%2]?.getD 0
def splitAtoms : List (Atom Reg Arr) := [
  .divmod .pair .a .index .two,.divmod .node .coordinate .pair .width,
  .binary .lt .flag .node .types]
def wireAtoms : List (Atom Reg Arr) := [
  .binary .sub .node .node .types,.divmod .comparison .quotient .node .wireSteps,
  .binary .mul .position .comparison .width,.binary .add .position .position .coordinate,
  .binary .mul .position .position .two,.binary .add .position .position .a,
  .read .value .domain .position]
def point : Code := .seq (atoms splitAtoms)
  (.branch .flag (.atom (.const .value 1)) (atoms wireAtoms))
def program : Code := .seq (atoms [
  .const .one 1,.const .two 2,.const .zero 0,
  .binary .mul .nodes .comparisons .wireSteps,.binary .add .nodes .nodes .types,
  .binary .mul .total .nodes .width,.binary .mul .total .total .two])
  (ArrayTabulate.tabulate .index .todo .total .one .zero .value .output point)

theorem point_runs (S : State) (M : ℕ) (bounded : S.Bounded M)
    (room : 1≤M) (two : S.scalar .two=2) (steps : 0<S.scalar .wireSteps)
    (input : (S.array .domain).length=2*(S.scalar .comparisons*S.scalar .width))
    (index : S.scalar .index<(S.scalar .types+S.scalar .comparisons*S.scalar .wireSteps)*S.scalar .width*2) :
    ∃ t≤11,∃ T,Runs (storageBound Reg Arr M) point S t T ∧ T.Bounded M ∧
      T.scalar .value=entry (S.array .domain) (S.scalar .types) (S.scalar .width)
        (S.scalar .wireSteps) (S.scalar .index) := by
  have hprod : 0<(S.scalar .types+S.scalar .comparisons*S.scalar .wireSteps)*S.scalar .width := by nlinarith
  have hw : 0<S.scalar .width := Nat.pos_of_mul_pos_left hprod
  have hq : S.scalar .index/2<(S.scalar .types+S.scalar .comparisons*S.scalar .wireSteps)*S.scalar .width :=
    (Nat.div_lt_iff_lt_mul (by decide : 0<2)).mpr index
  have hn : S.scalar .index/2/S.scalar .width<S.scalar .types+S.scalar .comparisons*S.scalar .wireSteps :=
    (Nat.div_lt_iff_lt_mul hw).mpr hq
  have hc := Nat.mod_lt (S.scalar .index/2) hw
  have ha : S.scalar .index%2<2 := by omega
  have valid : ValidAtoms M splitAtoms S := by
    simp [splitAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar,two]
    exact ⟨hw,by split_ifs <;> omega⟩
  obtain ⟨pre,hU⟩ := atoms_runs bounded splitAtoms valid
  let U := applyAtoms splitAtoms S
  have hf : U.scalar .flag=if S.scalar .index/2/S.scalar .width<S.scalar .types then 1 else 0 := by
    simp [U,splitAtoms,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,two]
  by_cases h : S.scalar .index/2/S.scalar .width<S.scalar .types
  · have last := atom_runs hU (.const Reg.value 1) trivial room
    refine ⟨5,by omega,U.setScalar .value 1,.seq pre (.branch_nonzero (by rw [hf]; simp [h]) last),
      hU.setScalar .value room,?_⟩
    simp [entry,h]
  · have hcomp : (S.scalar .index/2/S.scalar .width-S.scalar .types)/S.scalar .wireSteps<S.scalar .comparisons := by
      apply (Nat.div_lt_iff_lt_mul steps).mpr
      omega
    have haddr : 2*((S.scalar .index/2/S.scalar .width-S.scalar .types)/S.scalar .wireSteps*S.scalar .width+
        S.scalar .index/2%S.scalar .width)+S.scalar .index%2<(S.array .domain).length := by
      have hm := Nat.mul_le_mul_right (S.scalar .width)
        (show (S.scalar .index/2/S.scalar .width-S.scalar .types)/S.scalar .wireSteps+1≤S.scalar .comparisons by omega)
      rw [input]
      nlinarith
    have hlen := bounded.2.1 Arr.domain
    have hnode : S.scalar .index/2/S.scalar .width≤M :=
      (Nat.div_le_self _ _).trans ((Nat.div_le_self _ _).trans (bounded.1 .index))
    have wireValid : ValidAtoms M wireAtoms U := by
      simp [wireAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
        Store.setScalar,U,splitAtoms,applyAtoms,two,Nat.mul_comm]
      simp [Nat.mul_comm] at haddr
      exact ⟨by omega,steps,by nlinarith,by nlinarith,by nlinarith,by omega,haddr⟩
    obtain ⟨last,hT⟩ := atoms_runs hU wireAtoms wireValid
    refine ⟨11,by omega,applyAtoms wireAtoms U,.seq pre (.branch_zero (by rw [hf]; simp [h]) last),hT,?_⟩
    simp [applyAtoms,wireAtoms,U,splitAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,two,entry,h,Nat.mul_comm]

structure Context (a b r steps : ℕ) (xs : List ℕ) (S : State) : Prop where
  types : S.scalar .types=a
  comparisons : S.scalar .comparisons=b
  width : S.scalar .width=r
  wireSteps : S.scalar .wireSteps=steps
  two : S.scalar .two=2
  domain : S.array .domain=xs

theorem program_runs (S : State) (M : ℕ) (bounded : S.Bounded M) (room : 2≤M)
    (steps : 0<S.scalar .wireSteps)
    (nodes : S.scalar .types+S.scalar .comparisons*S.scalar .wireSteps≤M)
    (size : (S.scalar .types+S.scalar .comparisons*S.scalar .wireSteps)*S.scalar .width*2≤M)
    (input : (S.array .domain).length=2*(S.scalar .comparisons*S.scalar .width)) :
    ∃ t≤15*((S.scalar .types+S.scalar .comparisons*S.scalar .wireSteps)*S.scalar .width*2)+11,∃ T,
      Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧
      T.array .output=List.ofFn (fun i : Fin ((S.scalar .types+S.scalar .comparisons*S.scalar .wireSteps)*S.scalar .width*2) =>
        entry (S.array .domain) (S.scalar .types) (S.scalar .width) (S.scalar .wireSteps) i) := by
  let P := Context (S.scalar .types) (S.scalar .comparisons) (S.scalar .width)
    (S.scalar .wireSteps) (S.array .domain)
  have pi : ∀ T x,P T → P (T.setScalar .index x) := by
    intro T x h
    exact ⟨by simpa using h.types,by simpa using h.comparisons,by simpa using h.width,
      by simpa using h.wireSteps,by simpa using h.two,h.domain⟩
  have pt : ∀ T x,P T → P (T.setScalar .todo x) := by
    intro T x h
    exact ⟨by simpa using h.types,by simpa using h.comparisons,by simpa using h.width,
      by simpa using h.wireSteps,by simpa using h.two,h.domain⟩
  have po : ∀ T xs,P T → P (T.setArray .output xs) := by
    intro T xs h
    exact ⟨h.types,h.comparisons,h.width,h.wireSteps,h.two,by simpa using h.domain⟩
  let N := (S.scalar .types+S.scalar .comparisons*S.scalar .wireSteps)*S.scalar .width*2
  have body : ∀ i : Fin N,∀ T,P T → T.Bounded M → T.scalar .index=i.val →
      T.scalar .todo=N-i.val → T.scalar .one=1 → ∃ t≤11,∃ U,
        Runs (storageBound Reg Arr M) point T t U ∧ U.Bounded M ∧ P U ∧
        U.scalar .index=i.val ∧ U.scalar .todo=N-i.val ∧ U.scalar .one=1 ∧
        U.scalar .value=entry (S.array .domain) (S.scalar .types) (S.scalar .width) (S.scalar .wireSteps) i ∧
        U.array .output=T.array .output := by
    intro i T hT hb hi ht ho
    obtain ⟨t,htime,U,run,hU,hv⟩ := point_runs T M hb (by omega) hT.two
      (by rwa [hT.wireSteps]) (by rwa [hT.domain,hT.comparisons,hT.width])
      (by rw [hi,hT.types,hT.comparisons,hT.wireSteps,hT.width]; exact i.isLt)
    have hu : P U := ⟨(run.scalar_eq_of_not_mem .types (by decide)).trans hT.types,
      (run.scalar_eq_of_not_mem .comparisons (by decide)).trans hT.comparisons,
      (run.scalar_eq_of_not_mem .width (by decide)).trans hT.width,
      (run.scalar_eq_of_not_mem .wireSteps (by decide)).trans hT.wireSteps,
      (run.scalar_eq_of_not_mem .two (by decide)).trans hT.two,
      (run.array_eq_of_not_mem .domain (by decide)).trans hT.domain⟩
    exact ⟨t,htime,U,run,hU,hu,(run.scalar_eq_of_not_mem .index (by decide)).trans hi,
      (run.scalar_eq_of_not_mem .todo (by decide)).trans ht,
      (run.scalar_eq_of_not_mem .one (by decide)).trans ho,
      by simpa only [hT.domain,hT.types,hT.width,hT.wireSteps,hi] using hv,
      run.array_eq_of_not_mem .output (by decide)⟩
  let pre : List (Atom Reg Arr) := [
    .const .one 1,.const .two 2,.const .zero 0,
    .binary .mul .nodes .comparisons .wireSteps,.binary .add .nodes .nodes .types,
    .binary .mul .total .nodes .width,.binary .mul .total .total .two]
  have valid : ValidAtoms M pre S := by
    simp [pre,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar]
    exact ⟨by omega,room,by omega,by omega,by nlinarith,by nlinarith⟩
  obtain ⟨preRun,hU⟩ := atoms_runs bounded pre valid
  let U := applyAtoms pre S
  have hu : P U := by
    refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> simp [U,pre,applyAtoms,Atom.apply,Store.setScalar]
  obtain ⟨t,ht,T,run,hT,_,hout⟩ := ArrayTabulate.tabulate_runs
    Reg.index Reg.todo Reg.total Reg.one Reg.zero Reg.value Arr.output point
    (fun i : Fin N => entry (S.array .domain) (S.scalar .types) (S.scalar .width) (S.scalar .wireSteps) i)
    P M 11 pi pt po (by decide) (by decide) (by decide) body U hU hu
    (by simp [U,pre,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,N,Nat.add_comm])
    (by simp [U,pre,applyAtoms,Atom.apply,Store.setScalar])
    (by simp [U,pre,applyAtoms,Atom.apply,Store.setScalar])
  exact ⟨7+t,by omega,T,.seq preRun run,hT,hout⟩

end GroupWL.MachinePrograms.NodeLabels
