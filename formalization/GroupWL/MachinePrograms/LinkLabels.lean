import GroupWL.MachinePrograms.LinkIndex
import GroupWL.MachinePrograms.NatArrayComponents
import GroupWL.MachinePrograms.ArrayTabulate

/-! Materialize the permitted labels of every coded private-wire link. -/
namespace GroupWL.MachinePrograms.LinkLabels
open NatArrayLanguage
set_option maxHeartbeats 2000000

inductive WorkReg where
  | width | links | total | index | todo | one | two | zero | pair | label | coordinate | position | value
  deriving DecidableEq,Fintype
inductive WorkArr where
  | domain | output
  deriving DecidableEq,Fintype
abbrev Reg := LinkIndex.Reg⊕WorkReg
abbrev Arr := LinkIndex.Arr⊕WorkArr
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr
abbrev lr : LinkIndex.Reg→Reg := Sum.inl
abbrev wr : WorkReg→Reg := Sum.inr
abbrev wa : WorkArr→Arr := Sum.inr

def entry (xs : List ℕ) (e L r index : ℕ) : ℕ :=
  xs[2*(LinkIndex.comparison e L (index/2/r)*r+index/2%r)+index%2]?.getD 0
def splitAtoms : List (Atom Reg Arr) := [
  .divmod (wr .pair) (wr .label) (wr .index) (wr .two),
  .divmod (lr .link) (wr .coordinate) (wr .pair) (wr .width)]
def readAtoms : List (Atom Reg Arr) := [
  .binary .mul (wr .position) (lr .comparison) (wr .width),
  .binary .add (wr .position) (wr .position) (wr .coordinate),
  .binary .mul (wr .position) (wr .position) (wr .two),
  .binary .add (wr .position) (wr .position) (wr .label),
  .read (wr .value) (wa .domain) (wr .position)]
def point : Code := .seq (atoms splitAtoms)
  (.seq (LinkIndex.program.map Sum.inl Sum.inl) (atoms readAtoms))
def prelude : List (Atom Reg Arr) := [
  .const (wr .one) 1,.const (wr .two) 2,.const (wr .zero) 0,
  .binary .mul (wr .links) (lr .comparisons) (lr .length),
  .binary .add (wr .links) (wr .links) (lr .comparisons),
  .binary .add (wr .links) (wr .links) (lr .comparisons),
  .binary .mul (wr .total) (wr .links) (wr .width),
  .binary .mul (wr .total) (wr .total) (wr .two)]
def program : Code := .seq (atoms prelude)
  (ArrayTabulate.tabulate (wr .index) (wr .todo) (wr .total) (wr .one) (wr .zero)
    (wr .value) (wa .output) point)

theorem point_runs (S : State) (M : ℕ) (bounded : S.Bounded M) (room : 2≤M)
    (two : S.scalar (wr .two)=2) (positive : 0<S.scalar (lr .length))
    (small : S.scalar (lr .comparisons)+S.scalar (lr .comparisons)*S.scalar (lr .length)≤M)
    (input : (S.array (wa .domain)).length=2*(S.scalar (lr .comparisons)*S.scalar (wr .width)))
    (index : S.scalar (wr .index)<
      (S.scalar (lr .comparisons)+S.scalar (lr .comparisons)*S.scalar (lr .length)+S.scalar (lr .comparisons))*S.scalar (wr .width)*2) :
    ∃ t≤19,∃ T,Runs (storageBound Reg Arr M) point S t T ∧ T.Bounded M ∧
      T.scalar (wr .value)=entry (S.array (wa .domain)) (S.scalar (lr .comparisons))
        (S.scalar (lr .length)) (S.scalar (wr .width)) (S.scalar (wr .index)) := by
  let links := S.scalar (lr .comparisons)+S.scalar (lr .comparisons)*S.scalar (lr .length)+S.scalar (lr .comparisons)
  have hprod : 0<links*S.scalar (wr .width) := by change 0<_*_; dsimp [links]; nlinarith
  have hw : 0<S.scalar (wr .width) := Nat.pos_of_mul_pos_left hprod
  have hq : S.scalar (wr .index)/2<links*S.scalar (wr .width) :=
    (Nat.div_lt_iff_lt_mul (by decide : 0<2)).mpr index
  have hl : S.scalar (wr .index)/2/S.scalar (wr .width)<links := (Nat.div_lt_iff_lt_mul hw).mpr hq
  have hc := Nat.mod_lt (S.scalar (wr .index)/2) hw
  have ha : S.scalar (wr .index)%2<2 := by omega
  have valid : ValidAtoms M splitAtoms S := by
    simp [splitAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,Store.setScalar,two,hw]
  obtain ⟨pre,hU⟩ := atoms_runs bounded splitAtoms valid
  let U := applyAtoms splitAtoms S
  have ue : U.left.scalar .comparisons=S.scalar (lr .comparisons) := by
    simp [U,splitAtoms,applyAtoms,Atom.apply,Store.left,Store.setScalar]
  have uL : U.left.scalar .length=S.scalar (lr .length) := by
    simp [U,splitAtoms,applyAtoms,Atom.apply,Store.left,Store.setScalar]
  have ul : U.left.scalar .link=S.scalar (wr .index)/2/S.scalar (wr .width) := by
    simp [U,splitAtoms,applyAtoms,Atom.apply,Store.left,Store.setScalar,two]
  obtain ⟨t,ht,X,run,hX,_,xcomp,_⟩ := LinkIndex.program_runs U.left M hU.left room
    (by rwa [uL]) (by rwa [ue,uL])
  rw [ue,uL,ul] at xcomp
  let V := X.join U.right
  have client : Runs (storageBound Reg Arr M) (LinkIndex.program.map Sum.inl Sum.inl) U t V := run.left_bounded hU
  have hV : V.Bounded M := hX.join hU.right
  have vc : V.scalar (lr .comparison)=LinkIndex.comparison (S.scalar (lr .comparisons))
      (S.scalar (lr .length)) (S.scalar (wr .index)/2/S.scalar (wr .width)) := xcomp
  have vs (r : WorkReg) : V.scalar (wr r)=U.scalar (wr r) := rfl
  have va : V.array (wa .domain)=S.array (wa .domain) := rfl
  have hcomp := LinkIndex.comparison_lt positive hl
  have haddr : 2*(LinkIndex.comparison (S.scalar (lr .comparisons)) (S.scalar (lr .length))
      (S.scalar (wr .index)/2/S.scalar (wr .width))*S.scalar (wr .width)+S.scalar (wr .index)/2%S.scalar (wr .width))+
      S.scalar (wr .index)%2<(S.array (wa .domain)).length := by
    have hm := Nat.mul_le_mul_right (S.scalar (wr .width)) (Nat.succ_le_of_lt hcomp)
    rw [input]
    nlinarith
  have hlen := bounded.2.1 (wa .domain)
  have readValid : ValidAtoms M readAtoms V := by
    simp [readAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,vc,vs,va,U,splitAtoms,applyAtoms,two,Nat.mul_comm]
    simp [Nat.mul_comm] at haddr
    exact ⟨by nlinarith,by nlinarith,by nlinarith,by omega,haddr⟩
  obtain ⟨last,hT⟩ := atoms_runs hV readAtoms readValid
  refine ⟨2+(t+5),by omega,applyAtoms readAtoms V,.seq pre (.seq client last),hT,?_⟩
  simp [applyAtoms,readAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,vc,vs,va,U,splitAtoms,two,entry,Nat.mul_comm]

structure Context (e L r : ℕ) (xs : List ℕ) (S : State) : Prop where
  comparisons : S.scalar (lr .comparisons)=e
  length : S.scalar (lr .length)=L
  width : S.scalar (wr .width)=r
  two : S.scalar (wr .two)=2
  domain : S.array (wa .domain)=xs

theorem program_runs (S : State) (M : ℕ) (bounded : S.Bounded M) (room : 2≤M)
    (positive : 0<S.scalar (lr .length))
    (links : S.scalar (lr .comparisons)+S.scalar (lr .comparisons)*S.scalar (lr .length)+S.scalar (lr .comparisons)≤M)
    (size : (S.scalar (lr .comparisons)+S.scalar (lr .comparisons)*S.scalar (lr .length)+S.scalar (lr .comparisons))*S.scalar (wr .width)*2≤M)
    (input : (S.array (wa .domain)).length=2*(S.scalar (lr .comparisons)*S.scalar (wr .width))) :
    ∃ t≤23*((S.scalar (lr .comparisons)+S.scalar (lr .comparisons)*S.scalar (lr .length)+S.scalar (lr .comparisons))*S.scalar (wr .width)*2)+12,∃ T,
      Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧
      T.array (wa .output)=List.ofFn (fun i : Fin ((S.scalar (lr .comparisons)+S.scalar (lr .comparisons)*S.scalar (lr .length)+S.scalar (lr .comparisons))*S.scalar (wr .width)*2) =>
        entry (S.array (wa .domain)) (S.scalar (lr .comparisons)) (S.scalar (lr .length)) (S.scalar (wr .width)) i) := by
  let P := Context (S.scalar (lr .comparisons)) (S.scalar (lr .length)) (S.scalar (wr .width)) (S.array (wa .domain))
  have pi : ∀ T x,P T → P (T.setScalar (wr .index) x) := by
    intro T x h
    exact ⟨by simpa using h.comparisons,by simpa using h.length,by simpa using h.width,
      by simpa using h.two,h.domain⟩
  have pt : ∀ T x,P T → P (T.setScalar (wr .todo) x) := by
    intro T x h
    exact ⟨by simpa using h.comparisons,by simpa using h.length,by simpa using h.width,
      by simpa using h.two,h.domain⟩
  have po : ∀ T xs,P T → P (T.setArray (wa .output) xs) := by
    intro T xs h
    exact ⟨h.comparisons,h.length,h.width,h.two,by simpa using h.domain⟩
  let N := (S.scalar (lr .comparisons)+S.scalar (lr .comparisons)*S.scalar (lr .length)+S.scalar (lr .comparisons))*S.scalar (wr .width)*2
  have body : ∀ i : Fin N,∀ T,P T → T.Bounded M → T.scalar (wr .index)=i.val →
      T.scalar (wr .todo)=N-i.val → T.scalar (wr .one)=1 → ∃ t≤19,∃ U,
        Runs (storageBound Reg Arr M) point T t U ∧ U.Bounded M ∧ P U ∧
        U.scalar (wr .index)=i.val ∧ U.scalar (wr .todo)=N-i.val ∧ U.scalar (wr .one)=1 ∧
        U.scalar (wr .value)=entry (S.array (wa .domain)) (S.scalar (lr .comparisons)) (S.scalar (lr .length)) (S.scalar (wr .width)) i ∧
        U.array (wa .output)=T.array (wa .output) := by
    intro i T hT hb hi ht ho
    obtain ⟨t,htime,U,run,hU,hv⟩ := point_runs T M hb room hT.two
      (by rwa [hT.length]) (by rw [hT.comparisons,hT.length]; omega)
      (by rwa [hT.domain,hT.comparisons,hT.width])
      (by rw [hi,hT.comparisons,hT.length,hT.width]; exact i.isLt)
    have hu : P U := ⟨(run.scalar_eq_of_not_mem (lr .comparisons) (by decide)).trans hT.comparisons,
      (run.scalar_eq_of_not_mem (lr .length) (by decide)).trans hT.length,
      (run.scalar_eq_of_not_mem (wr .width) (by decide)).trans hT.width,
      (run.scalar_eq_of_not_mem (wr .two) (by decide)).trans hT.two,
      (run.array_eq_of_not_mem (wa .domain) (by decide)).trans hT.domain⟩
    exact ⟨t,htime,U,run,hU,hu,(run.scalar_eq_of_not_mem (wr .index) (by decide)).trans hi,
      (run.scalar_eq_of_not_mem (wr .todo) (by decide)).trans ht,
      (run.scalar_eq_of_not_mem (wr .one) (by decide)).trans ho,
      by simpa only [hT.domain,hT.comparisons,hT.length,hT.width,hi] using hv,
      run.array_eq_of_not_mem (wa .output) (by decide)⟩
  have valid : ValidAtoms M prelude S := by
    simp [prelude,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar]
    exact ⟨by omega,room,by omega,by omega,by omega,by nlinarith,by nlinarith⟩
  obtain ⟨preRun,hU⟩ := atoms_runs bounded prelude valid
  let U := applyAtoms prelude S
  have hu : P U := by
    refine ⟨?_,?_,?_,?_,?_⟩ <;> simp [U,prelude,applyAtoms,Atom.apply,Store.setScalar]
  obtain ⟨t,ht,T,run,hT,_,hout⟩ := ArrayTabulate.tabulate_runs
    (wr .index) (wr .todo) (wr .total) (wr .one) (wr .zero) (wr .value) (wa .output) point
    (fun i : Fin N => entry (S.array (wa .domain)) (S.scalar (lr .comparisons)) (S.scalar (lr .length)) (S.scalar (wr .width)) i)
    P M 19 pi pt po (by decide) (by decide) (by decide) body U hU hu
    (by simp [U,prelude,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,N,Nat.add_comm])
    (by simp [U,prelude,applyAtoms,Atom.apply,Store.setScalar])
    (by simp [U,prelude,applyAtoms,Atom.apply,Store.setScalar])
  exact ⟨8+t,by omega,T,.seq preRun run,hT,hout⟩

end GroupWL.MachinePrograms.LinkLabels
