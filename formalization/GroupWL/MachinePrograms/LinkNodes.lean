import GroupWL.MachinePrograms.LinkIndex
import GroupWL.MachinePrograms.NatArrayComponents
import GroupWL.MachinePrograms.ArrayTabulate

/-! Explicit endpoint-node computation from a decoded private-wire link. -/
namespace GroupWL.MachinePrograms.LinkNodes
open NatArrayLanguage
set_option maxHeartbeats 2000000

inductive WorkReg where
  | types | base | wireSteps | left | right | flag | one | two | zero | count | todo
  deriving DecidableEq,Fintype
inductive WorkArr where
  | source | target | leftNodes | rightNodes
  deriving DecidableEq,Fintype
abbrev Reg := LinkIndex.Reg⊕WorkReg
abbrev Arr := LinkIndex.Arr⊕WorkArr
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr
abbrev lr : LinkIndex.Reg→Reg := Sum.inl
abbrev wr : WorkReg→Reg := Sum.inr
abbrev wa : WorkArr→Arr := Sum.inr

def leftNode (sources : List ℕ) (types e L i : ℕ) : ℕ :=
  if i<e then sources[i]?.getD 0
  else if i<e+e*L then types+(i-e)/L*(L+1)+(i-e)%L
  else types+(i-(e+e*L))*(L+1)+L
def rightNode (targets : List ℕ) (types e L i : ℕ) : ℕ :=
  if i<e then types+i*(L+1)
  else if i<e+e*L then types+(i-e)/L*(L+1)+(i-e)%L+1
  else targets[i-(e+e*L)]?.getD 0

def pointPrelude : List (Atom Reg Arr) := [
  .const (wr .one) 1,.const (wr .zero) 0,
  .binary .add (wr .wireSteps) (lr .length) (wr .one),
  .binary .mul (wr .base) (lr .comparison) (wr .wireSteps),
  .binary .add (wr .base) (wr .base) (wr .types),
  .copy (wr .left) (wr .base),.copy (wr .right) (wr .base),
  .binary .eq (wr .flag) (lr .kind) (wr .zero)]
def middleAtoms : List (Atom Reg Arr) := [
  .binary .add (wr .left) (wr .base) (lr .offset),
  .binary .add (wr .right) (wr .left) (wr .one)]
def lastAtoms : List (Atom Reg Arr) := [
  .binary .add (wr .left) (wr .base) (lr .length),
  .read (wr .right) (wa .target) (lr .comparison)]
def endpoints : Code := .seq (atoms pointPrelude)
  (.branch (wr .flag) (.atom (.read (wr .left) (wa .source) (lr .comparison)))
    (.seq (.atom (.binary .eq (wr .flag) (lr .kind) (wr .one)))
      (.branch (wr .flag) (atoms middleAtoms) (atoms lastAtoms))))
def point : Code := .seq (LinkIndex.program.map Sum.inl Sum.inl) endpoints

theorem endpoint_bounds {e L i types : ℕ} {sources targets : List ℕ}
    (positive : 0<L) (valid : i<e+e*L+e)
    (sourceLength : sources.length=e) (targetLength : targets.length=e)
    (sourceValues : ∀x∈sources,x<types) (targetValues : ∀x∈targets,x<types) :
    leftNode sources types e L i<types+e*(L+1) ∧
      rightNode targets types e L i<types+e*(L+1) := by
  have hread {xs : List ℕ} {j : ℕ} (hl : xs.length=e) (hv : ∀x∈xs,x<types) (hj : j<e) :
      xs[j]?.getD 0<types := by
    have hx : j<xs.length := by omega
    rw [List.getElem?_eq_getElem hx]
    exact hv _ (List.getElem_mem hx)
  unfold leftNode rightNode
  split_ifs with h₁ h₂
  · have h := hread sourceLength sourceValues h₁
    have hm := Nat.mul_le_mul_right (L+1) (show i+1≤e by omega)
    constructor <;> nlinarith
  · have hc : (i-e)/L<e := (Nat.div_lt_iff_lt_mul positive).mpr (by omega)
    have ho := Nat.mod_lt (i-e) positive
    have hm := Nat.mul_le_mul_right (L+1) (show (i-e)/L+1≤e by omega)
    constructor <;> nlinarith
  · have hc : i-(e+e*L)<e := by omega
    have h := hread targetLength targetValues hc
    have hm := Nat.mul_le_mul_right (L+1) (show i-(e+e*L)+1≤e by omega)
    constructor <;> nlinarith

theorem endpoints_runs (S : State) (M e L i types : ℕ) (sources targets : List ℕ)
    (bounded : S.Bounded M) (room : 2≤M) (positive : 0<L) (valid : i<e+e*L+e)
    (nodes : types+e*(L+1)≤M) (hL : S.scalar (lr .length)=L)
    (htypes : S.scalar (wr .types)=types)
    (hkind : S.scalar (lr .kind)=LinkIndex.kind e L i)
    (hcomp : S.scalar (lr .comparison)=LinkIndex.comparison e L i)
    (hoff : S.scalar (lr .offset)=LinkIndex.offset e L i)
    (hsource : S.array (wa .source)=sources) (htarget : S.array (wa .target)=targets)
    (sourceLength : sources.length=e) (targetLength : targets.length=e) :
    ∃ t≤13,∃ T,Runs (storageBound Reg Arr M) endpoints S t T ∧ T.Bounded M ∧
      T.scalar (wr .left)=leftNode sources types e L i ∧
      T.scalar (wr .right)=rightNode targets types e L i ∧ T.scalar (wr .one)=1 := by
  have hc := LinkIndex.comparison_lt positive valid
  have he : 0<e := by
    by_contra h
    have he : e=0 := by omega
    simp [he] at valid
  have hbase := Nat.mul_le_mul_right (L+1) (Nat.succ_le_of_lt hc)
  have hsteps : L+1≤M := by have := Nat.mul_le_mul_right (L+1) he; nlinarith
  have preValid : ValidAtoms M pointPrelude S := by
    simp [pointPrelude,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,hL,htypes,hcomp,hkind]
    exact ⟨by omega,hsteps,by nlinarith,by nlinarith,by split_ifs <;> omega⟩
  obtain ⟨pre,hU⟩ := atoms_runs bounded pointPrelude preValid
  let U := applyAtoms pointPrelude S
  have ub : U.scalar (wr .base)=types+LinkIndex.comparison e L i*(L+1) := by
    simp [U,applyAtoms,pointPrelude,Atom.apply,BinaryOp.eval,Store.setScalar,hL,htypes,hcomp,Nat.add_comm]
  have uk : U.scalar (lr .kind)=LinkIndex.kind e L i := by
    simpa [U,applyAtoms,pointPrelude,Atom.apply,Store.setScalar] using hkind
  have ucomp : U.scalar (lr .comparison)=LinkIndex.comparison e L i := by
    simpa [U,applyAtoms,pointPrelude,Atom.apply,Store.setScalar] using hcomp
  have uoff : U.scalar (lr .offset)=LinkIndex.offset e L i := by
    simpa [U,applyAtoms,pointPrelude,Atom.apply,Store.setScalar] using hoff
  have uf : U.scalar (wr .flag)=if LinkIndex.kind e L i=0 then 1 else 0 := by
    simp [U,applyAtoms,pointPrelude,Atom.apply,BinaryOp.eval,Store.setScalar,hkind]
  have uone : U.scalar (wr .one)=1 := by simp [U,applyAtoms,pointPrelude,Atom.apply,Store.setScalar]
  have ulength : U.scalar (lr .length)=L := by simpa [U,applyAtoms,pointPrelude,Atom.apply,Store.setScalar] using hL
  have us : U.array (wa .source)=sources := hsource
  have ut : U.array (wa .target)=targets := htarget
  by_cases hfirst : i<e
  · have hk : LinkIndex.kind e L i=0 := by simp [LinkIndex.kind,hfirst]
    have hj : LinkIndex.comparison e L i=i := by simp [LinkIndex.comparison,hfirst]
    let a : Atom Reg Arr := .read (wr .left) (wa .source) (lr .comparison)
    have ha : a.Valid U := by change U.scalar (lr .comparison)<(U.array (wa .source)).length; rwa [ucomp,hj,us,sourceLength]
    have last := atom_runs hU a ha trivial
    refine ⟨10,by omega,a.apply U,.seq pre (.branch_nonzero (by rw [uf,hk]; decide) last),
      a.apply_bounded hU trivial,?_,?_,?_⟩
    · simp [a,Atom.apply,ucomp,hj,us,leftNode,hfirst]
    · simp [a,Atom.apply,U,applyAtoms,pointPrelude,Store.setScalar,hL,hcomp,hj,htypes,BinaryOp.eval,
        rightNode,hfirst,Nat.add_comm]
    · simpa [a,Atom.apply] using uone
  · have hk : LinkIndex.kind e L i≠0 := by
      simp [LinkIndex.kind,hfirst]; split_ifs <;> decide
    let a : Atom Reg Arr := .binary .eq (wr .flag) (lr .kind) (wr .one)
    have ha : a.SmallResult M U := by simp [a,Atom.SmallResult,BinaryOp.eval]; split_ifs <;> omega
    have test := atom_runs hU a trivial ha
    have hV := a.apply_bounded hU ha
    let V := a.apply U
    have vf : V.scalar (wr .flag)=if LinkIndex.kind e L i=1 then 1 else 0 := by simp [V,a,Atom.apply,BinaryOp.eval,uk,uone]
    by_cases hmid : i<e+e*L
    · have hm : LinkIndex.kind e L i=1 := by simp [LinkIndex.kind,hfirst,hmid]
      have hj : LinkIndex.comparison e L i=(i-e)/L := by simp [LinkIndex.comparison,hfirst,hmid]
      have ho : LinkIndex.offset e L i=(i-e)%L := by simp [LinkIndex.offset,hfirst,hmid]
      have hrem := Nat.mod_lt (i-e) positive
      have hb : types+(i-e)/L*(L+1)+(i-e)%L+1≤M := by rw [hj] at hbase; nlinarith
      have midValid : ValidAtoms M middleAtoms V := by
        simp [middleAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
          Store.setScalar,V,a,ub,uoff,uone,hj,ho]
        omega
      obtain ⟨last,hT⟩ := atoms_runs hV middleAtoms midValid
      refine ⟨13,by omega,applyAtoms middleAtoms V,
        .seq pre (.branch_zero (by rw [uf]; simp [hk])
          (.seq test (.branch_nonzero (by rw [vf,hm]; decide) last))),hT,?_,?_,?_⟩ <;>
        simp [applyAtoms,middleAtoms,V,a,Atom.apply,BinaryOp.eval,Store.setScalar,ub,uoff,uone,
          hj,ho,leftNode,rightNode,hfirst,hmid]
    · have hm : LinkIndex.kind e L i=2 := by simp [LinkIndex.kind,hfirst,hmid]
      have hj : LinkIndex.comparison e L i=i-(e+e*L) := by simp [LinkIndex.comparison,hfirst,hmid]
      have hc' : i-(e+e*L)<e := by omega
      have hb : types+(i-(e+e*L))*(L+1)+L≤M := by rw [hj] at hbase; nlinarith
      have lastValid : ValidAtoms M lastAtoms V := by
        simp [lastAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
          Store.setScalar,V,a,ub,ulength,ucomp,ut,hj,targetLength]
        exact ⟨hb,hc'⟩
      obtain ⟨last,hT⟩ := atoms_runs hV lastAtoms lastValid
      refine ⟨13,by omega,applyAtoms lastAtoms V,
        .seq pre (.branch_zero (by rw [uf]; simp [hk])
          (.seq test (.branch_zero (by rw [vf,hm]; decide) last))),hT,?_,?_,?_⟩ <;>
        simp [applyAtoms,lastAtoms,V,a,Atom.apply,BinaryOp.eval,Store.setScalar,ub,ulength,ucomp,ut,
          hj,leftNode,rightNode,hfirst,hmid,uone]

theorem point_runs (S : State) (M : ℕ) (bounded : S.Bounded M) (room : 2≤M)
    (positive : 0<S.scalar (lr .length))
    (valid : S.scalar (lr .link)<S.scalar (lr .comparisons)+S.scalar (lr .comparisons)*S.scalar (lr .length)+S.scalar (lr .comparisons))
    (nodes : S.scalar (wr .types)+S.scalar (lr .comparisons)*(S.scalar (lr .length)+1)≤M)
    (sourceLength : (S.array (wa .source)).length=S.scalar (lr .comparisons))
    (targetLength : (S.array (wa .target)).length=S.scalar (lr .comparisons)) :
    ∃ t≤25,∃ T,Runs (storageBound Reg Arr M) point S t T ∧ T.Bounded M ∧
      T.scalar (wr .left)=leftNode (S.array (wa .source)) (S.scalar (wr .types))
        (S.scalar (lr .comparisons)) (S.scalar (lr .length)) (S.scalar (lr .link)) ∧
      T.scalar (wr .right)=rightNode (S.array (wa .target)) (S.scalar (wr .types))
        (S.scalar (lr .comparisons)) (S.scalar (lr .length)) (S.scalar (lr .link)) ∧ T.scalar (wr .one)=1 := by
  have small : S.left.scalar .comparisons+S.left.scalar .comparisons*S.left.scalar .length≤M := by
    change S.scalar (lr .comparisons)+S.scalar (lr .comparisons)*S.scalar (lr .length)≤M
    nlinarith
  obtain ⟨t,ht,X,run,hX,hk,hc,ho⟩ := LinkIndex.program_runs S.left M bounded.left room positive small
  let U := X.join S.right
  have client : Runs (storageBound Reg Arr M) (LinkIndex.program.map Sum.inl Sum.inl) S t U :=
    run.left_bounded bounded
  have hU : U.Bounded M := hX.join bounded.right
  have uL : U.scalar (lr .length)=S.scalar (lr .length) :=
    run.scalar_eq_of_not_mem .length (by decide)
  obtain ⟨u,hu,T,last,hT,hl,hr,h1⟩ := endpoints_runs U M (S.scalar (lr .comparisons))
    (S.scalar (lr .length)) (S.scalar (lr .link)) (S.scalar (wr .types))
    (S.array (wa .source)) (S.array (wa .target)) hU room positive valid nodes uL rfl hk hc ho rfl rfl
    sourceLength targetLength
  exact ⟨t+u,by omega,T,.seq client last,hT,hl,hr,h1⟩

def outputArray (right : Bool) : Arr := wa (if right then .rightNodes else .leftNodes)
def valueReg (right : Bool) : Reg := wr (if right then .right else .left)
def value (right : Bool) (sources targets : List ℕ) (types e L i : ℕ) : ℕ :=
  if right then rightNode targets types e L i else leftNode sources types e L i
def tablePrelude : List (Atom Reg Arr) := [
  .const (wr .one) 1,.const (wr .zero) 0,.binary .mul (wr .count) (lr .comparisons) (lr .length),
  .binary .add (wr .count) (wr .count) (lr .comparisons),
  .binary .add (wr .count) (wr .count) (lr .comparisons)]
def program (right : Bool) : Code := .seq (atoms tablePrelude)
  (ArrayTabulate.tabulate (lr .link) (wr .todo) (wr .count) (wr .one) (wr .zero)
    (valueReg right) (outputArray right) point)

structure Context (e L types : ℕ) (sources targets : List ℕ) (S : State) : Prop where
  comparisons : S.scalar (lr .comparisons)=e
  length : S.scalar (lr .length)=L
  types : S.scalar (wr .types)=types
  source : S.array (wa .source)=sources
  target : S.array (wa .target)=targets

theorem program_runs (right : Bool) (S : State) (M : ℕ) (bounded : S.Bounded M) (room : 2≤M)
    (positive : 0<S.scalar (lr .length))
    (links : S.scalar (lr .comparisons)+S.scalar (lr .comparisons)*S.scalar (lr .length)+S.scalar (lr .comparisons)≤M)
    (nodes : S.scalar (wr .types)+S.scalar (lr .comparisons)*(S.scalar (lr .length)+1)≤M)
    (sourceLength : (S.array (wa .source)).length=S.scalar (lr .comparisons))
    (targetLength : (S.array (wa .target)).length=S.scalar (lr .comparisons)) :
    ∃ t≤29*(S.scalar (lr .comparisons)+S.scalar (lr .comparisons)*S.scalar (lr .length)+S.scalar (lr .comparisons))+9,∃ T,
      Runs (storageBound Reg Arr M) (program right) S t T ∧ T.Bounded M ∧
      T.array (outputArray right)=List.ofFn (fun i : Fin (S.scalar (lr .comparisons)+S.scalar (lr .comparisons)*S.scalar (lr .length)+S.scalar (lr .comparisons)) =>
        value right (S.array (wa .source)) (S.array (wa .target)) (S.scalar (wr .types))
          (S.scalar (lr .comparisons)) (S.scalar (lr .length)) i) := by
  let P := Context (S.scalar (lr .comparisons)) (S.scalar (lr .length)) (S.scalar (wr .types))
    (S.array (wa .source)) (S.array (wa .target))
  have pi : ∀ T x,P T → P (T.setScalar (lr .link) x) := by
    intro T x h
    exact ⟨by simpa using h.comparisons,by simpa using h.length,by simpa using h.types,h.source,h.target⟩
  have pt : ∀ T x,P T → P (T.setScalar (wr .todo) x) := by
    intro T x h
    exact ⟨by simpa using h.comparisons,by simpa using h.length,by simpa using h.types,h.source,h.target⟩
  have po : ∀ T xs,P T → P (T.setArray (outputArray right) xs) := by
    intro T xs h
    refine ⟨h.comparisons,h.length,h.types,?_,?_⟩ <;>
      cases right <;> simp [outputArray,Store.setArray,h.source,h.target]
  let N := S.scalar (lr .comparisons)+S.scalar (lr .comparisons)*S.scalar (lr .length)+S.scalar (lr .comparisons)
  have body : ∀ i : Fin N,∀ T,P T → T.Bounded M → T.scalar (lr .link)=i.val →
      T.scalar (wr .todo)=N-i.val → T.scalar (wr .one)=1 → ∃ t≤25,∃ U,
        Runs (storageBound Reg Arr M) point T t U ∧ U.Bounded M ∧ P U ∧
        U.scalar (lr .link)=i.val ∧ U.scalar (wr .todo)=N-i.val ∧ U.scalar (wr .one)=1 ∧
        U.scalar (valueReg right)=value right (S.array (wa .source)) (S.array (wa .target)) (S.scalar (wr .types))
          (S.scalar (lr .comparisons)) (S.scalar (lr .length)) i ∧ U.array (outputArray right)=T.array (outputArray right) := by
    intro i T hT hb hi ht ho
    obtain ⟨t,htime,U,run,hU,hl,hr,h1⟩ := point_runs T M hb room (by rwa [hT.length])
      (by rw [hi,hT.comparisons,hT.length]; exact i.isLt) (by rwa [hT.types,hT.comparisons,hT.length])
      (by rwa [hT.source,hT.comparisons]) (by rwa [hT.target,hT.comparisons])
    have hu : P U := ⟨(run.scalar_eq_of_not_mem (lr .comparisons) (by decide)).trans hT.comparisons,
      (run.scalar_eq_of_not_mem (lr .length) (by decide)).trans hT.length,
      (run.scalar_eq_of_not_mem (wr .types) (by decide)).trans hT.types,
      (run.array_eq_of_not_mem (wa .source) (by decide)).trans hT.source,
      (run.array_eq_of_not_mem (wa .target) (by decide)).trans hT.target⟩
    refine ⟨t,htime,U,run,hU,hu,(run.scalar_eq_of_not_mem (lr .link) (by decide)).trans hi,
      (run.scalar_eq_of_not_mem (wr .todo) (by decide)).trans ht,h1,?_,?_⟩
    · cases right
      · simpa only [valueReg,value,Bool.false_eq_true,if_false,hT.source,hT.types,hT.comparisons,hT.length,hi] using hl
      · simpa only [valueReg,value,if_true,hT.target,hT.types,hT.comparisons,hT.length,hi] using hr
    · apply run.array_eq_of_not_mem
      cases right <;> decide
  have valid : ValidAtoms M tablePrelude S := by
    simp [tablePrelude,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar]
    omega
  obtain ⟨preRun,hU⟩ := atoms_runs bounded tablePrelude valid
  let U := applyAtoms tablePrelude S
  have hu : P U := by
    refine ⟨?_,?_,?_,?_,?_⟩ <;> simp [U,tablePrelude,applyAtoms,Atom.apply,Store.setScalar]
  obtain ⟨t,ht,T,run,hT,_,hout⟩ := ArrayTabulate.tabulate_runs
    (lr .link) (wr .todo) (wr .count) (wr .one) (wr .zero) (valueReg right) (outputArray right) point
    (fun i : Fin N => value right (S.array (wa .source)) (S.array (wa .target)) (S.scalar (wr .types))
      (S.scalar (lr .comparisons)) (S.scalar (lr .length)) i)
    P M 25 pi pt po (by decide) (by decide) (by decide) body U hU hu
    (by simp [U,tablePrelude,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,N,Nat.add_comm])
    (by simp [U,tablePrelude,applyAtoms,Atom.apply,Store.setScalar])
    (by simp [U,tablePrelude,applyAtoms,Atom.apply,Store.setScalar])
  exact ⟨5+t,by omega,T,.seq preRun run,hT,hout⟩

end GroupWL.MachinePrograms.LinkNodes
