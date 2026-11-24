import GroupWL.MachinePrograms.ArrayTabulate
import GroupWL.MachinePrograms.NatArrayFrames

/-! Concrete programs for all four endpoints of a square candidate. -/
namespace GroupWL.MachinePrograms.SquareIndices
open NatArrayLanguage
set_option maxHeartbeats 2000000

inductive Reg where
  | width | cutoff | hcount | total | index | todo | zero | one | two | four
  | pair | bits | link | coordinate | a | b | next | quotient
  | node | base | position | label | at | flag | temporary | value
  deriving DecidableEq,Fintype
inductive Arr where
  | leftNodes | rightNodes | permutation | horizontalRanks | verticalRanks | output
  deriving DecidableEq,Fintype
inductive Endpoint where
  | left | right | before | after
  deriving DecidableEq,Fintype
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

structure Data where
  width : ℕ
  cutoff : ℕ
  comparisons : ℕ
  nodes : ℕ
  hcount : ℕ
  leftNodes : List ℕ
  rightNodes : List ℕ
  permutation : List ℕ
  horizontalRanks : List ℕ
  verticalRanks : List ℕ

def Data.links (d : Data) := d.cutoff+d.comparisons
def Data.count (d : Data) := d.links*d.width*4
def Data.label (d : Data) (l i a : ℕ) :=
  if l<d.cutoff then a
  else if (d.permutation[(l-d.cutoff)*d.width+i]?).getD 0=0 then a else 1-a
def Data.entry (d : Data) (which : Endpoint) (key : ℕ) : ℕ :=
  let l := key/4/d.width
  let i := key/4%d.width
  let a := key%4/2
  let b := key%4%2
  let next := (i+1)%d.width
  match which with
  | .left => (d.horizontalRanks[4*((d.leftNodes[l]?).getD 0*d.width+i)+2*a+b]?).getD 0
  | .right => (d.horizontalRanks[4*((d.rightNodes[l]?).getD 0*d.width+i)+
      2*d.label l i a+d.label l next b]?).getD 0
  | .before => d.hcount+(d.verticalRanks[2*(l*d.width+i)+a]?).getD 0
  | .after => d.hcount+(d.verticalRanks[2*(l*d.width+next)+b]?).getD 0

structure Data.Valid (d : Data) (M : ℕ) : Prop where
  left_length : d.leftNodes.length=d.links
  right_length : d.rightNodes.length=d.links
  left_values : ∀x∈d.leftNodes,x<d.nodes
  right_values : ∀x∈d.rightNodes,x<d.nodes
  permutation_length : d.permutation.length=d.comparisons*d.width
  horizontal_length : d.horizontalRanks.length=4*(d.nodes*d.width)
  vertical_length : d.verticalRanks.length=2*(d.links*d.width)
  vertical_values : ∀x∈d.verticalRanks,d.hcount+x≤M

structure Context (d : Data) (S : State) : Prop where
  width : S.scalar .width=d.width
  cutoff : S.scalar .cutoff=d.cutoff
  hcount : S.scalar .hcount=d.hcount
  zero : S.scalar .zero=0
  one : S.scalar .one=1
  two : S.scalar .two=2
  four : S.scalar .four=4
  leftNodes : S.array .leftNodes=d.leftNodes
  rightNodes : S.array .rightNodes=d.rightNodes
  permutation : S.array .permutation=d.permutation
  horizontalRanks : S.array .horizontalRanks=d.horizontalRanks
  verticalRanks : S.array .verticalRanks=d.verticalRanks

def decodeAtoms : List (Atom Reg Arr) := [
  .divmod .pair .bits .index .four,.divmod .link .coordinate .pair .width,
  .divmod .a .b .bits .two,.binary .add .next .coordinate .one,
  .divmod .quotient .next .next .width]
def horizontalAtoms : List (Atom Reg Arr) := [
  .binary .mul .base .node .width,.binary .add .position .base .coordinate,
  .binary .mul .position .position .four,.binary .mul .temporary .a .two,
  .binary .add .position .position .temporary,.binary .add .position .position .b,
  .read .value .horizontalRanks .position]
def verticalAtoms : List (Atom Reg Arr) := [
  .binary .mul .base .link .width,.binary .add .position .base .at,
  .binary .mul .position .position .two,.binary .add .position .position .label,
  .read .value .verticalRanks .position,.binary .add .value .hcount .value]
def flipPrelude : List (Atom Reg Arr) := [
  .binary .sub .base .link .cutoff,.binary .mul .base .base .width,
  .binary .add .position .base .at,.read .flag .permutation .position,
  .binary .eq .flag .flag .zero]
def flip : Code := .seq (.atom (.binary .lt .flag .link .cutoff))
  (.branch .flag .skip (.seq (atoms flipPrelude)
    (.branch .flag .skip (.atom (.binary .sub .label .one .label)))))
def rightLabels : Code := .seq (atoms [.copy .label .a,.copy .at .coordinate])
  (.seq flip (.seq (atoms [.copy .a .label,.copy .label .b,.copy .at .next])
    (.seq flip (.atom (.copy .b .label)))))
def finish : Endpoint→Code
  | .left => .seq (.atom (.read .node .leftNodes .link)) (atoms horizontalAtoms)
  | .right => .seq rightLabels
      (.seq (.atom (.read .node .rightNodes .link)) (atoms horizontalAtoms))
  | .before => .seq (atoms [.copy .at .coordinate,.copy .label .a]) (atoms verticalAtoms)
  | .after => .seq (atoms [.copy .at .next,.copy .label .b]) (atoms verticalAtoms)
def point (which : Endpoint) : Code := .seq (atoms decodeAtoms) (finish which)
def program (which : Endpoint) : Code :=
  ArrayTabulate.tabulate .index .todo .total .one .zero .value .output (point which)

theorem context_frame {d : Data} {S T : State} {B t : ℕ} {p : Code}
    (h : Runs B p S t T) (hs : Context d S)
    (hw : Reg.width∉p.scalarWrites) (hc : Reg.cutoff∉p.scalarWrites)
    (hh : Reg.hcount∉p.scalarWrites) (hz : Reg.zero∉p.scalarWrites)
    (ho : Reg.one∉p.scalarWrites) (ht : Reg.two∉p.scalarWrites)
    (hf : Reg.four∉p.scalarWrites) (ha : p.arrayWrites=∅) : Context d T := by
  refine ⟨(h.scalar_eq_of_not_mem _ hw).trans hs.width,
    (h.scalar_eq_of_not_mem _ hc).trans hs.cutoff,
    (h.scalar_eq_of_not_mem _ hh).trans hs.hcount,
    (h.scalar_eq_of_not_mem _ hz).trans hs.zero,
    (h.scalar_eq_of_not_mem _ ho).trans hs.one,
    (h.scalar_eq_of_not_mem _ ht).trans hs.two,
    (h.scalar_eq_of_not_mem _ hf).trans hs.four,?_,?_,?_,?_,?_⟩
  all_goals first
    | exact (h.array_eq_of_not_mem _ (by rw [ha]; simp)).trans hs.leftNodes
    | exact (h.array_eq_of_not_mem _ (by rw [ha]; simp)).trans hs.rightNodes
    | exact (h.array_eq_of_not_mem _ (by rw [ha]; simp)).trans hs.permutation
    | exact (h.array_eq_of_not_mem _ (by rw [ha]; simp)).trans hs.horizontalRanks
    | exact (h.array_eq_of_not_mem _ (by rw [ha]; simp)).trans hs.verticalRanks

theorem label_lt (d : Data) (l i a : ℕ) (ha : a<2) : d.label l i a<2 := by
  unfold Data.label
  split_ifs <;> omega

theorem decode_runs (d : Data) (S : State) (M : ℕ) (bounded : S.Bounded M)
    (context : Context d S) (index : S.scalar .index<d.count) :
    Runs (storageBound Reg Arr M) (atoms decodeAtoms) S 5 (applyAtoms decodeAtoms S) ∧
      (applyAtoms decodeAtoms S).Bounded M := by
  have hw : 0<d.width := by
    have : 0<d.links*d.width := by unfold Data.count at index; nlinarith
    exact Nat.pos_of_mul_pos_left this
  have hc := Nat.mod_lt (S.scalar .index/4) hw
  have hb : d.width≤M := by simpa [context.width] using bounded.1 Reg.width
  have valid : ValidAtoms M decodeAtoms S := by
    simp [decodeAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,context.width,context.one,context.two,context.four]
    exact ⟨hw,by omega,hw⟩
  exact atoms_runs bounded decodeAtoms valid

theorem horizontal_runs (d : Data) (S : State) (M : ℕ) (bounded : S.Bounded M)
    (context : Context d S) (valid : Data.Valid d M)
    (hn : S.scalar .node<d.nodes) (hi : S.scalar .coordinate<d.width)
    (ha : S.scalar .a<2) (hb : S.scalar .b<2) :
    Runs (storageBound Reg Arr M) (atoms horizontalAtoms) S 7 (applyAtoms horizontalAtoms S) ∧
      (applyAtoms horizontalAtoms S).Bounded M ∧
      (applyAtoms horizontalAtoms S).scalar .value=
        (d.horizontalRanks[4*(S.scalar .node*d.width+S.scalar .coordinate)+2*S.scalar .a+S.scalar .b]?).getD 0 := by
  have hl : 4*(d.nodes*d.width)≤M := by
    simpa [context.horizontalRanks,valid.horizontal_length] using bounded.2.1 Arr.horizontalRanks
  have hm := Nat.mul_le_mul_right d.width (Nat.succ_le_of_lt hn)
  have hr : 4*(S.scalar .node*d.width+S.scalar .coordinate)+2*S.scalar .a+S.scalar .b<4*(d.nodes*d.width) := by nlinarith
  have hv : ValidAtoms M horizontalAtoms S := by
    simp [horizontalAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,context.width,context.two,context.four,context.horizontalRanks,valid.horizontal_length]
    exact ⟨by nlinarith,by nlinarith,by nlinarith,by nlinarith,
      by nlinarith,by nlinarith,by simpa [Nat.mul_comm] using hr⟩
  obtain ⟨run,hT⟩ := atoms_runs bounded horizontalAtoms hv
  exact ⟨run,hT,by simp [applyAtoms,horizontalAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,
    context.width,context.two,context.four,context.horizontalRanks,Nat.mul_comm]⟩

theorem vertical_runs (d : Data) (S : State) (M : ℕ) (bounded : S.Bounded M)
    (context : Context d S) (valid : Data.Valid d M)
    (hl : S.scalar .link<d.links) (hi : S.scalar .at<d.width) (ha : S.scalar .label<2) :
    Runs (storageBound Reg Arr M) (atoms verticalAtoms) S 6 (applyAtoms verticalAtoms S) ∧
      (applyAtoms verticalAtoms S).Bounded M ∧
      (applyAtoms verticalAtoms S).scalar .value=
        d.hcount+(d.verticalRanks[2*(S.scalar .link*d.width+S.scalar .at)+S.scalar .label]?).getD 0 := by
  have hlen : 2*(d.links*d.width)≤M := by
    simpa [context.verticalRanks,valid.vertical_length] using bounded.2.1 Arr.verticalRanks
  have hm := Nat.mul_le_mul_right d.width (Nat.succ_le_of_lt hl)
  have hr : 2*(S.scalar .link*d.width+S.scalar .at)+S.scalar .label<d.verticalRanks.length := by
    rw [valid.vertical_length];nlinarith
  have hval : d.hcount+(d.verticalRanks[2*(S.scalar .link*d.width+S.scalar .at)+S.scalar .label]?).getD 0≤M := by
    rw [List.getElem?_eq_getElem hr]
    exact valid.vertical_values _ (List.getElem_mem hr)
  have hv : ValidAtoms M verticalAtoms S := by
    simp [verticalAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,context.width,context.two,context.hcount,context.verticalRanks]
    exact ⟨by nlinarith,by nlinarith,by nlinarith,by rw [valid.vertical_length] at hr; nlinarith,
      by simpa [Nat.mul_comm] using hr,by simpa [Nat.mul_comm] using hval⟩
  obtain ⟨run,hT⟩ := atoms_runs bounded verticalAtoms hv
  exact ⟨run,hT,by simp [applyAtoms,verticalAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,
    context.width,context.two,context.hcount,context.verticalRanks,Nat.mul_comm]⟩

theorem flip_runs (d : Data) (S : State) (M : ℕ) (bounded : S.Bounded M)
    (context : Context d S) (valid : Data.Valid d M)
    (hl : S.scalar .link<d.links) (hi : S.scalar .at<d.width) :
    ∃ t≤9,∃ T,Runs (storageBound Reg Arr M) flip S t T ∧ T.Bounded M ∧
      T.scalar .label=d.label (S.scalar .link) (S.scalar .at) (S.scalar .label) := by
  have h1 : 1≤M := by simpa [context.one] using bounded.1 Reg.one
  let test : Atom Reg Arr := .binary .lt .flag .link .cutoff
  have ts : test.SmallResult M S := by
    simp [test,Atom.SmallResult,BinaryOp.eval];split_ifs <;> omega
  have first := atom_runs bounded test trivial ts
  have hU := test.apply_bounded bounded ts
  let U := test.apply S
  have uf : U.scalar .flag=if S.scalar .link<d.cutoff then 1 else 0 := by
    simp [U,test,Atom.apply,BinaryOp.eval,context.cutoff]
  by_cases hc : S.scalar .link<d.cutoff
  · refine ⟨2,by omega,U,.seq first (.branch_nonzero (by rw [uf];simp [hc])
      (.skip (Store.size_le_of_bounded hU))),hU,?_⟩
    simp [Data.label,hc,U,test,Atom.apply,Store.setScalar]
  · have hm := Nat.mul_le_mul_right d.width
      (show S.scalar .link-d.cutoff+1≤d.comparisons by unfold Data.links at hl;omega)
    have hp : (S.scalar .link-d.cutoff)*d.width+S.scalar .at<d.permutation.length := by
      rw [valid.permutation_length];nlinarith
    have hlen : d.permutation.length≤M := by simpa [context.permutation] using bounded.2.1 Arr.permutation
    have vp : ValidAtoms M flipPrelude U := by
      simp [flipPrelude,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
        Store.setScalar,U,test,context.cutoff,context.width,context.zero,context.permutation]
      refine ⟨?_,?_,?_,?_,?_⟩
      · have := bounded.1 Reg.link;omega
      · nlinarith
      · omega
      · exact hp
      · split_ifs <;> omega
    obtain ⟨middle,hV⟩ := atoms_runs hU flipPrelude vp
    let V := applyAtoms flipPrelude U
    have vf : V.scalar .flag=
        if (d.permutation[(S.scalar .link-d.cutoff)*d.width+S.scalar .at]?).getD 0=0 then 1 else 0 := by
      simp [V,applyAtoms,flipPrelude,U,test,Atom.apply,BinaryOp.eval,Store.setScalar,
        context.cutoff,context.width,context.zero,context.permutation]
    have vl : V.scalar .label=S.scalar .label := by
      simp [V,applyAtoms,flipPrelude,U,test,Atom.apply,Store.setScalar]
    have vo : V.scalar .one=1 := by
      simpa [V,applyAtoms,flipPrelude,U,test,Atom.apply,Store.setScalar] using context.one
    by_cases hp0 : (d.permutation[(S.scalar .link-d.cutoff)*d.width+S.scalar .at]?).getD 0=0
    · refine ⟨8,by omega,V,.seq first (.branch_zero (by rw [uf];simp [hc])
        (.seq middle (.branch_nonzero (by rw [vf];simp [hp0])
          (.skip (Store.size_le_of_bounded hV))))),hV,?_⟩
      simpa [Data.label,hc,hp0] using vl
    · let last : Atom Reg Arr := .binary .sub .label .one .label
      have ls : last.SmallResult M V := by simp [last,Atom.SmallResult,BinaryOp.eval,vo];omega
      have lastRun := atom_runs hV last trivial ls
      refine ⟨9,le_rfl,last.apply V,.seq first (.branch_zero (by rw [uf];simp [hc])
        (.seq middle (.branch_zero (by rw [vf];simp [hp0]) lastRun))),
        last.apply_bounded hV ls,?_⟩
      simp [last,Atom.apply,BinaryOp.eval,vo,vl,Data.label,hc,hp0]

theorem rightLabels_runs (d : Data) (S : State) (M : ℕ) (bounded : S.Bounded M)
    (context : Context d S) (valid : Data.Valid d M)
    (hl : S.scalar .link<d.links) (hi : S.scalar .coordinate<d.width)
    (hn : S.scalar .next<d.width) :
    ∃ t≤24,∃ T,Runs (storageBound Reg Arr M) rightLabels S t T ∧ T.Bounded M ∧
      T.scalar .a=d.label (S.scalar .link) (S.scalar .coordinate) (S.scalar .a) ∧
      T.scalar .b=d.label (S.scalar .link) (S.scalar .next) (S.scalar .b) := by
  let as : List (Atom Reg Arr) := [.copy .label .a,.copy .at .coordinate]
  obtain ⟨first,hU⟩ := atoms_runs bounded as (by simp [as,ValidAtoms,Atom.Valid,Atom.SmallResult])
  let U := applyAtoms as S
  have cu : Context d U := context_frame first context (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have ul : U.scalar .link=S.scalar .link := by simp [U,as,applyAtoms,Atom.apply,Store.setScalar]
  have ua : U.scalar .at=S.scalar .coordinate := by simp [U,as,applyAtoms,Atom.apply,Store.setScalar]
  have uv : U.scalar .label=S.scalar .a := by simp [U,as,applyAtoms,Atom.apply,Store.setScalar]
  obtain ⟨t,ht,V,run,hV,hv⟩ := flip_runs d U M hU cu valid (by rwa [ul]) (by rwa [ua])
  have cv : Context d V := context_frame run cu (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have vl := (run.scalar_eq_of_not_mem .link (by decide)).trans ul
  have vb : V.scalar .b=S.scalar .b := (run.scalar_eq_of_not_mem .b (by decide)).trans
    (by simp [U,as,applyAtoms,Atom.apply,Store.setScalar])
  have vn : V.scalar .next=S.scalar .next := (run.scalar_eq_of_not_mem .next (by decide)).trans
    (by simp [U,as,applyAtoms,Atom.apply,Store.setScalar])
  let bs : List (Atom Reg Arr) := [.copy .a .label,.copy .label .b,.copy .at .next]
  obtain ⟨middle,hW⟩ := atoms_runs hV bs (by simp [bs,ValidAtoms,Atom.Valid,Atom.SmallResult])
  let W := applyAtoms bs V
  have cw : Context d W := context_frame middle cv (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have wl : W.scalar .link=S.scalar .link := by simpa [W,bs,applyAtoms,Atom.apply,Store.setScalar] using vl
  have wa : W.scalar .at=S.scalar .next := by simp [W,bs,applyAtoms,Atom.apply,Store.setScalar,vn]
  have wv : W.scalar .label=S.scalar .b := by simp [W,bs,applyAtoms,Atom.apply,Store.setScalar,vb]
  have waa : W.scalar .a=d.label (S.scalar .link) (S.scalar .coordinate) (S.scalar .a) := by
    simpa [W,bs,applyAtoms,Atom.apply,Store.setScalar,ul,ua,uv] using hv
  obtain ⟨s,hs,X,last,hX,hx⟩ := flip_runs d W M hW cw valid (by rwa [wl]) (by rwa [wa])
  let copy : Atom Reg Arr := .copy .b .label
  have copyRun := atom_runs hX copy trivial trivial
  refine ⟨2+(t+(3+(s+1))),by omega,copy.apply X,
    .seq first (.seq run (.seq middle (.seq last copyRun))),copy.apply_bounded hX trivial,?_,?_⟩
  · simpa [copy,Atom.apply,Store.setScalar] using
      (last.scalar_eq_of_not_mem .a (by decide)).trans waa
  · simpa [copy,Atom.apply,wl,wa,wv] using hx

theorem readHorizontal_runs (source : Arr) (xs : List ℕ) (d : Data) (S : State) (M : ℕ)
    (bounded : S.Bounded M) (context : Context d S) (valid : Data.Valid d M)
    (input : S.array source=xs) (length : xs.length=d.links) (values : ∀x∈xs,x<d.nodes)
    (hl : S.scalar .link<d.links) (hi : S.scalar .coordinate<d.width)
    (ha : S.scalar .a<2) (hb : S.scalar .b<2) :
    ∃ T,Runs (storageBound Reg Arr M)
      (.seq (.atom (.read .node source .link)) (atoms horizontalAtoms)) S 8 T ∧ T.Bounded M ∧
      T.scalar .value=(d.horizontalRanks[4*((xs[S.scalar .link]?).getD 0*d.width+
        S.scalar .coordinate)+2*S.scalar .a+S.scalar .b]?).getD 0 := by
  let firstAtom : Atom Reg Arr := .read .node source .link
  have hp : S.scalar .link<xs.length := by omega
  have fv : firstAtom.Valid S := by simpa [firstAtom,Atom.Valid,input] using hp
  have first := atom_runs bounded firstAtom fv trivial
  have hU := firstAtom.apply_bounded bounded trivial
  let U := firstAtom.apply S
  have cu : Context d U := context_frame first context (by cases source <;> decide) (by cases source <;> decide) (by cases source <;> decide)
    (by cases source <;> decide) (by cases source <;> decide) (by cases source <;> decide) (by cases source <;> decide) (by cases source <;> decide)
  have un : U.scalar .node<d.nodes := by
    simp only [U,firstAtom,Atom.apply,Store.setScalar_same,input,List.getElem?_eq_getElem hp,Option.getD_some]
    exact values _ (List.getElem_mem hp)
  obtain ⟨last,hT,hv⟩ := horizontal_runs d U M hU cu valid un
    (by simpa [U,firstAtom,Atom.apply,Store.setScalar] using hi)
    (by simpa [U,firstAtom,Atom.apply,Store.setScalar] using ha)
    (by simpa [U,firstAtom,Atom.apply,Store.setScalar] using hb)
  exact ⟨applyAtoms horizontalAtoms U,.seq first last,hT,
    by simpa [U,firstAtom,Atom.apply,Store.setScalar,input] using hv⟩

structure Decoded (d : Data) (key : ℕ) (S : State) : Prop where
  link : S.scalar .link=key/4/d.width
  coordinate : S.scalar .coordinate=key/4%d.width
  a : S.scalar .a=key%4/2
  b : S.scalar .b=key%4%2
  next : S.scalar .next=(key/4%d.width+1)%d.width

theorem finish_runs (which : Endpoint) (d : Data) (key M : ℕ) (S : State)
    (bounded : S.Bounded M) (context : Context d S) (valid : Data.Valid d M)
    (decoded : Decoded d key S) (index : key<d.count) :
    ∃ t≤32,∃ T,Runs (storageBound Reg Arr M) (finish which) S t T ∧ T.Bounded M ∧
      T.scalar .value=d.entry which key := by
  have hw : 0<d.width := by
    have : 0<d.links*d.width := by unfold Data.count at index;nlinarith
    exact Nat.pos_of_mul_pos_left this
  have hq : key/4<d.links*d.width := (Nat.div_lt_iff_lt_mul (by decide : 0<4)).mpr index
  have hl : S.scalar .link<d.links := by rw [decoded.link];exact (Nat.div_lt_iff_lt_mul hw).mpr hq
  have hi : S.scalar .coordinate<d.width := by rw [decoded.coordinate];exact Nat.mod_lt _ hw
  have hn : S.scalar .next<d.width := by rw [decoded.next];exact Nat.mod_lt _ hw
  have ha : S.scalar .a<2 := by rw [decoded.a];omega
  have hb : S.scalar .b<2 := by rw [decoded.b];omega
  cases which with
  | left =>
    obtain ⟨T,run,hT,hv⟩ := readHorizontal_runs .leftNodes d.leftNodes d S M bounded context valid
      context.leftNodes valid.left_length valid.left_values hl hi ha hb
    exact ⟨8,by omega,T,run,hT,by simpa [Data.entry,decoded.link,decoded.coordinate,decoded.a,decoded.b] using hv⟩
  | right =>
    obtain ⟨t,ht,U,run,hU,ua,ub⟩ := rightLabels_runs d S M bounded context valid hl hi hn
    have cu : Context d U := context_frame run context (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
    have ul := run.scalar_eq_of_not_mem .link (by decide)
    have ui := run.scalar_eq_of_not_mem .coordinate (by decide)
    obtain ⟨T,last,hT,hv⟩ := readHorizontal_runs .rightNodes d.rightNodes d U M hU cu valid
      cu.rightNodes valid.right_length valid.right_values (by rwa [ul]) (by rwa [ui])
      (by rw [ua];exact label_lt _ _ _ _ ha) (by rw [ub];exact label_lt _ _ _ _ hb)
    exact ⟨t+8,by omega,T,.seq run last,hT,by simpa [Data.entry,ul,ui,ua,ub,
      decoded.link,decoded.coordinate,decoded.a,decoded.b,decoded.next] using hv⟩
  | before =>
    let as : List (Atom Reg Arr) := [.copy .at .coordinate,.copy .label .a]
    obtain ⟨first,hU⟩ := atoms_runs bounded as (by simp [as,ValidAtoms,Atom.Valid,Atom.SmallResult])
    let U := applyAtoms as S
    have cu : Context d U := context_frame first context (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
    obtain ⟨last,hT,hv⟩ := vertical_runs d U M hU cu valid
      (by simpa [U,as,applyAtoms,Atom.apply,Store.setScalar] using hl)
      (by simpa [U,as,applyAtoms,Atom.apply,Store.setScalar] using hi)
      (by simpa [U,as,applyAtoms,Atom.apply,Store.setScalar] using ha)
    exact ⟨8,by omega,applyAtoms verticalAtoms U,.seq first last,hT,
      by simpa [Data.entry,U,as,applyAtoms,Atom.apply,Store.setScalar,
        decoded.link,decoded.coordinate,decoded.a] using hv⟩
  | after =>
    let as : List (Atom Reg Arr) := [.copy .at .next,.copy .label .b]
    obtain ⟨first,hU⟩ := atoms_runs bounded as (by simp [as,ValidAtoms,Atom.Valid,Atom.SmallResult])
    let U := applyAtoms as S
    have cu : Context d U := context_frame first context (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
    obtain ⟨last,hT,hv⟩ := vertical_runs d U M hU cu valid
      (by simpa [U,as,applyAtoms,Atom.apply,Store.setScalar] using hl)
      (by simpa [U,as,applyAtoms,Atom.apply,Store.setScalar] using hn)
      (by simpa [U,as,applyAtoms,Atom.apply,Store.setScalar] using hb)
    exact ⟨8,by omega,applyAtoms verticalAtoms U,.seq first last,hT,
      by simpa [Data.entry,U,as,applyAtoms,Atom.apply,Store.setScalar,
        decoded.link,decoded.next,decoded.b] using hv⟩

theorem point_runs (which : Endpoint) (d : Data) (S : State) (M : ℕ)
    (bounded : S.Bounded M) (context : Context d S) (valid : Data.Valid d M)
    (index : S.scalar .index<d.count) :
    ∃ t≤37,∃ T,Runs (storageBound Reg Arr M) (point which) S t T ∧ T.Bounded M ∧
      T.scalar .value=d.entry which (S.scalar .index) := by
  obtain ⟨first,hU⟩ := decode_runs d S M bounded context index
  let U := applyAtoms decodeAtoms S
  have cu : Context d U := context_frame first context (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have decoded : Decoded d (S.scalar .index) U := by
    constructor <;> simp [U,applyAtoms,decodeAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,
      context.width,context.one,context.two,context.four]
  obtain ⟨t,ht,T,last,hT,hv⟩ := finish_runs which d (S.scalar .index) M U hU cu valid decoded index
  exact ⟨5+t,by omega,T,.seq first last,hT,hv⟩

theorem program_runs (which : Endpoint) (d : Data) (S : State) (M : ℕ)
    (bounded : S.Bounded M) (context : Context d S) (valid : Data.Valid d M)
    (total : S.scalar .total=d.count) :
    ∃ t≤41*d.count+4,∃ T,Runs (storageBound Reg Arr M) (program which) S t T ∧
      T.Bounded M ∧ Context d T ∧ T.array .output=List.ofFn (fun i : Fin d.count => d.entry which i) := by
  have pi : ∀ T x,Context d T → Context d (T.setScalar .index x) := by
    intro T x h;rcases h with ⟨a,b,c,e,f,g,h,i,j,k,l,m⟩
    constructor <;> assumption
  have pt : ∀ T x,Context d T → Context d (T.setScalar .todo x) := by
    intro T x h;rcases h with ⟨a,b,c,e,f,g,h,i,j,k,l,m⟩
    constructor <;> assumption
  have po : ∀ T xs,Context d T → Context d (T.setArray .output xs) := by
    intro T xs h;rcases h with ⟨a,b,c,e,f,g,h,i,j,k,l,m⟩
    constructor <;> assumption
  have body : ∀ i : Fin d.count,∀ T,Context d T → T.Bounded M → T.scalar .index=i.val →
      T.scalar .todo=d.count-i.val → T.scalar .one=1 →
      ∃ t≤37,∃ U,Runs (storageBound Reg Arr M) (point which) T t U ∧ U.Bounded M ∧
        Context d U ∧ U.scalar .index=i.val ∧ U.scalar .todo=d.count-i.val ∧ U.scalar .one=1 ∧
        U.scalar .value=d.entry which i ∧ U.array .output=T.array .output := by
    intro i T hc hb hi ht ho
    obtain ⟨t,hcost,U,run,hU,hv⟩ := point_runs which d T M hb hc valid (by rw [hi];exact i.isLt)
    have contextU : Context d U := by
      apply context_frame run hc <;> cases which <;> decide
    have ui := run.scalar_eq_of_not_mem .index (by cases which <;> decide)
    have ut := run.scalar_eq_of_not_mem .todo (by cases which <;> decide)
    have uo := run.array_eq_of_not_mem .output (by cases which <;> decide)
    exact ⟨t,hcost,U,run,hU,contextU,ui.trans hi,ut.trans ht,contextU.one,by simpa [hi] using hv,uo⟩
  obtain ⟨t,ht,T,run,hT,hc,hout⟩ := ArrayTabulate.tabulate_runs Reg.index Reg.todo Reg.total
    Reg.one Reg.zero Reg.value Arr.output (point which) (fun i : Fin d.count => d.entry which i)
    (Context d) M 37 pi pt po (by decide) (by decide) (by decide) body
    S bounded context total context.one context.zero
  exact ⟨t,by omega,T,run,hT,hc,hout⟩

end GroupWL.MachinePrograms.SquareIndices
