import GroupWL.MachinePrograms.NatArrayParser
import GroupWL.MachinePrograms.ArrayTabulation
import GroupWL.CircuitDescription

/-! A uniform finite-control parser for mixed unary and raw-bit records.
The record width and number of leading unary fields are ordinary registers. -/
namespace GroupWL.MachinePrograms.CircuitRecordParser
open NatArrayLanguage
open NatArrayLowering (bitNat)

inductive Token where | nat (value : ℕ) | bit (value : Bool)
  deriving DecidableEq
namespace Token
def value : Token → ℕ | .nat n => n | .bit b => bitNat b
def word : Token → List Bool | .nat n => CircuitDescription.natWord n | .bit b => [b]
def isNat : Token → Bool | .nat _ => true | .bit _ => false
end Token

def stream (xs : List Token) : List Bool := xs.flatMap Token.word

inductive Reg where
  | cursor | length | value | valid | scanning | bit | flag | one
  | quotient | column | unaryCount | stride | count | index | todo | zero
  deriving DecidableEq,Fintype
inductive Arr where | input | output
  deriving DecidableEq,Fintype
abbrev State := Store Reg Arr
abbrev Code := NatArrayLanguage.Program Reg Arr

def scanRegisters : Fin 8 ↪ Reg := ⟨![.cursor,.length,.value,.valid,.scanning,.bit,.flag,.one],by decide⟩
def readCell : Code := .seq (atoms [
    .divmod .quotient .column .index .stride,.binary .lt .flag .column .unaryCount])
  (.branch .flag (NatArrayParser.unaryScan scanRegisters .input)
    (atoms [.read .value .input .cursor,.binary .add .cursor .cursor .one]))
def cell : Code := .seq readCell (atoms [
  .write .output .index .value,.binary .add .index .index .one,.binary .sub .todo .todo .one])
def loop : Code := .while .todo cell
def program : Code := .seq (atoms [
  .const .one 1,.const .zero 0,.allocate .output .count .zero,.copy .todo .count,.const .index 0]) loop

theorem drop_cons_info {w : List Bool} {pos : ℕ} {b : Bool} {tail : List Bool}
    (h : w.drop pos=b::tail) :
    ∃ hi : pos<w.length,w[pos]=b ∧ w.drop (pos+1)=tail := by
  have hi : pos<w.length := by
    have hh := congrArg List.length h
    simp only [List.length_drop,List.length_cons] at hh
    omega
  refine ⟨hi,?_,?_⟩
  · have hh := congrArg List.head? h
    simpa only [List.head?_drop,List.head?_cons,List.getElem?_eq_getElem hi,Option.some.injEq] using hh
  · have hh := congrArg List.tail h
    simpa only [List.tail_drop,List.tail_cons] using hh

theorem readCell_scalar_frame {B t : ℕ} {S T : State} (h : Runs B readCell S t T)
    (r : Reg) (hr : r=.length ∨ r=.unaryCount ∨ r=.stride ∨ r=.count ∨ r=.index ∨ r=.todo) :
    T.scalar r=S.scalar r := by
  apply h.scalar_eq_of_not_mem
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [readCell,NatArrayParser.unaryScan,NatArrayParser.unaryStep,atoms,NatArrayLanguage.sequence,
      NatArrayLanguage.Program.scalarWrites,Atom.scalarWrites,scanRegisters]

theorem readCell_array_frame {B t : ℕ} {S T : State} (h : Runs B readCell S t T) (a : Arr) :
    T.array a=S.array a := by
  apply h.array_eq_of_not_mem
  simp [readCell,NatArrayParser.unaryScan,NatArrayParser.unaryStep,atoms,NatArrayLanguage.sequence,
    NatArrayLanguage.Program.arrayWrites,Atom.arrayWrites]

theorem readCell_runs (S : State) (M : ℕ) (w tail : List Bool) (x : Token)
    (bounded : S.Bounded M) (room : 1≤M) (stride : 0<S.scalar .stride) (length : S.scalar .length=w.length)
    (valid : S.scalar .valid=1) (one : S.scalar .one=1)
    (input : S.array .input=w.map bitNat)
    (word : w.drop (S.scalar .cursor)=x.word++tail)
    (kind : x.isNat=decide (S.scalar .index%S.scalar .stride<S.scalar .unaryCount)) :
    ∃t≤7*w.length+14,∃T,Runs (storageBound Reg Arr M) readCell S t T ∧
      T.Bounded M ∧ T.scalar .value=x.value ∧ T.scalar .valid=1 ∧ T.scalar .one=1 ∧
      T.scalar .cursor=S.scalar .cursor+x.word.length ∧ w.drop (T.scalar .cursor)=tail := by
  let pre : List (Atom Reg Arr) := [
    .divmod .quotient .column .index .stride,.binary .lt .flag .column .unaryCount]
  have pv : ValidAtoms M pre S := by
    simp [pre,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,Store.setScalar,BinaryOp.eval,stride,room]
    split_ifs <;> omega
  obtain ⟨pr,hU⟩ := atoms_runs bounded pre pv
  let U := applyAtoms pre S
  have ucursor : U.scalar .cursor=S.scalar .cursor := by simp [U,pre,applyAtoms,Atom.apply,Store.setScalar]
  have ulength : U.scalar .length=w.length := by simp [U,pre,applyAtoms,Atom.apply,Store.setScalar,length]
  have uvalid : U.scalar .valid=1 := by simp [U,pre,applyAtoms,Atom.apply,Store.setScalar,valid]
  have uone : U.scalar .one=1 := by simp [U,pre,applyAtoms,Atom.apply,Store.setScalar,one]
  have uinput : U.array .input=w.map bitNat := input
  have uflag : U.scalar .flag=if S.scalar .index%S.scalar .stride<S.scalar .unaryCount then 1 else 0 := by
    simp [U,pre,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar]
  cases x with
  | nat n =>
    have hk : S.scalar .index%S.scalar .stride<S.scalar .unaryCount := of_decide_eq_true kind.symm
    obtain ⟨T,run,hT,tp,tv,tvalid,ts,tl,tone,ta⟩ := NatArrayParser.unaryScan_success scanRegisters Arr.input
      U w tail (S.scalar .cursor) n M hU room ucursor ulength uvalid uinput (by
        simpa [Token.word,CircuitDescription.natWord,List.append_assoc] using word)
    change T.scalar Reg.cursor=S.scalar Reg.cursor+n+1 at tp
    have hn : n≤w.length := by
      have hh := congrArg List.length word
      simp only [Token.word,CircuitDescription.length_natWord,List.length_append,List.length_drop] at hh
      omega
    refine ⟨2+(7*n+11+1),by omega,T,.seq pr (.branch_nonzero (by rw [uflag,if_pos hk]; decide) run),hT,tv,tvalid,tone,?_,?_⟩
    · simpa [Token.word,CircuitDescription.length_natWord,Nat.add_assoc] using tp
    · have hdrop := congrArg (List.drop (n+1)) word
      rw [tp]
      simpa [Token.word,CircuitDescription.natWord,List.drop_drop,List.drop_append,
        List.length_replicate,List.drop_replicate,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hdrop
  | bit b =>
    have hk : ¬S.scalar .index%S.scalar .stride<S.scalar .unaryCount := of_decide_eq_false kind.symm
    have hw : w.drop (S.scalar .cursor)=b::tail := by simpa [Token.word] using word
    obtain ⟨hi,hbit,htail⟩ := drop_cons_info hw
    have hlenM : w.length≤M := by simpa [length] using bounded.1 Reg.length
    let post : List (Atom Reg Arr) := [.read .value .input .cursor,.binary .add .cursor .cursor .one]
    have postValid : ValidAtoms M post U := by
      simp [post,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar,
        ucursor,uinput,uone,List.length_map]
      omega
    obtain ⟨postRun,hT⟩ := atoms_runs hU post postValid
    let T := applyAtoms post U
    have tp : T.scalar .cursor=S.scalar .cursor+1 := by
      simp [T,post,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,ucursor,uone]
    refine ⟨5,by omega,T,.seq pr (.branch_zero (by rw [uflag,if_neg hk]) postRun),hT,?_,?_,?_,?_,?_⟩
    · simp [T,post,applyAtoms,Atom.apply,Store.setScalar,ucursor,uinput,List.getElem?_eq_getElem hi,hbit,Token.value]
    · simp [T,post,applyAtoms,Atom.apply,Store.setScalar,uvalid]
    · simp [T,post,applyAtoms,Atom.apply,Store.setScalar,uone]
    · simpa [Token.word] using tp
    · simpa [tp] using htail

def tokenValue (xs : List Token) (i : ℕ) : ℕ := (xs[i]?.getD (.nat 0)).value

structure Invariant (xs : List Token) (w tail : List Bool) (M stride un i : ℕ) (S : State) : Prop where
  bounded : S.Bounded M
  length : S.scalar .length=w.length
  valid : S.scalar .valid=1
  one : S.scalar .one=1
  input : S.array .input=w.map bitNat
  stride : S.scalar .stride=stride
  unaryCount : S.scalar .unaryCount=un
  count : S.scalar .count=xs.length
  index : S.scalar .index=i
  todo : S.scalar .todo=xs.length-i
  output : ArrayTabulation.Prefix (tokenValue xs) xs.length i (S.array .output)
  rest : w.drop (S.scalar .cursor)=stream (xs.drop i)++tail

theorem loop_runs (xs : List Token) (w tail : List Bool) (M stride un : ℕ)
    (room : 1≤M) (positive : 0<xs.length → 0<stride)
    (shape : ∀i : Fin xs.length,(xs[i]).isNat=decide (i.val%stride<un))
    (remaining : ℕ) : ∀ (i : ℕ) (S : State),i+remaining=xs.length →
      Invariant xs w tail M stride un i S →
      ∃t≤remaining*(7*w.length+18)+1,∃T,
        Runs (storageBound Reg Arr M) loop S t T ∧ Invariant xs w tail M stride un xs.length T := by
  induction remaining with
  | zero =>
    intro i S hi hS
    have he : i=xs.length := by omega
    subst i
    exact ⟨1,by omega,S,.while_zero (by rw [hS.todo]; omega)
      (Store.size_le_of_bounded hS.bounded),hS⟩
  | succ remaining ih =>
    intro i S hi hS
    have hilt : i<xs.length := by omega
    have hword : w.drop (S.scalar .cursor)=(xs[i]).word++(stream (xs.drop (i+1))++tail) := by
      rw [hS.rest,List.drop_eq_getElem_cons hilt]
      simp only [stream,List.flatMap_cons,List.append_assoc]
    obtain ⟨t,ht,U,readRun,hU,uvalue,uvalid,uone,ucursor,urest⟩ := readCell_runs S M w
      (stream (xs.drop (i+1))++tail) xs[i] hS.bounded room
      (by rw [hS.stride]; exact positive (by omega)) hS.length hS.valid hS.one hS.input hword
      (by simpa only [hS.index,hS.stride,hS.unaryCount] using shape ⟨i,hilt⟩)
    have frame := readCell_scalar_frame readRun
    have ui : U.scalar .index=i := (frame .index (by simp)).trans hS.index
    have ut : U.scalar .todo=xs.length-i := (frame .todo (by simp)).trans hS.todo
    have uc : U.scalar .count=xs.length := (frame .count (by simp)).trans hS.count
    have uout : U.array .output=S.array .output := readCell_array_frame readRun .output
    have uin : U.array .input=w.map bitNat := (readCell_array_frame readRun .input).trans hS.input
    have hlen : (U.array .output).length=xs.length := uout ▸ hS.output.1
    have countM : xs.length≤M := uc ▸ hU.1 Reg.count
    let post : List (Atom Reg Arr) := [.write .output .index .value,
      .binary .add .index .index .one,.binary .sub .todo .todo .one]
    have pv : ValidAtoms M post U := by
      simp [post,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar,
        Store.setArray,ui,ut,uone,hlen,hilt]
      omega
    obtain ⟨postRun,hV⟩ := atoms_runs hU post pv
    let V := applyAtoms post U
    have vi : V.scalar .index=i+1 := by simp [V,post,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,ui,uone]
    have vrest : Invariant xs w tail M stride un (i+1) V := by
      refine ⟨hV,?_,?_,?_,?_,?_,?_,?_,vi,?_,?_,?_⟩
      · simpa [V,post,applyAtoms,Atom.apply,Store.setScalar,Store.setArray] using
          (frame .length (by simp)).trans hS.length
      · simp [V,post,applyAtoms,Atom.apply,Store.setScalar,Store.setArray,uvalid]
      · simp [V,post,applyAtoms,Atom.apply,Store.setScalar,Store.setArray,uone]
      · simp [V,post,applyAtoms,Atom.apply,Store.setScalar,Store.setArray,uin]
      · simpa [V,post,applyAtoms,Atom.apply,Store.setScalar,Store.setArray] using
          (frame .stride (by simp)).trans hS.stride
      · simpa [V,post,applyAtoms,Atom.apply,Store.setScalar,Store.setArray] using
          (frame .unaryCount (by simp)).trans hS.unaryCount
      · simp [V,post,applyAtoms,Atom.apply,Store.setScalar,Store.setArray,uc]
      · simp [V,post,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,ut,uone,Nat.sub_sub]
      · have hv : U.scalar .value=tokenValue xs i := by simpa [tokenValue,List.getElem?_eq_getElem hilt] using uvalue
        have hp := hS.output.write hilt
        simpa [V,post,applyAtoms,Atom.apply,Store.setScalar,Store.setArray,uout,ui,hv] using hp
      · simpa [V,post,applyAtoms,Atom.apply,Store.setScalar,Store.setArray] using urest
    obtain ⟨u,hu,T,run,hT⟩ := ih (i+1) V (by omega) vrest
    refine ⟨t+3+u+1,?_,T,.while_nonzero (by rw [hS.todo]; omega) (.seq readRun postRun) run,hT⟩
    nlinarith

theorem program_runs (xs : List Token) (w tail : List Bool) (M stride un : ℕ)
    (S : State) (bounded : S.Bounded M) (room : 1≤M)
    (length : S.scalar .length=w.length) (valid : S.scalar .valid=1)
    (input : S.array .input=w.map bitNat) (hs : S.scalar .stride=stride)
    (hu : S.scalar .unaryCount=un) (hc : S.scalar .count=xs.length)
    (word : w.drop (S.scalar .cursor)=stream xs++tail)
    (positive : 0<xs.length → 0<stride)
    (shape : ∀i : Fin xs.length,(xs[i]).isNat=decide (i.val%stride<un)) :
    ∃t≤xs.length*(7*w.length+18)+6,∃T,
      Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧
      T.array .output=xs.map Token.value ∧ T.array .input=w.map bitNat ∧
      T.scalar .length=w.length ∧ T.scalar .valid=1 ∧
      w.drop (T.scalar .cursor)=tail := by
  let pre : List (Atom Reg Arr) := [.const .one 1,.const .zero 0,.allocate .output .count .zero,
    .copy .todo .count,.const .index 0]
  have pv : ValidAtoms M pre S := by simp [pre,ValidAtoms,Atom.Valid,Atom.SmallResult,room]
  obtain ⟨pr,hU⟩ := atoms_runs bounded pre pv
  let U := applyAtoms pre S
  have start : Invariant xs w tail M stride un 0 U := by
    refine ⟨hU,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    all_goals try {simp [U,pre,applyAtoms,Atom.apply,Store.setScalar,Store.setArray,length,valid,input,hs,hu,hc,word]}
    simpa [U,pre,applyAtoms,Atom.apply,Store.setScalar,Store.setArray,hc] using
      ArrayTabulation.Prefix.zero (tokenValue xs) xs.length
  obtain ⟨t,ht,T,run,hT⟩ := loop_runs xs w tail M stride un room positive shape xs.length 0 U (by omega) start
  refine ⟨5+t,by omega,T,.seq pr run,hT.bounded,?_,hT.input,hT.length,hT.valid,?_⟩
  · rw [hT.output.complete]
    apply List.ext_getElem (by simp)
    intro i hi hi'
    have hil : i<xs.length := by simpa using hi'
    simp [tokenValue,List.getElem?_eq_getElem hil]
  · simpa [stream] using hT.rest

end GroupWL.MachinePrograms.CircuitRecordParser
