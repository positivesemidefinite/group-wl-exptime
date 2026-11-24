import GroupWL.MachinePrograms.InternalWedgeDescriptors

/-! Exact constant-width incidence descriptors for the obstruction matrix. -/
namespace GroupWL.MachinePrograms.EdgeWedgeDescriptors
open NatArrayLanguage NatArrayExpressions
set_option maxHeartbeats 2500000
set_option maxRecDepth 4096
abbrev Field := InternalWedgeDescriptors.Field
inductive Reg where | total | index | todo | one | zero | frames | readouts | oldInput deriving DecidableEq,Fintype
inductive Arr where | offsets | incidences | output deriving DecidableEq,Fintype
abbrev State := Store Reg Arr
abbrev E := Expr Reg Arr
structure Data where
  frames : ℕ
  readouts : ℕ
  blocks : ℕ
  edges : ℕ
  oldInput : ℕ
  offsets : List ℕ
  incidences : List ℕ

def read (xs : List ℕ) (i : ℕ) := xs[i]?.getD 0
def value (D : Data) (f : Field) (i : ℕ) : ℕ :=
  let edge := i/2/D.frames/D.frames
  let a := i/2/D.frames%D.frames
  let b := i/2%D.frames
  let c := i%2
  let block := read D.incidences edge/D.readouts
  let u := read D.offsets block+a*2
  let v := D.oldInput+(edge*D.frames+b)*2
  match f with
  | .u0 => u | .v0 => v+c | .u1 => u+c | .v1 => v
  | .second => if 0<c then 1 else 0
  | .keep => 1

def add (a b : E) : E := .binary (.binary .add) a b
def mul (a b : E) : E := .binary (.binary .mul) a b
def div (a b : E) : E := .binary .quotient a b
def mod (a b : E) : E := .binary .remainder a b
def firstQuotient : E := div (.scalar .index) (.const 2)
def secondQuotient : E := div firstQuotient (.scalar .frames)
def edge : E := div secondQuotient (.scalar .frames)
def a : E := mod secondQuotient (.scalar .frames)
def b : E := mod firstQuotient (.scalar .frames)
def coordinate : E := mod (.scalar .index) (.const 2)
def block : E := div (.read .incidences edge) (.scalar .readouts)
def left : E := add (.read .offsets block) (mul a (.const 2))
def right : E := add (.scalar .oldInput) (mul (add (mul edge (.scalar .frames)) b) (.const 2))
def expression : Field → E
  | .u0 => left | .v0 => add right coordinate | .u1 => add left coordinate | .v1 => right
  | .second => .binary (.binary .lt) (.const 0) coordinate
  | .keep => .const 1

def Ready (D : Data) (S : State) : Prop :=
  S.scalar .frames=D.frames ∧ S.scalar .readouts=D.readouts ∧ S.scalar .oldInput=D.oldInput ∧
  S.array .offsets=D.offsets ∧ S.array .incidences=D.incidences
structure Valid (D : Data) (M : ℕ) : Prop where
  frames : 0<D.frames
  readouts : 0<D.readouts
  offsets : D.blocks≤D.offsets.length
  incidences : D.incidences.length=D.edges
  offsets_bound : ∀v<D.blocks,read D.offsets v+D.frames*2+1≤M
  codes : ∀j<D.edges,read D.incidences j<D.blocks*D.readouts
  forms : D.oldInput+D.edges*D.frames*2≤M
  room : 2≤M

theorem expression_eval (D : Data) (f : Field) (S : State) (h : Ready D S) :
    (expression f).eval S=value D f (S.scalar .index) := by
  rcases h with ⟨hf,hr,hn,ho,he⟩
  cases f <;> simp [expression,left,right,add,mul,div,mod,firstQuotient,secondQuotient,edge,a,b,coordinate,block,
    Expr.eval,Op.eval,BinaryOp.eval,value,read,hf,hr,hn,ho,he]

theorem expression_safe (D : Data) (f : Field) (S : State) (M : ℕ)
    (h : Ready D S) (bounded : S.Bounded M) (valid : Valid D M)
    (index : S.scalar .index<D.edges*D.frames*D.frames*2) : (expression f).Safe M S := by
  rcases h with ⟨hf,hr,hn,ho,he⟩
  have hi := bounded.1 Reg.index
  have hq := Nat.div_le_self (S.scalar .index) 2
  have hq2 := Nat.div_le_self (S.scalar .index/2) D.frames
  have hq3 := Nat.div_le_self (S.scalar .index/2/D.frames) D.frames
  have hi2 : S.scalar .index/2<D.edges*D.frames*D.frames :=
    (Nat.div_lt_iff_lt_mul (by decide : 0<2)).2 index
  have hiq : S.scalar .index/2/D.frames<D.edges*D.frames :=
    (Nat.div_lt_iff_lt_mul valid.frames).2 hi2
  have hie : S.scalar .index/2/D.frames/D.frames<D.edges :=
    (Nat.div_lt_iff_lt_mul valid.frames).2 hiq
  have ha := Nat.mod_lt (S.scalar .index/2/D.frames) valid.frames
  have hb := Nat.mod_lt (S.scalar .index/2) valid.frames
  have hc := Nat.mod_lt (S.scalar .index) (by decide : 0<2)
  have code := valid.codes _ hie
  have hv : read D.incidences (S.scalar .index/2/D.frames/D.frames)/D.readouts<D.blocks :=
    (Nat.div_lt_iff_lt_mul valid.readouts).2 code
  have hoff := valid.offsets_bound _ hv
  have hblock := Nat.div_le_self (read D.incidences (S.scalar .index/2/D.frames/D.frames)) D.readouts
  have readBound : read D.incidences (S.scalar .index/2/D.frames/D.frames)≤M := by
    have hlen : S.scalar .index/2/D.frames/D.frames<(S.array .incidences).length := by rw [he,valid.incidences]; exact hie
    have := bounded.2.2 Arr.incidences ((S.array .incidences)[S.scalar .index/2/D.frames/D.frames]'hlen)
      (List.getElem_mem hlen)
    rw [read,←he,List.getElem?_eq_getElem hlen,Option.getD_some]
    exact this
  have hm := Nat.mul_le_mul_right D.frames (show S.scalar .index/2/D.frames/D.frames+1≤D.edges by omega)
  have hpos : (S.scalar .index/2/D.frames/D.frames*D.frames+S.scalar .index/2%D.frames)*2+S.scalar .index%2≤D.edges*D.frames*2 := by nlinarith
  have hforms := valid.forms
  have hM := valid.room
  have hfM : D.frames≤M := by simpa [hf] using bounded.1 Reg.frames
  have hvlen := hv.trans_le valid.offsets
  simp only [read] at code hv hoff hblock readBound hvlen
  cases f <;>
    simp [expression,left,right,add,mul,div,mod,firstQuotient,secondQuotient,edge,a,b,coordinate,block,
      Expr.Safe,Expr.eval,Op.valid,Op.eval,BinaryOp.eval,hf,hr,hn,ho,he,
      valid.frames,valid.readouts,valid.incidences]
  all_goals (try split_ifs) <;> omega

def registers : Fin 5 ↪ Reg := ⟨![.total,.index,.todo,.one,.zero],by decide⟩
def program (f : Field) := tableProgram (expression f) registers Arr.output

theorem program_runs (D : Data) (f : Field) (M : ℕ) (valid : Valid D M)
    (S : Store (Registers Reg (expression f).need) Arr) (bounded : S.Bounded M)
    (ready : Ready D (inputs S)) (total : S.scalar (.inl .total)=D.edges*D.frames*D.frames*2) :
    ∃t≤(D.edges*D.frames*D.frames*2)*((expression f).cost+4)+6,∃U,
      Runs (storageBound (Registers Reg (expression f).need) Arr M) (program f) S t U ∧
      U.Bounded M ∧ Ready D (inputs U) ∧
      U.array .output=List.ofFn (fun i : Fin (D.edges*D.frames*D.frames*2)=>value D f i) := by
  apply tableProgram_runs (expression f) registers .output (Ready D) (value D f) M
    (D.edges*D.frames*D.frames*2) (by have := valid.room; omega)
  · intro V hV i x
    fin_cases i <;> simpa [Ready,registers,Store.setScalar] using hV
  · intro V hV xs
    simpa [Ready,Store.setArray] using hV
  · intro V hV hB hi
    exact expression_safe D f V M hV hB valid hi
  · intro V hV hi
    exact expression_eval D f V hV
  · exact bounded
  · exact ready
  · exact total

end GroupWL.MachinePrograms.EdgeWedgeDescriptors
