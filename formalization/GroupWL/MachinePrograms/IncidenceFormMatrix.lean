import GroupWL.MachinePrograms.NatArrayExpressionClient

/-! Concrete identity and readout-projection coefficient matrix. -/
namespace GroupWL.MachinePrograms.IncidenceFormMatrix
open NatArrayLanguage NatArrayExpressions
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
inductive Reg where | total | index | todo | one | zero | frames | blocks | readouts | oldInput deriving DecidableEq,Fintype
inductive Arr where | dimensions | offsets | incidences | radicals | output deriving DecidableEq,Fintype
abbrev State := Store Reg Arr
abbrev E := Expr Reg Arr
structure Data where
  frames : ℕ
  blocks : ℕ
  readouts : ℕ
  edges : ℕ
  oldInput : ℕ
  dimensions : List ℕ
  offsets : List ℕ
  incidences : List ℕ
  radicals : List ℕ

def read (xs : List ℕ) (i : ℕ) := xs[i]?.getD 0
def forms (D : Data) := D.oldInput+D.edges*D.frames*2
def value (D : Data) (i : ℕ) : ℕ :=
  let row := i/D.oldInput
  let col := i%D.oldInput
  if row<D.oldInput then (if row=col then 1 else 0) else
  let t := row-D.oldInput
  let edge := t/2/D.frames
  let frame := t/2%D.frames
  let code := read D.incidences edge
  let vertex := D.blocks+code%D.readouts
  let dim := read D.dimensions vertex
  let start := read D.offsets vertex+frame*dim
  if t%2=0 then (if col=start then 1 else 0) else
  if start<col ∧ col<start+dim then read D.radicals (code*D.blocks+(col-start-1)) else 0

def add (a b : E) : E := .binary (.binary .add) a b
def sub (a b : E) : E := .binary (.binary .sub) a b
def mul (a b : E) : E := .binary (.binary .mul) a b
def div (a b : E) : E := .binary .quotient a b
def mod (a b : E) : E := .binary .remainder a b
def eq (a b : E) : E := .binary (.binary .eq) a b
def lt (a b : E) : E := .binary (.binary .lt) a b
def row : E := div (.scalar .index) (.scalar .oldInput)
def col : E := mod (.scalar .index) (.scalar .oldInput)
def tailRow : E := sub row (.scalar .oldInput)
def edge : E := div (div tailRow (.const 2)) (.scalar .frames)
def frame : E := mod (div tailRow (.const 2)) (.scalar .frames)
def code : E := .read .incidences edge
def vertex : E := add (.scalar .blocks) (mod code (.scalar .readouts))
def dim : E := .read .dimensions vertex
def start : E := add (.read .offsets vertex) (mul frame dim)
def radicalAddress : E := add (mul code (.scalar .blocks)) (sub (sub col start) (.const 1))
def radicalValue : E := .branch (lt start col) (.branch (lt col (add start dim)) (.read .radicals radicalAddress) (.const 0)) (.const 0)
def expression : E := .branch (lt row (.scalar .oldInput)) (eq row col)
  (.branch (eq (mod tailRow (.const 2)) (.const 0)) (eq col start) radicalValue)

def Ready (D : Data) (S : State) : Prop :=
  S.scalar .frames=D.frames ∧ S.scalar .blocks=D.blocks ∧ S.scalar .readouts=D.readouts ∧ S.scalar .oldInput=D.oldInput ∧
  S.array .dimensions=D.dimensions ∧ S.array .offsets=D.offsets ∧ S.array .incidences=D.incidences ∧ S.array .radicals=D.radicals
structure Valid (D : Data) : Prop where
  frames : 0<D.frames
  readouts : 0<D.readouts
  oldInput : 0<D.oldInput
  dimensions : D.dimensions.length=D.blocks+D.readouts
  offsets : D.offsets.length=D.blocks+D.readouts
  incidences : D.incidences.length=D.edges
  radicals : D.radicals.length=D.blocks*D.readouts*D.blocks
  dims : ∀v<D.blocks+D.readouts,read D.dimensions v≤D.blocks+1
  offsets_bound : ∀v<D.blocks+D.readouts,read D.offsets v+D.frames*read D.dimensions v≤D.oldInput
  codes : ∀j<D.edges,read D.incidences j<D.blocks*D.readouts

theorem expression_eval (D : Data) (S : State) (h : Ready D S) : expression.eval S=value D (S.scalar .index) := by
  rcases h with ⟨hf,hb,hr,hn,hd,ho,he,hz⟩
  simp [expression,radicalValue,radicalAddress,start,dim,vertex,code,edge,frame,tailRow,row,col,
    add,sub,mul,div,mod,eq,lt,Expr.eval,Op.eval,BinaryOp.eval,value,read,hf,hb,hr,hn,hd,ho,he,hz]
  split_ifs <;> omega

theorem expression_safe (D : Data) (S : State) (M : ℕ) (h : Ready D S) (bounded : S.Bounded M)
    (valid : Valid D) (room : 2≤M) (index : S.scalar .index<forms D*D.oldInput) : expression.Safe M S := by
  rcases h with ⟨hf,hb,hr,hn,hd,ho,he,hz⟩
  have hi := bounded.1 Reg.index
  have hnM : D.oldInput≤M := by simpa [hn] using bounded.1 Reg.oldInput
  have hrow := Nat.div_le_self (S.scalar .index) D.oldInput
  have hcol := Nat.mod_lt (S.scalar .index) valid.oldInput
  have hrowlt : S.scalar .index/D.oldInput<forms D := (Nat.div_lt_iff_lt_mul valid.oldInput).2 index
  by_cases hfirst : S.scalar .index/D.oldInput<D.oldInput
  · simp [expression,row,col,lt,eq,div,mod,Expr.Safe,Expr.eval,Op.valid,Op.eval,BinaryOp.eval,hn,valid.oldInput,hfirst]
    split_ifs <;> omega
  · have ht : S.scalar .index/D.oldInput-D.oldInput<D.edges*D.frames*2 := by unfold forms at hrowlt; omega
    have he2 : (S.scalar .index/D.oldInput-D.oldInput)/2<D.edges*D.frames :=
      (Nat.div_lt_iff_lt_mul (by decide : 0<2)).2 ht
    have hie : (S.scalar .index/D.oldInput-D.oldInput)/2/D.frames<D.edges :=
      (Nat.div_lt_iff_lt_mul valid.frames).2 he2
    have hfr := Nat.mod_lt ((S.scalar .index/D.oldInput-D.oldInput)/2) valid.frames
    have hcode := valid.codes _ hie
    have hv : D.blocks+read D.incidences ((S.scalar .index/D.oldInput-D.oldInput)/2/D.frames)%D.readouts<D.blocks+D.readouts := by
      have := Nat.mod_lt (read D.incidences ((S.scalar .index/D.oldInput-D.oldInput)/2/D.frames)) valid.readouts; omega
    have hdim := valid.dims _ hv
    have hoff := valid.offsets_bound _ hv
    have hm := Nat.mul_le_mul_right (read D.dimensions (D.blocks+read D.incidences ((S.scalar .index/D.oldInput-D.oldInput)/2/D.frames)%D.readouts))
      (show (S.scalar .index/D.oldInput-D.oldInput)/2%D.frames+1≤D.frames by omega)
    have hxlen : D.blocks+D.readouts≤M := by rw [←valid.dimensions,←hd]; exact bounded.2.1 Arr.dimensions
    have hzlen : D.blocks*D.readouts*D.blocks≤M := by rw [←valid.radicals,←hz]; exact bounded.2.1 Arr.radicals
    have hmul := Nat.mul_le_mul_right D.blocks (show read D.incidences ((S.scalar .index/D.oldInput-D.oldInput)/2/D.frames)+1≤D.blocks*D.readouts by omega)
    have hdiv2 := Nat.div_le_self (S.scalar .index/D.oldInput-D.oldInput) 2
    have hdivq := Nat.div_le_self ((S.scalar .index/D.oldInput-D.oldInput)/2) D.frames
    have hmodq := Nat.mod_le ((S.scalar .index/D.oldInput-D.oldInput)/2) D.frames
    simp only [read,Nat.add_mul,Nat.one_mul] at hcode hv hdim hoff hm hmul
    simp [expression,radicalValue,radicalAddress,start,dim,vertex,code,edge,frame,tailRow,row,col,
      add,sub,mul,div,mod,eq,lt,Expr.Safe,Expr.eval,Op.valid,Op.eval,BinaryOp.eval,
      hf,hb,hr,hn,hd,ho,he,hz,valid.frames,valid.readouts,valid.oldInput,
      valid.dimensions,valid.offsets,valid.incidences,valid.radicals,hfirst]
    split_ifs <;> omega

def registers : Fin 5 ↪ Reg := ⟨![.total,.index,.todo,.one,.zero],by decide⟩
def program := tableProgram expression registers Arr.output

theorem program_runs (D : Data) (M : ℕ) (valid : Valid D) (room : 2≤M)
    (S : Store (Registers Reg expression.need) Arr) (bounded : S.Bounded M)
    (ready : Ready D (inputs S)) (total : S.scalar (.inl .total)=forms D*D.oldInput) :
    ∃t≤(forms D*D.oldInput)*(expression.cost+4)+6,∃U,
      Runs (storageBound (Registers Reg expression.need) Arr M) program S t U ∧ U.Bounded M ∧
      Ready D (inputs U) ∧ U.array .output=List.ofFn (fun i : Fin (forms D*D.oldInput)=>value D i) := by
  apply tableProgram_runs expression registers .output (Ready D) (value D) M (forms D*D.oldInput) (by omega)
  · intro V hV i x
    fin_cases i <;> simpa [Ready,registers,Store.setScalar] using hV
  · intro V hV xs
    simpa [Ready,Store.setArray] using hV
  · intro V hV hB hi
    exact expression_safe D V M hV hB valid room hi
  · intro V hV hi
    exact expression_eval D V hV
  · exact bounded
  · exact ready
  · exact total

end GroupWL.MachinePrograms.IncidenceFormMatrix
