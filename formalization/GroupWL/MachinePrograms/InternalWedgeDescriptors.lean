import GroupWL.MachinePrograms.NatArrayExpressionClient

/-! Concrete descriptor tables for internal wedge coordinates, before the
uniform-coordinate padding is removed by stable selection. -/
namespace GroupWL.MachinePrograms.InternalWedgeDescriptors
open NatArrayLanguage NatArrayExpressions
set_option maxHeartbeats 2500000
set_option maxRecDepth 4096
inductive Field where | u0 | v0 | u1 | v1 | second | keep deriving DecidableEq,Fintype
inductive Reg where | total | index | todo | one | zero | frames | cap | pairs deriving DecidableEq,Fintype
inductive Arr where | dimensions | offsets | pairCodes | output deriving DecidableEq,Fintype
abbrev State := Store Reg Arr
abbrev E := Expr Reg Arr
structure Data where
  frames : ℕ
  cap : ℕ
  vertices : ℕ
  pairs : ℕ
  dimensions : List ℕ
  offsets : List ℕ
  pairCodes : List ℕ

def read (xs : List ℕ) (i : ℕ) := xs[i]?.getD 0
def value (D : Data) (f : Field) (i : ℕ) : ℕ :=
  let vertex := i/D.cap/D.pairs
  let pair := read D.pairCodes (i/D.cap%D.pairs)
  let c := i%D.cap
  let dim := read D.dimensions vertex
  let off := read D.offsets vertex
  match f with
  | .u0 => off+pair/D.frames*dim
  | .v0 => off+pair%D.frames*dim+c
  | .u1 => off+pair/D.frames*dim+c
  | .v1 => off+pair%D.frames*dim
  | .second => if 0<c then 1 else 0
  | .keep => if c<dim then 1 else 0

def add (a b : E) : E := .binary (.binary .add) a b
def mul (a b : E) : E := .binary (.binary .mul) a b
def div (a b : E) : E := .binary .quotient a b
def mod (a b : E) : E := .binary .remainder a b
def vertex : E := div (div (.scalar .index) (.scalar .cap)) (.scalar .pairs)
def pair : E := .read .pairCodes (mod (div (.scalar .index) (.scalar .cap)) (.scalar .pairs))
def coordinate : E := mod (.scalar .index) (.scalar .cap)
def dim : E := .read .dimensions vertex
def off : E := .read .offsets vertex
def left : E := add off (mul (div pair (.scalar .frames)) dim)
def right : E := add off (mul (mod pair (.scalar .frames)) dim)
def expression : Field → E
  | .u0 => left | .v0 => add right coordinate | .u1 => add left coordinate | .v1 => right
  | .second => .binary (.binary .lt) (.const 0) coordinate
  | .keep => .binary (.binary .lt) coordinate dim

def Ready (D : Data) (S : State) : Prop :=
  S.scalar .frames=D.frames ∧ S.scalar .cap=D.cap ∧ S.scalar .pairs=D.pairs ∧
  S.array .dimensions=D.dimensions ∧ S.array .offsets=D.offsets ∧ S.array .pairCodes=D.pairCodes
structure Valid (D : Data) (M : ℕ) : Prop where
  frames : 0<D.frames
  cap : 0<D.cap
  pairs : 0<D.pairs
  dimensions : D.dimensions.length=D.vertices
  offsets : D.offsets.length=D.vertices
  pairCodes : D.pairCodes.length=D.pairs
  dim : ∀v<D.vertices,read D.dimensions v≤D.cap
  offsets_bound : ∀v<D.vertices,read D.offsets v+D.frames*D.cap+D.cap≤M
  codes : ∀j<D.pairs,read D.pairCodes j<D.frames*D.frames
  room : 1≤M

theorem expression_eval (D : Data) (f : Field) (S : State) (h : Ready D S) :
    (expression f).eval S=value D f (S.scalar .index) := by
  rcases h with ⟨hf,hc,hp,hd,ho,hw⟩
  cases f <;> simp [expression,left,right,add,mul,div,mod,vertex,pair,coordinate,dim,off,
    Expr.eval,Op.eval,BinaryOp.eval,value,read,hf,hc,hp,hd,ho,hw]

theorem expression_safe (D : Data) (f : Field) (S : State) (M : ℕ)
    (h : Ready D S) (bounded : S.Bounded M) (valid : Valid D M)
    (index : S.scalar .index<D.vertices*D.pairs*D.cap) : (expression f).Safe M S := by
  rcases h with ⟨hf,hc,hp,hd,ho,hw⟩
  have hi := bounded.1 Reg.index
  have hq := Nat.div_le_self (S.scalar .index) D.cap
  have hv := Nat.div_le_self (S.scalar .index/D.cap) D.pairs
  have hvlt : S.scalar .index/D.cap/D.pairs<D.vertices := by
    apply (Nat.div_lt_iff_lt_mul valid.pairs).2
    apply (Nat.div_lt_iff_lt_mul valid.cap).2
    simpa only [Nat.mul_assoc] using index
  have hj := Nat.mod_lt (S.scalar .index/D.cap) valid.pairs
  have hjb := Nat.mod_le (S.scalar .index/D.cap) D.pairs
  have hclt := Nat.mod_lt (S.scalar .index) valid.cap
  have hcb := Nat.mod_le (S.scalar .index) D.cap
  have hdv := valid.dim _ hvlt
  have hov := valid.offsets_bound _ hvlt
  have hcode := valid.codes _ hj
  have ha : read D.pairCodes (S.scalar .index/D.cap%D.pairs)/D.frames<D.frames :=
    (Nat.div_lt_iff_lt_mul valid.frames).2 hcode
  have hb := Nat.mod_lt (read D.pairCodes (S.scalar .index/D.cap%D.pairs)) valid.frames
  have hab : read D.pairCodes (S.scalar .index/D.cap%D.pairs)/D.frames*
      read D.dimensions (S.scalar .index/D.cap/D.pairs)≤D.frames*D.cap :=
    Nat.mul_le_mul ha.le hdv
  have hbb : read D.pairCodes (S.scalar .index/D.cap%D.pairs)%D.frames*
      read D.dimensions (S.scalar .index/D.cap/D.pairs)≤D.frames*D.cap :=
    Nat.mul_le_mul hb.le hdv
  have hcapM : D.cap≤M := by omega
  have hframeM : D.frames≤M := by simpa [hf] using bounded.1 Reg.frames
  have hM := valid.room
  simp only [read] at hdv hov hcode ha hb hab hbb
  cases f <;>
    simp [expression,left,right,add,mul,div,mod,vertex,pair,coordinate,dim,off,
      Expr.Safe,Expr.eval,Op.valid,Op.eval,BinaryOp.eval,hf,hc,hp,hd,ho,hw,
      valid.frames,valid.cap,valid.pairs,valid.dimensions,valid.offsets,valid.pairCodes]
  all_goals (try split_ifs) <;> omega

def registers : Fin 5 ↪ Reg := ⟨![.total,.index,.todo,.one,.zero],by decide⟩
def program (f : Field) := tableProgram (expression f) registers Arr.output

theorem program_runs (D : Data) (f : Field) (M : ℕ) (valid : Valid D M)
    (S : Store (Registers Reg (expression f).need) Arr) (bounded : S.Bounded M)
    (ready : Ready D (inputs S)) (total : S.scalar (.inl .total)=D.vertices*D.pairs*D.cap) :
    ∃t≤(D.vertices*D.pairs*D.cap)*((expression f).cost+4)+6,∃U,
      Runs (storageBound (Registers Reg (expression f).need) Arr M) (program f) S t U ∧
      U.Bounded M ∧ Ready D (inputs U) ∧
      U.array .output=List.ofFn (fun i : Fin (D.vertices*D.pairs*D.cap)=>value D f i) := by
  apply tableProgram_runs (expression f) registers .output (Ready D) (value D f) M
    (D.vertices*D.pairs*D.cap) valid.room
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

end GroupWL.MachinePrograms.InternalWedgeDescriptors
