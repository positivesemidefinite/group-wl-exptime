import GroupWL.MachinePrograms.NatArrayExpressionClient
import GroupWL.MachinePrograms.MatrixArithmetic

/-! Explicit arithmetic for a sum of at most two coordinate wedges. -/
namespace GroupWL.MachinePrograms.WedgeConstraints
open NatArrayLanguage NatArrayExpressions
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

structure Descriptors where
  u0 : List ℕ
  v0 : List ℕ
  u1 : List ℕ
  v1 : List ℕ
  second : List ℕ

def Descriptors.Valid (D : Descriptors) (outputs forms : ℕ) : Prop :=
  D.u0.length=outputs ∧ D.v0.length=outputs ∧ D.u1.length=outputs ∧
  D.v1.length=outputs ∧ D.second.length=outputs ∧
  (∀x∈D.u0,x<forms) ∧ (∀x∈D.v0,x<forms) ∧
  (∀x∈D.u1,x<forms) ∧ (∀x∈D.v1,x<forms)

def wedge (p a b c d : ℕ) := (a*b%p+p-c*d%p)%p
def term (E H : List ℕ) (p n k a b row col : ℕ) :=
  wedge p (MatrixArithmetic.read H (a*k+row)) (MatrixArithmetic.read E (b*n+col))
    (MatrixArithmetic.read H (b*k+row)) (MatrixArithmetic.read E (a*n+col))
def value (D : Descriptors) (E H : List ℕ) (p n k row col z : ℕ) :=
  (term E H p n k (MatrixArithmetic.read D.u0 z) (MatrixArithmetic.read D.v0 z) row col+
    if MatrixArithmetic.read D.second z=0 then 0 else
      term E H p n k (MatrixArithmetic.read D.u1 z) (MatrixArithmetic.read D.v1 z) row col)%p

inductive Reg where
  | total | index | remaining | one | zero | modulus | oldInput | oldOutput | input | output | width
  deriving DecidableEq,Fintype
inductive Arr where | u0 | v0 | u1 | v1 | second | forms | chosen | result
  deriving DecidableEq,Fintype
abbrev Base := Store Reg Arr
abbrev X := Expr Reg Arr
def c (n : ℕ) : X := .const n
def s (r : Reg) : X := .scalar r
def add (a b : X) : X := .binary (.binary .add) a b
def sub (a b : X) : X := .binary (.binary .sub) a b
def mul (a b : X) : X := .binary (.binary .mul) a b
def div (a b : X) : X := .binary .quotient a b
def mod (a b : X) : X := .binary .remainder a b
def lt (a b : X) : X := .binary (.binary .lt) a b
def col : X := mod (div (s .index) (s .output)) (s .input)
def row : X := div (s .index) (mul (s .input) (s .output))
def out : X := mod (s .index) (s .output)
def descriptor (a : Arr) : X := .read a out
def formRead (a : Arr) : X := .read .forms (add (mul (descriptor a) (s .oldInput)) col)
def chosenRead (a : Arr) : X := .read .chosen (add (mul (descriptor a) (s .width)) row)
def wedgeExpr (a b : Arr) : X := mod
  (sub (add (mod (mul (chosenRead a) (formRead b)) (s .modulus)) (s .modulus))
    (mod (mul (chosenRead b) (formRead a)) (s .modulus))) (s .modulus)
def expression : X := .branch (lt out (s .oldOutput))
  (.branch (lt col (s .oldInput))
    (mod (add (wedgeExpr .u0 .v0)
      (.branch (descriptor .second) (wedgeExpr .u1 .v1) (c 0))) (s .modulus)) (c 0)) (c 0)
def registers : Fin 5 ↪ Reg := ⟨![.total,.index,.remaining,.one,.zero],by decide⟩
abbrev State := Store (Registers Reg expression.need) Arr
def program := tableProgram expression registers Arr.result

def entry (D : Descriptors) (E H : List ℕ) (p n oldOut k ni no index : ℕ) :=
  if index%no<oldOut ∧ index/no%ni<n then
    value D E H p n k (index/(ni*no)) (index/no%ni) (index%no) else 0

def Ready (D : Descriptors) (E H : List ℕ) (p n oldOut k ni no : ℕ) (S : Base) : Prop :=
  S.scalar .modulus=p ∧ S.scalar .oldInput=n ∧ S.scalar .oldOutput=oldOut ∧
  S.scalar .width=k ∧ S.scalar .input=ni ∧ S.scalar .output=no ∧
  S.array .u0=D.u0 ∧ S.array .v0=D.v0 ∧ S.array .u1=D.u1 ∧ S.array .v1=D.v1 ∧
  S.array .second=D.second ∧ S.array .forms=E ∧ S.array .chosen=H

theorem expression_eval (D : Descriptors) (E H : List ℕ) (p n oldOut k ni no : ℕ)
    (S : Base) (h : Ready D E H p n oldOut k ni no S) :
    expression.eval S=entry D E H p n oldOut k ni no (S.scalar .index) := by
  rcases h with ⟨hp,hn,ho,hk,hni,hno,hu0,hv0,hu1,hv1,hsecond,hE,hH⟩
  simp [expression,wedgeExpr,chosenRead,formRead,descriptor,out,row,col,lt,mod,div,mul,sub,add,c,s,
    Expr.eval,Op.eval,BinaryOp.eval,hp,hn,ho,hk,hni,hno,hu0,hv0,hu1,hv1,hsecond,hE,hH,
    entry,value,term,wedge,MatrixArithmetic.read]
  split_ifs <;> simp_all <;> omega

theorem safe_add {a b : X} {S : Base} {M : ℕ} (ha : a.Safe M S) (hb : b.Safe M S)
    (h : a.eval S+b.eval S≤M) : (add a b).Safe M S := ⟨ha,hb,trivial,h⟩
theorem safe_sub {a b : X} {S : Base} {M : ℕ} (ha : a.Safe M S) (hb : b.Safe M S)
    (h : a.eval S≤M) : (sub a b).Safe M S := ⟨ha,hb,trivial,(Nat.sub_le _ _).trans h⟩
theorem safe_mul {a b : X} {S : Base} {M : ℕ} (ha : a.Safe M S) (hb : b.Safe M S)
    (h : a.eval S*b.eval S≤M) : (mul a b).Safe M S := ⟨ha,hb,trivial,h⟩
theorem safe_div {a b : X} {S : Base} {M : ℕ} (ha : a.Safe M S) (hb : b.Safe M S)
    (hp : 0<b.eval S) (h : a.eval S≤M) : (div a b).Safe M S :=
  ⟨ha,hb,hp,(Nat.div_le_self _ _).trans h⟩
theorem safe_mod {a b : X} {S : Base} {M : ℕ} (ha : a.Safe M S) (hb : b.Safe M S)
    (hp : 0<b.eval S) (h : b.eval S≤M) : (mod a b).Safe M S :=
  ⟨ha,hb,hp,(Nat.mod_lt _ hp).le.trans h⟩
theorem safe_lt {a b : X} {S : Base} {M : ℕ} (ha : a.Safe M S) (hb : b.Safe M S)
    (h : 1≤M) : (lt a b).Safe M S := by
  refine ⟨ha,hb,trivial,?_⟩
  change (if a.eval S<b.eval S then 1 else 0)≤M
  split_ifs <;> omega

theorem expression_safe (D : Descriptors) (E H : List ℕ) (p n oldOut k ni no f M : ℕ)
    (hp : 0<p) (hM : 1≤M) (hpM : p*p+2*p≤M) (hnino : ni*no≤M)
    (hE : E.length=f*n) (hH : H.length=f*k) (ev : ∀x∈E,x<p) (hv : ∀x∈H,x<p)
    (valid : D.Valid oldOut f) (S : Base) (bounded : S.Bounded M)
    (ready : Ready D E H p n oldOut k ni no S) (hi : S.scalar .index<k*ni*no) :
    expression.Safe M S := by
  rcases ready with ⟨hsp,hsn,hso,hsk,hsni,hsno,hu0,hv0,hu1,hv1,hsecond,hsE,hsH⟩
  have hni : 0<ni := Nat.pos_of_ne_zero (by intro h; rw [h] at hi; simp at hi)
  have hno : 0<no := Nat.pos_of_ne_zero (by intro h; rw [h] at hi; simp at hi)
  have hk : 0<k := Nat.pos_of_ne_zero (by intro h; rw [h] at hi; simp at hi)
  have hscalar (r : Reg) : (s r).Safe M S := trivial
  have heval (r : Reg) : (s r).eval S=S.scalar r := rfl
  have hidx : (s .index).eval S≤M := bounded.1 _
  have hinput : (s .input).eval S≤M := bounded.1 _
  have houtput : (s .output).eval S≤M := bounded.1 _
  have hcol : col.Safe M S := safe_mod
    (safe_div (hscalar _) (hscalar _) (by simpa [heval,hsno] using hno) hidx)
    (hscalar _) (by simpa [heval,hsni] using hni) hinput
  have hout : out.Safe M S := safe_mod (hscalar _) (hscalar _)
    (by simpa [heval,hsno] using hno) houtput
  have hrow : row.Safe M S := safe_div (hscalar _)
    (safe_mul (hscalar _) (hscalar _) (by simpa [heval,hsni,hsno] using hnino))
    (by change 0<S.scalar .input*S.scalar .output; rw [hsni,hsno]; positivity) hidx
  have erow : row.eval S=S.scalar .index/(ni*no) := by simp [row,div,mul,s,Expr.eval,Op.eval,BinaryOp.eval,hsni,hsno]
  have ecol : col.eval S=S.scalar .index/no%ni := by simp [col,mod,div,s,Expr.eval,Op.eval,hsni,hsno]
  have eout : out.eval S=S.scalar .index%no := by simp [out,mod,s,Expr.eval,Op.eval,hsno]
  have hrowk : row.eval S<k := by rw [erow]; apply (Nat.div_lt_iff_lt_mul (by positivity)).2; nlinarith
  have hcolni : col.eval S<ni := by rw [ecol]; exact Nat.mod_lt _ hni
  have houtno : out.eval S<no := by rw [eout]; exact Nat.mod_lt _ hno
  have houttest : (lt out (s .oldOutput)).Safe M S := safe_lt hout (hscalar _) hM
  have hcoltest : (lt col (s .oldInput)).Safe M S := safe_lt hcol (hscalar _) hM
  refine ⟨houttest,?_⟩
  by_cases hzo : out.eval S<oldOut
  · simp only [lt,s,Expr.eval,Op.eval,BinaryOp.eval,hso,if_pos hzo,Nat.one_ne_zero,if_false]
    refine ⟨hcoltest,?_⟩
    by_cases hcn : col.eval S<n
    · simp only [lt,s,Expr.eval,Op.eval,BinaryOp.eval,hsn,if_pos hcn,Nat.one_ne_zero,if_false]
      have hdlen (a : Arr) (ha : a=.u0 ∨ a=.v0 ∨ a=.u1 ∨ a=.v1 ∨ a=.second) :
          (S.array a).length=oldOut := by
        rcases ha with rfl|rfl|rfl|rfl|rfl <;> simp only [hu0,hv0,hu1,hv1,hsecond]
        · exact valid.1
        · exact valid.2.1
        · exact valid.2.2.1
        · exact valid.2.2.2.1
        · exact valid.2.2.2.2.1
      have hdSafe (a : Arr) (ha : a=.u0 ∨ a=.v0 ∨ a=.u1 ∨ a=.v1 ∨ a=.second) :
          (descriptor a).Safe M S := ⟨hout,by rw [hdlen a ha]; exact hzo⟩
      have hdval (a : Arr) (ha : a=.u0 ∨ a=.v0 ∨ a=.u1 ∨ a=.v1) : (descriptor a).eval S<f := by
        have values : ∀x∈S.array a,x<f := by
          rcases ha with rfl|rfl|rfl|rfl
          · simpa only [hu0] using valid.2.2.2.2.2.1
          · simpa only [hv0] using valid.2.2.2.2.2.2.1
          · simpa only [hu1] using valid.2.2.2.2.2.2.2.1
          · simpa only [hv1] using valid.2.2.2.2.2.2.2.2
        have hia : out.eval S<(S.array a).length := by rw [hdlen a (by tauto)]; exact hzo
        simpa only [descriptor,Expr.eval,List.getElem?_eq_getElem hia,Option.getD_some] using
          values ((S.array a)[out.eval S]) (List.getElem_mem hia)
      have chosenSafe (a : Arr) (ha : a=.u0 ∨ a=.v0 ∨ a=.u1 ∨ a=.v1) :
          (chosenRead a).Safe M S := by
        have hlt : (descriptor a).eval S*k+row.eval S<(S.array .chosen).length := by
          rw [hsH,hH]; nlinarith [hdval a ha]
        have hlen := bounded.2.1 Arr.chosen
        refine ⟨safe_add (safe_mul (hdSafe a (by tauto)) (hscalar _) ?_) hrow ?_,?_⟩
        all_goals change _
        · simp only [s,Expr.eval,hsk]; nlinarith
        · simpa only [mul,s,Expr.eval,Op.eval,BinaryOp.eval,hsk] using hlt.le.trans hlen
        · simpa only [add,mul,s,Expr.eval,Op.eval,BinaryOp.eval,hsk] using hlt
      have formSafe (a : Arr) (ha : a=.u0 ∨ a=.v0 ∨ a=.u1 ∨ a=.v1) :
          (formRead a).Safe M S := by
        have hlt : (descriptor a).eval S*n+col.eval S<(S.array .forms).length := by
          rw [hsE,hE]; nlinarith [hdval a ha]
        have hlen := bounded.2.1 Arr.forms
        refine ⟨safe_add (safe_mul (hdSafe a (by tauto)) (hscalar _) ?_) hcol ?_,?_⟩
        · simp only [s,Expr.eval,hsn]; nlinarith
        · simpa only [mul,s,Expr.eval,Op.eval,BinaryOp.eval,hsn] using hlt.le.trans hlen
        · simpa only [add,mul,s,Expr.eval,Op.eval,BinaryOp.eval,hsn] using hlt
      have chosenLt (a : Arr) : (chosenRead a).eval S<p := by
        change MatrixArithmetic.read (S.array .chosen) _<p
        rw [hsH]
        exact MatrixArithmetic.read_lt hv hp _
      have formLt (a : Arr) : (formRead a).eval S<p := by
        change MatrixArithmetic.read (S.array .forms) _<p
        rw [hsE]
        exact MatrixArithmetic.read_lt ev hp _
      have wedgeSafe (a b : Arr) (ha : a=.u0 ∨ a=.v0 ∨ a=.u1 ∨ a=.v1)
          (hb : b=.u0 ∨ b=.v0 ∨ b=.u1 ∨ b=.v1) : (wedgeExpr a b).Safe M S := by
        have prodSafe (a b : Arr) (ha : a=.u0 ∨ a=.v0 ∨ a=.u1 ∨ a=.v1)
            (hb : b=.u0 ∨ b=.v0 ∨ b=.u1 ∨ b=.v1) :=
          safe_mul (chosenSafe a ha) (formSafe b hb) (by nlinarith [chosenLt a,formLt b])
        have modSafe (a b : Arr) (ha : a=.u0 ∨ a=.v0 ∨ a=.u1 ∨ a=.v1)
            (hb : b=.u0 ∨ b=.v0 ∨ b=.u1 ∨ b=.v1) :=
          safe_mod (prodSafe a b ha hb) (hscalar .modulus) (by simpa [s,Expr.eval,hsp] using hp)
            (by simp only [s,Expr.eval,hsp]; omega)
        have hl : (mod (mul (chosenRead a) (formRead b)) (s .modulus)).eval S<p := by
          change _%S.scalar .modulus<p
          rw [hsp]; exact Nat.mod_lt _ hp
        apply safe_mod _ (hscalar _) (by simpa [s,Expr.eval,hsp] using hp) (by simp [s,Expr.eval,hsp]; omega)
        apply safe_sub (safe_add (modSafe a b ha hb) (hscalar _) (by change (mod (mul (chosenRead a) (formRead b)) (s .modulus)).eval S+S.scalar .modulus≤M; rw [hsp]; omega))
          (modSafe b a hb ha)
        change (mod (mul (chosenRead a) (formRead b)) (s .modulus)).eval S+S.scalar .modulus≤M
        rw [hsp]; omega
      have secondSafe : (.branch (descriptor .second) (wedgeExpr .u1 .v1) (c 0) : X).Safe M S := by
        refine ⟨hdSafe _ (by simp),?_⟩
        split_ifs
        · exact Nat.zero_le _
        · exact wedgeSafe _ _ (by simp) (by simp)
      have wedgeLt (a b : Arr) : (wedgeExpr a b).eval S<p := by
        change _%S.scalar .modulus<p
        rw [hsp]; exact Nat.mod_lt _ hp
      apply safe_mod _ (hscalar _) (by simpa [s,Expr.eval,hsp] using hp) (by simp [s,Expr.eval,hsp]; omega)
      apply safe_add (wedgeSafe _ _ (by simp) (by simp)) secondSafe
      change (wedgeExpr .u0 .v0).eval S+(if (descriptor .second).eval S=0 then 0 else (wedgeExpr .u1 .v1).eval S)≤M
      split_ifs <;> nlinarith [wedgeLt .u0 .v0,wedgeLt .u1 .v1]
    · simp only [lt,s,Expr.eval,Op.eval,BinaryOp.eval,hsn,if_neg hcn,if_true,c,Expr.Safe]
      exact Nat.zero_le _
  · simp only [lt,s,Expr.eval,Op.eval,BinaryOp.eval,hso,if_neg hzo,if_true,c,Expr.Safe]
    exact Nat.zero_le _

theorem program_runs (D : Descriptors) (E H : List ℕ) (p n oldOut k ni no f M : ℕ)
    (hp : 0<p) (hM : 1≤M) (hpM : p*p+2*p≤M) (hnino : ni*no≤M)
    (hE : E.length=f*n) (hH : H.length=f*k) (ev : ∀x∈E,x<p) (hv : ∀x∈H,x<p)
    (valid : D.Valid oldOut f) (S : State) (bounded : S.Bounded M)
    (ready : Ready D E H p n oldOut k ni no (inputs S)) (length : S.scalar (.inl .total)=k*ni*no) :
    ∃t≤(k*ni*no)*(expression.cost+4)+6,∃U,Runs (storageBound (Registers Reg expression.need) Arr M)
      program S t U ∧ U.Bounded M ∧ Ready D E H p n oldOut k ni no (inputs U) ∧
      U.array .result=List.ofFn (fun i : Fin (k*ni*no)=>entry D E H p n oldOut k ni no i.val) := by
  apply tableProgram_runs expression registers .result (Ready D E H p n oldOut k ni no)
    (entry D E H p n oldOut k ni no) M (k*ni*no) hM
  · intro V hV i v
    fin_cases i <;> simpa [Ready,registers,Store.setScalar] using hV
  · intro V hV xs
    simpa [Ready,Store.setArray] using hV
  · intro V hV hB hi
    exact expression_safe D E H p n oldOut k ni no f M hp hM hpM hnino hE hH ev hv valid V hB hV hi
  · intro V hV hi
    exact expression_eval D E H p n oldOut k ni no V hV
  · exact bounded
  · exact ready
  · exact length

end GroupWL.MachinePrograms.WedgeConstraints
