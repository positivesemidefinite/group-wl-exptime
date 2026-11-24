import GroupWL.MachinePrograms.NatArrayEncoding
import GroupWL.MachinePrograms.UnaryArithmetic
import GroupWL.MachinePrograms.UnaryComparisons
import GroupWL.MachinePrograms.UnaryDivision
import GroupWL.MachinePrograms.UnarySubtraction

/-! Concrete scalar atoms of the finite-register array language. -/
namespace GroupWL.MachinePrograms.NatArrayLowering

open NatArrayLanguage

variable {Reg Arr : Type*} [DecidableEq Reg] [DecidableEq Arr]
  [Fintype Reg] [Fintype Arr]

def workEmbedding (n : ℕ) (hn : n ≤ 16) : Fin n ↪ StackIndex Reg Arr where
  toFun i := scratchSlot ⟨i.val, lt_of_lt_of_le i.isLt hn⟩
  inj' := by
    intro i j h
    apply Fin.ext
    simpa only [scratchSlot, Sum.inr.injEq, Fin.mk.injEq] using h

theorem copyOperand_runs (S : Store Reg Arr) (T : Structured.Store (StackIndex Reg Arr))
    (hT : DataEncoded S T) (r : Reg) (i j : Fin 16) (hij : i ≠ j)
    (hi : T (scratchSlot i) = []) (hj : T (scratchSlot j) = []) :
    Structured.Runs (Structured.copy (scalarSlot r) (scratchSlot i) (scratchSlot j)) T
      (7*S.scalar r+2) (Function.update T (scratchSlot i) (Structured.unary (S.scalar r))) := by
  have h := Structured.copy_runs T (scalarSlot r) (scratchSlot i) (scratchSlot j)
    (by simp) (by simp) (by simpa using hij) hj
  simpa [hT.1 r, hi, Structured.unary] using h

def flushScalar (i j : Fin 16) (r : Reg) : Structured.Program (StackIndex Reg Arr) :=
  .seq (Structured.clear (scalarSlot r))
    (Structured.copy (scratchSlot i) (scalarSlot r) (scratchSlot j))

theorem flushScalar_runs (S : Store Reg Arr) (T : Structured.Store (StackIndex Reg Arr))
    (hT : DataEncoded S T) (r : Reg) (i j : Fin 16) (hij : i ≠ j) (n : ℕ)
    (hi : T (scratchSlot i) = Structured.unary n) (hj : T (scratchSlot j) = []) :
    Structured.Runs (flushScalar i j r) T (2*S.scalar r+7*n+3)
      (Function.update T (scalarSlot r) (Structured.unary n)) := by
  let U := Function.update T (scalarSlot r) []
  have first : Structured.Runs (Structured.clear (scalarSlot r)) T (2*S.scalar r+1) U := by
    simpa [U, hT.1 r] using Structured.clear_runs T (scalarSlot r)
  have last : Structured.Runs
      (Structured.copy (scratchSlot i) (scalarSlot r) (scratchSlot j)) U (7*n+2)
      (Function.update T (scalarSlot r) (Structured.unary n)) := by
    have h := Structured.copy_runs U (scratchSlot i) (scalarSlot r) (scratchSlot j)
      (by simp) (by simpa using hij) (by simp)
      (by simpa [U] using hj)
    simpa [U, hi, Function.update_idem] using h
  convert Structured.Runs.seq first last using 1 <;> omega

def constBody (r : Reg) (n : ℕ) : BodyCode (Arr := Arr) (.const r n) where
  body := .seq (Structured.clear (scalarSlot r)) (Structured.pushUnary (scalarSlot r) n)
  correct S B hv hb ha := by
    let U := Function.update (encodeStore S) (scalarSlot r) []
    have first : Structured.Runs (Structured.clear (scalarSlot r)) (encodeStore S)
        (2*S.scalar r+1) U := by
      simpa [U] using Structured.clear_runs (encodeStore S) (scalarSlot r)
    have last : Structured.Runs (Structured.pushUnary (scalarSlot r) n) U n
        (Function.update (encodeStore S) (scalarSlot r) (Structured.unary n)) := by
      simpa [U, Function.update_idem] using Structured.pushUnary_runs (scalarSlot r) n U
    have hm := (Store.scalar_le_size S r).trans hb
    have hn : n ≤ B := by
      simpa [Atom.apply, Store.setScalar] using (Store.scalar_le_size ((Atom.const r n).apply S) r).trans ha
    have hp : B+1 ≤ (B+1)^3 := le_self_pow (by omega) (by decide)
    refine ⟨2*S.scalar r+1+n, by nlinarith, _, Structured.Runs.seq first last, ?_⟩
    exact (dataEncoded_encodeStore S).update_scalar r n

def copyBody (r s : Reg) : BodyCode (Arr := Arr) (.copy r s) where
  body := if r = s then .skip else .seq (Structured.clear (scalarSlot r))
    (Structured.copy (scalarSlot s) (scalarSlot r) (scratchSlot 15))
  correct S B hv hb ha := by
    by_cases hrs : r = s
    · subst s
      refine ⟨0, by omega, encodeStore S, ?_, ?_⟩
      · simp only [if_pos rfl]
        exact Structured.Runs.skip _
      · simpa [Atom.apply, Store.setScalar, Function.update_eq_self] using dataEncoded_encodeStore S
    · simp only [if_neg hrs]
      let U := Function.update (encodeStore S) (scalarSlot r) []
      have first : Structured.Runs (Structured.clear (scalarSlot r)) (encodeStore S)
          (2*S.scalar r+1) U := by
        simpa [U] using Structured.clear_runs (encodeStore S) (scalarSlot r)
      have last : Structured.Runs
          (Structured.copy (scalarSlot s) (scalarSlot r) (scratchSlot 15)) U (7*S.scalar s+2)
          (Function.update (encodeStore S) (scalarSlot r) (Structured.unary (S.scalar s))) := by
        have h := Structured.copy_runs U (scalarSlot s) (scalarSlot r) (scratchSlot 15)
          (by simpa using Ne.symm hrs) (by simp) (by simp) (by simp [U])
        simpa [U, Ne.symm hrs, Structured.unary, Function.update_idem] using h
      have hr := (Store.scalar_le_size S r).trans hb
      have hs := (Store.scalar_le_size S s).trans hb
      have hp : B+1 ≤ (B+1)^3 := le_self_pow (by omega) (by decide)
      refine ⟨(2*S.scalar r+1)+(7*S.scalar s+2), by nlinarith, _, Structured.Runs.seq first last, ?_⟩
      exact (dataEncoded_encodeStore S).update_scalar r (S.scalar s)

def boolToUnary (k : StackIndex Reg Arr) : Structured.Program (StackIndex Reg Arr) :=
  .pop k .skip .skip (.push k true)

theorem boolToUnary_runs (T : Structured.Store (StackIndex Reg Arr)) (k : StackIndex Reg Arr)
    (b : Bool) (hk : T k = [b]) :
    Structured.Runs (boolToUnary k) T (1 + if b then 1 else 0)
      (Function.update T k (Structured.unary (if b then 1 else 0))) := by
  cases b with
  | false =>
    apply Structured.Runs.pop
    simpa [Structured.select, hk, Structured.unary] using
      Structured.Runs.skip (Function.update T k [])
  | true =>
    apply Structured.Runs.pop
    simpa [Structured.select, hk, Structured.unary, Function.update_idem] using
      Structured.Runs.push (Function.update T k []) k true

def comparisonWork (mode : Structured.UnaryComparison) : Structured.Program (StackIndex Reg Arr) :=
  .seq (Structured.compareUnary mode (workEmbedding 6 (by decide))) (boolToUnary (scratchSlot 2))

theorem comparisonWork_runs (mode : Structured.UnaryComparison)
    (T : Structured.Store (StackIndex Reg Arr)) (m n : ℕ)
    (hm : T (scratchSlot 0) = Structured.unary m) (hn : T (scratchSlot 1) = Structured.unary n)
    (he : ∀ i : Fin 16, 2 ≤ i.val → T (scratchSlot i) = []) :
    ∃ t ≤ 16*(m+n+1)+2,
      Structured.Runs (comparisonWork mode) T t
        (Function.update T (scratchSlot 2) (Structured.unary (if mode.result m n then 1 else 0))) := by
  obtain ⟨t, ht, hr⟩ := Structured.compareUnary_runs mode (workEmbedding (Reg := Reg) (Arr := Arr) 6 (by decide))
    m n T hm hn (he 2 (by decide)) (he 3 (by decide)) (he 4 (by decide)) (he 5 (by decide))
  let U := Function.update T (scratchSlot 2) [mode.result m n]
  have hb := boolToUnary_runs U (scratchSlot 2) (mode.result m n) (by simp [U])
  have run := Structured.Runs.seq hr hb
  refine ⟨t+(1+if mode.result m n then 1 else 0), ?_, ?_⟩
  · split <;> omega
  · simpa [comparisonWork, U, Function.update_idem] using run

def binaryWork : BinaryOp → Structured.Program (StackIndex Reg Arr)
  | .add => .seq (Structured.copy (scratchSlot 0) (scratchSlot 2) (scratchSlot 15))
      (Structured.copy (scratchSlot 1) (scratchSlot 2) (scratchSlot 15))
  | .sub => .seq (Structured.copy (scratchSlot 0) (scratchSlot 2) (scratchSlot 15))
      (Structured.subtractCopy (scratchSlot 1) (scratchSlot 2) (scratchSlot 3) (scratchSlot 15))
  | .mul => Structured.multiply (scratchSlot 0) (scratchSlot 1) (scratchSlot 2)
      (scratchSlot 3) (scratchSlot 15)
  | .eq => comparisonWork .eq
  | .lt => comparisonWork .lt
  | .le => comparisonWork .le

theorem binaryWork_runs (op : BinaryOp) (T : Structured.Store (StackIndex Reg Arr)) (m n : ℕ)
    (hm : T (scratchSlot 0) = Structured.unary m) (hn : T (scratchSlot 1) = Structured.unary n)
    (he : ∀ i : Fin 16, 2 ≤ i.val → T (scratchSlot i) = []) :
    ∃ t ≤ 40*(m+1)*(n+1), Structured.Runs (binaryWork op) T t
      (Function.update T (scratchSlot 2) (Structured.unary (op.eval m n))) := by
  have copy0 : Structured.Runs
      (Structured.copy (scratchSlot 0) (scratchSlot 2) (scratchSlot 15)) T (7*m+2)
      (Function.update T (scratchSlot 2) (Structured.unary m)) := by
    simpa [hm, he 2 (by decide)] using
      Structured.copy_runs T (scratchSlot 0) (scratchSlot 2) (scratchSlot 15)
        (by simp) (by simp) (by simp) (he 15 (by decide))
  let U := Function.update T (scratchSlot 2) (Structured.unary m)
  have h1 : U (scratchSlot 1) = Structured.unary n := by simp [U, hn]
  have h2 : U (scratchSlot 2) = Structured.unary m := by simp [U]
  have h3 : U (scratchSlot 3) = [] := by simp [U, he 3 (by decide)]
  have h15 : U (scratchSlot 15) = [] := by simp [U, he 15 (by decide)]
  cases op with
  | add =>
    have last := Structured.addCopy_runs U (scratchSlot 1) (scratchSlot 2) (scratchSlot 15)
      (by simp) (by simp) (by simp) n m h1 h2 h15
    refine ⟨(7*m+2)+(7*n+2), by nlinarith, ?_⟩
    simpa [binaryWork, BinaryOp.eval, U, Function.update_idem, Nat.add_comm] using
      Structured.Runs.seq copy0 last
  | sub =>
    have last := Structured.subtractCopy_runs U (scratchSlot 1) (scratchSlot 2)
      (scratchSlot 3) (scratchSlot 15) (by simp) (by simp) (by simp) (by simp)
      n m h1 h2 h3 h15
    refine ⟨(7*m+2)+(10*n+3), by nlinarith, ?_⟩
    simpa [binaryWork, BinaryOp.eval, U, Function.update_idem] using Structured.Runs.seq copy0 last
  | mul =>
    have run := Structured.multiply_runs T (scratchSlot 0) (scratchSlot 1) (scratchSlot 2)
      (scratchSlot 3) (scratchSlot 15) (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp) m n hm hn (he 3 (by decide)) (he 15 (by decide))
    exact ⟨7*m*n+11*m+3, by nlinarith, by simpa [binaryWork, BinaryOp.eval, he 2 (by decide)] using run⟩
  | eq =>
    obtain ⟨t, ht, hr⟩ := comparisonWork_runs .eq T m n hm hn he
    refine ⟨t, ht.trans (by nlinarith), ?_⟩
    simpa [binaryWork, BinaryOp.eval, Structured.UnaryComparison.result] using hr
  | lt =>
    obtain ⟨t, ht, hr⟩ := comparisonWork_runs .lt T m n hm hn he
    refine ⟨t, ht.trans (by nlinarith), ?_⟩
    simpa [binaryWork, BinaryOp.eval, Structured.UnaryComparison.result] using hr
  | le =>
    obtain ⟨t, ht, hr⟩ := comparisonWork_runs .le T m n hm hn he
    refine ⟨t, ht.trans (by nlinarith), ?_⟩
    simpa [binaryWork, BinaryOp.eval, Structured.UnaryComparison.result] using hr

def operandStore (S : Store Reg Arr) (m n : ℕ) : Structured.Store (StackIndex Reg Arr) :=
  Function.update (Function.update (encodeStore S) (scratchSlot 0) (Structured.unary m))
    (scratchSlot 1) (Structured.unary n)

theorem operandStore_data (S : Store Reg Arr) (m n : ℕ) : DataEncoded S (operandStore S m n) :=
  ((dataEncoded_encodeStore S).update_scratch 0 _).update_scratch 1 _

@[simp] theorem operandStore_zero (S : Store Reg Arr) (m n : ℕ) :
    operandStore S m n (scratchSlot 0) = Structured.unary m := by simp [operandStore]

@[simp] theorem operandStore_one (S : Store Reg Arr) (m n : ℕ) :
    operandStore S m n (scratchSlot 1) = Structured.unary n := by simp [operandStore]

theorem operandStore_empty (S : Store Reg Arr) (m n : ℕ) (i : Fin 16) (hi : 2 ≤ i.val) :
    operandStore S m n (scratchSlot i) = [] := by
  have h0 : i ≠ 0 := by intro h; subst i; contradiction
  have h1 : i ≠ 1 := by intro h; subst i; contradiction
  simp [operandStore, h0, h1]

def loadOperands (left right : Reg) : Structured.Program (StackIndex Reg Arr) :=
  .seq (Structured.copy (scalarSlot left) (scratchSlot 0) (scratchSlot 15))
    (Structured.copy (scalarSlot right) (scratchSlot 1) (scratchSlot 15))

theorem loadOperands_runs (S : Store Reg Arr) (left right : Reg) :
    Structured.Runs (loadOperands left right) (encodeStore S)
      ((7*S.scalar left+2)+(7*S.scalar right+2)) (operandStore S (S.scalar left) (S.scalar right)) := by
  let U := Function.update (encodeStore S) (scratchSlot 0) (Structured.unary (S.scalar left))
  have first := copyOperand_runs S (encodeStore S) (dataEncoded_encodeStore S) left 0 15
    (by decide) (by simp) (by simp)
  have last := copyOperand_runs S U ((dataEncoded_encodeStore S).update_scratch 0 _)
    right 1 15 (by decide) (by simp [U]) (by simp [U])
  exact Structured.Runs.seq first last

def binaryBody (op : BinaryOp) (destination left right : Reg) :
    BodyCode (Arr := Arr) (.binary op destination left right) where
  body := .seq (loadOperands left right)
    (.seq (binaryWork op) (flushScalar 2 15 destination))
  correct S B hv hb ha := by
    let m := S.scalar left
    let n := S.scalar right
    let v := op.eval m n
    let U := operandStore S m n
    have first := loadOperands_runs S left right
    obtain ⟨t, ht, middle⟩ := binaryWork_runs op U m n (by simp [U]) (by simp [U])
      (operandStore_empty S m n)
    let W := Function.update U (scratchSlot 2) (Structured.unary v)
    have hW : DataEncoded S W := (operandStore_data S m n).update_scratch 2 _
    have last := flushScalar_runs S W hW destination 2 15 (by decide) v
      (by simp [W]) (by simp [W, U, operandStore_empty S m n 15 (by decide)])
    have hm : m ≤ B := (Store.scalar_le_size S left).trans hb
    have hn : n ≤ B := (Store.scalar_le_size S right).trans hb
    have hv' : v ≤ B := by
      simpa [v, m, n, Atom.apply, Store.setScalar] using
        (Store.scalar_le_size ((Atom.binary op destination left right).apply S) destination).trans ha
    have hd := (Store.scalar_le_size S destination).trans hb
    have hp : B+1 ≤ (B+1)^3 := le_self_pow (by omega) (by decide)
    have hp2 : (B+1)^2 ≤ (B+1)^3 := by nlinarith [Nat.mul_le_mul_left ((B+1)^2) (show 1 ≤ B+1 by omega)]
    have ht' : t ≤ 40*(B+1)^2 := by nlinarith
    refine ⟨((7*m+2)+(7*n+2))+(t+(2*S.scalar destination+7*v+3)), by nlinarith,
      _, Structured.Runs.seq first (Structured.Runs.seq middle last), ?_⟩
    exact hW.update_scalar destination v

def divmodBody (quotient remainder dividend divisor : Reg) :
    BodyCode (Arr := Arr) (.divmod quotient remainder dividend divisor) where
  body := .seq (loadOperands dividend divisor)
    (.seq (Structured.divideUnary (workEmbedding 7 (by decide)))
      (.seq (flushScalar 2 15 quotient) (flushScalar 3 15 remainder)))
  correct S B hv hb ha := by
    obtain ⟨hqr, hpos⟩ := hv
    let m := S.scalar dividend
    let b := S.scalar divisor
    let U := operandStore S m b
    let reg := workEmbedding (Reg := Reg) (Arr := Arr) 7 (by decide)
    have first := loadOperands_runs S dividend divisor
    have he : ∀ i : Fin 7, 2 ≤ i.val → U (reg i) = [] := by
      intro i hi
      exact operandStore_empty S m b ⟨i.val, by omega⟩ hi
    obtain ⟨t, ht, middle⟩ := Structured.divideUnary_runs U reg m b hpos
      (by simp [U, reg, workEmbedding]) (by simp [U, reg, workEmbedding]) he
    let W := Function.update (Function.update U (scratchSlot 2) (Structured.unary (m/b)))
      (scratchSlot 3) (Structured.unary (m%b))
    have hW : DataEncoded S W := ((operandStore_data S m b).update_scratch 2 _).update_scratch 3 _
    have hW15 : W (scratchSlot 15) = [] := by
      simp [W, U, operandStore_empty S m b 15 (by decide)]
    have writeQ := flushScalar_runs S W hW quotient 2 15 (by decide) (m/b)
      (by simp [W]) hW15
    let Q := Function.update W (scalarSlot quotient) (Structured.unary (m/b))
    let S₁ := S.setScalar quotient (m/b)
    have hQ : DataEncoded S₁ Q := hW.update_scalar quotient (m/b)
    have writeR := flushScalar_runs S₁ Q hQ remainder 3 15 (by decide) (m%b)
      (by simp [Q, W]) (by simpa [Q] using hW15)
    have hr : S₁.scalar remainder = S.scalar remainder := by
      simp [S₁, Store.setScalar, Ne.symm hqr]
    rw [hr] at writeR
    have hm : m ≤ B := (Store.scalar_le_size S dividend).trans hb
    have hb' : b ≤ B := (Store.scalar_le_size S divisor).trans hb
    have hq := (Store.scalar_le_size S quotient).trans hb
    have hr' := (Store.scalar_le_size S remainder).trans hb
    have hquot : m/b ≤ B := (Nat.div_le_self m b).trans hm
    have hrem : m%b ≤ B := (Nat.mod_le m b).trans hm
    have hp : B+1 ≤ (B+1)^3 := le_self_pow (by omega) (by decide)
    have hp2 : (B+1)^2 ≤ (B+1)^3 := by nlinarith [Nat.mul_le_mul_left ((B+1)^2) (show 1 ≤ B+1 by omega)]
    have ht' : t ≤ 20*(B+1)^2 := by nlinarith
    refine ⟨((7*m+2)+(7*b+2))+
      (t+((2*S.scalar quotient+7*(m/b)+3)+(2*S.scalar remainder+7*(m%b)+3))),
      by nlinarith, Function.update Q (scalarSlot remainder) (Structured.unary (m%b)), ?_, ?_⟩
    · exact Structured.Runs.seq first
        (Structured.Runs.seq middle (Structured.Runs.seq writeQ writeR))
    · exact hQ.update_scalar remainder (m%b)

end GroupWL.MachinePrograms.NatArrayLowering
