import GroupWL.MachinePrograms.NatArrayProofs
import GroupWL.MachinePrograms.NatArrayCountedLoops
import GroupWL.MachinePrograms.NatArrayFrames
import GroupWL.MachinePrograms.ArrayTabulation

/-! Materialized modular matrix arithmetic in the finite-register language. -/
namespace GroupWL.MachinePrograms.MatrixArithmetic

open NatArrayLanguage
open scoped BigOperators
set_option maxHeartbeats 1000000

inductive Reg where
  | rows | inner | cols | modulus | one | zero
  | row | col | position | todo | total
  | k | remaining | indexA | indexB | left | right | product | sum | temp | quotient
  deriving DecidableEq, Fintype

inductive Arr where
  | left | right | output
  deriving DecidableEq, Fintype

abbrev Code := Program Reg Arr
abbrev State := Store Reg Arr

def dotStepAtoms : List (Atom Reg Arr) := [
  .binary .mul .indexA .row .inner,
  .binary .add .indexA .indexA .k,
  .read .left .left .indexA,
  .binary .mul .indexB .k .cols,
  .binary .add .indexB .indexB .col,
  .read .right .right .indexB,
  .binary .mul .product .left .right,
  .binary .add .temp .sum .product,
  .divmod .quotient .sum .temp .modulus]

def dotStep : Code := atoms dotStepAtoms

def dotProduct : Code := sequence [
  .atom (.const .sum 0),
  countedLoop .k .remaining .inner .one dotStep]

def multiplyCell : Code := sequence [
  .atom (.divmod .row .col .position .cols),
  dotProduct,
  .atom (.write .output .position .sum)]

def multiply : Code := .seq (atoms [
  .const .one 1, .const .zero 0,
  .binary .mul .total .rows .cols,
  .allocate .output .total .zero])
  (countedLoop .position .todo .total .one multiplyCell)

def read (xs : List ℕ) (i : ℕ) : ℕ := xs[i]?.getD 0

def partialDot (A B : List ℕ) (inner cols row col p k : ℕ) : ℕ :=
  (∑ j ∈ Finset.range k, read A (row*inner+j)*read B (j*cols+col))%p

@[simp] theorem partialDot_zero (A B : List ℕ) (inner cols row col p : ℕ) :
    partialDot A B inner cols row col p 0 = 0 := by simp [partialDot]

theorem partialDot_succ (A B : List ℕ) (inner cols row col p k : ℕ) :
    partialDot A B inner cols row col p (k+1) =
      (partialDot A B inner cols row col p k + read A (row*inner+k)*read B (k*cols+col))%p := by
  simp only [partialDot, Finset.sum_range_succ]
  exact (Nat.mod_add_mod _ _ _).symm

theorem read_lt {xs : List ℕ} {p : ℕ} (h : ∀ x∈xs, x<p) (hp : 0<p) (i : ℕ) :
    read xs i < p := by
  unfold read
  cases hx : xs[i]? with
  | none => simpa using hp
  | some x => exact h x (List.mem_of_getElem? hx)

theorem dotStep_runs (S : State) (M : ℕ) (bounded : S.Bounded M)
    (positive : 0 < S.scalar .modulus)
    (small : S.scalar .modulus*S.scalar .modulus+S.scalar .modulus ≤ M)
    (leftIndex : S.scalar .row*S.scalar .inner+S.scalar .k < (S.array .left).length)
    (rightIndex : S.scalar .k*S.scalar .cols+S.scalar .col < (S.array .right).length)
    (leftSmall : ∀ x∈S.array .left, x<S.scalar .modulus)
    (rightSmall : ∀ x∈S.array .right, x<S.scalar .modulus)
    (sumSmall : S.scalar .sum < S.scalar .modulus) :
    Runs (storageBound Reg Arr M) dotStep S 9 (applyAtoms dotStepAtoms S) ∧
      (applyAtoms dotStepAtoms S).Bounded M ∧
      (applyAtoms dotStepAtoms S).scalar .sum =
        (S.scalar .sum + read (S.array .left) (S.scalar .row*S.scalar .inner+S.scalar .k)*
          read (S.array .right) (S.scalar .k*S.scalar .cols+S.scalar .col))%S.scalar .modulus := by
  have hA := bounded.2.1 Arr.left
  have hB := bounded.2.1 Arr.right
  have hleft := read_lt leftSmall positive (S.scalar .row*S.scalar .inner+S.scalar .k)
  have hright := read_lt rightSmall positive (S.scalar .k*S.scalar .cols+S.scalar .col)
  have hprod : read (S.array .left) (S.scalar .row*S.scalar .inner+S.scalar .k)*
      read (S.array .right) (S.scalar .k*S.scalar .cols+S.scalar .col) ≤
      S.scalar .modulus*S.scalar .modulus := by nlinarith
  have hvalid : ValidAtoms M dotStepAtoms S := by
    simp [dotStepAtoms, ValidAtoms, Atom.Valid, Atom.SmallResult, Atom.apply,
      BinaryOp.eval, Store.setScalar, Function.update_apply]
    simp only [read] at hprod
    exact ⟨by nlinarith, by nlinarith, leftIndex, by nlinarith, by nlinarith,
      rightIndex, by nlinarith, by nlinarith, positive⟩
  obtain ⟨run,hb⟩ := atoms_runs bounded dotStepAtoms hvalid
  refine ⟨run, hb, ?_⟩
  simp [applyAtoms, dotStepAtoms, Atom.apply, BinaryOp.eval, Store.setScalar, read]

def dotInputs : Finset Reg := {.row, .col, .inner, .cols, .modulus, .one}

structure DotState (S : State) (M i : ℕ) (T : State) : Prop where
  bounded : T.Bounded M
  inputs : ∀ r∈dotInputs, T.scalar r = S.scalar r
  arrays : ∀ a, T.array a = S.array a
  index : T.scalar .k = i
  remaining : T.scalar .remaining = S.scalar .inner-i
  accumulator : T.scalar .sum = partialDot (S.array .left) (S.array .right)
    (S.scalar .inner) (S.scalar .cols) (S.scalar .row) (S.scalar .col) (S.scalar .modulus) i

theorem dotProduct_runs (S : State) (M : ℕ) (bounded : S.Bounded M)
    (one : S.scalar .one = 1) (positive : 0 < S.scalar .modulus)
    (small : S.scalar .modulus*S.scalar .modulus+S.scalar .modulus ≤ M)
    (leftIndex : ∀ i < S.scalar .inner,
      S.scalar .row*S.scalar .inner+i < (S.array .left).length)
    (rightIndex : ∀ i < S.scalar .inner,
      i*S.scalar .cols+S.scalar .col < (S.array .right).length)
    (leftSmall : ∀ x∈S.array .left, x<S.scalar .modulus)
    (rightSmall : ∀ x∈S.array .right, x<S.scalar .modulus) :
    ∃ t ≤ 12*S.scalar .inner+4, ∃ T,
      Runs (storageBound Reg Arr M) dotProduct S t T ∧
      T.Bounded M ∧ T.scalar .sum = partialDot (S.array .left) (S.array .right)
        (S.scalar .inner) (S.scalar .cols) (S.scalar .row) (S.scalar .col)
        (S.scalar .modulus) (S.scalar .inner) := by
  let S₀ := S.setScalar .sum 0
  let S₁ := S₀.setScalar .remaining (S.scalar .inner)
  let S₂ := S₁.setScalar .k 0
  have h₀ : S₀.Bounded M := bounded.setScalar _ (by omega)
  have h₁ : S₁.Bounded M := h₀.setScalar _ (bounded.1 .inner)
  have h₂ : S₂.Bounded M := h₁.setScalar _ (by omega)
  have hstart : DotState S M 0 S₂ := by
    refine ⟨h₂, ?_, ?_, ?_, ?_, ?_⟩
    · intro r hr
      have hdis : ∀ r∈dotInputs, r≠Reg.k ∧ r≠Reg.remaining ∧ r≠Reg.sum := by decide
      obtain ⟨hkr,hrr,hsr⟩ := hdis r hr
      simp [S₂,S₁,S₀,Store.setScalar,hkr,hrr,hsr]
    · intro a; rfl
    · simp [S₂]
    · simp [S₂, S₁]
    · simp [S₂, S₁, S₀]
  have hcontrol : ∀ i ≤ S.scalar .inner, ∀ T, DotState S M i T →
      T.scalar .k = i ∧ T.scalar .remaining = S.scalar .inner-i ∧
      T.scalar .one = 1 ∧ T.size ≤ storageBound Reg Arr M := by
    intro i hi T hT
    exact ⟨hT.index, hT.remaining,
      (hT.inputs .one (by decide)).trans one, Store.size_le_of_bounded hT.bounded⟩
  have hstep : ∀ i < S.scalar .inner, ∀ T, DotState S M i T →
      ∃ t ≤ 9, ∃ U, Runs (storageBound Reg Arr M) dotStep T t U ∧
        U.scalar .k = i ∧ U.scalar .remaining = S.scalar .inner-i ∧ U.scalar .one = 1 ∧
        (U.setScalar .k (i+1)).size ≤ storageBound Reg Arr M ∧
        DotState S M (i+1) (advance .k .remaining U) := by
    intro i hi T hT
    have hrow := hT.inputs .row (by decide)
    have hcol := hT.inputs .col (by decide)
    have hinner := hT.inputs .inner (by decide)
    have hcols := hT.inputs .cols (by decide)
    have hp := hT.inputs .modulus (by decide)
    have ha := hT.arrays Arr.left
    have hb := hT.arrays Arr.right
    obtain ⟨run, bound, acc⟩ := dotStep_runs T M hT.bounded (by omega)
      (by rwa [hp]) (by simpa only [hrow,hinner,hT.index,ha] using leftIndex i hi)
      (by simpa only [hcols,hcol,hT.index,hb] using rightIndex i hi)
      (by simpa only [ha,hp] using leftSmall)
      (by simpa only [hb,hp] using rightSmall)
      (by rw [hT.accumulator,hp]; exact Nat.mod_lt _ positive)
    let U := applyAtoms dotStepAtoms T
    have hframe (r : Reg) (hr : r∈dotInputs ∨ r=.k ∨ r=.remaining) : U.scalar r = T.scalar r := by
      apply run.scalar_eq_of_not_mem
      have hdis : ∀ r∈dotInputs, r∉dotStep.scalarWrites := by decide
      rcases hr with hr | hr | hr
      · exact hdis r hr
      · subst r; decide
      · subst r; decide
    have hiM : i+1 ≤ M := le_trans (by omega) (bounded.1 .inner)
    have hmid : (U.setScalar .k (i+1)).Bounded M := bound.setScalar _ hiM
    have hk : U.scalar .k = i := (hframe .k (by simp)).trans hT.index
    have hrem : U.scalar .remaining = S.scalar .inner-i :=
      (hframe .remaining (by simp)).trans hT.remaining
    have hone : U.scalar .one = 1 :=
      (hframe .one (by decide)).trans ((hT.inputs .one (by decide)).trans one)
    have hfinal : (advance .k .remaining U).Bounded M := by
      simpa only [advance,hk] using hmid.setScalar Reg.remaining
        (Nat.sub_le (U.scalar .remaining) 1 |>.trans (bound.1 .remaining))
    refine ⟨9, le_rfl, U, run, hk, hrem, hone, Store.size_le_of_bounded hmid,
      hfinal, ?_, ?_, ?_, ?_, ?_⟩
    · intro r hr
      have he := (hframe r (Or.inl hr)).trans (hT.inputs r hr)
      have hd : ∀ r∈dotInputs, r≠Reg.k ∧ r≠Reg.remaining := by decide
      have hrk := (hd r hr).1
      have hrr := (hd r hr).2
      simpa [advance,Store.setScalar,hrk,hrr] using he
    · intro a
      exact (run.array_eq_of_not_mem a (by
        simp [dotStep,atoms,dotStepAtoms,NatArrayLanguage.sequence,Program.arrayWrites,Atom.arrayWrites])).trans
          (hT.arrays a)
    · simp [advance,hk,Store.setScalar]
    · simp [advance,hrem,Store.setScalar,Nat.sub_sub]
    · change U.scalar .sum = _
      rw [acc, hT.accumulator, hrow, hinner, hT.index, hcols, hcol, ha, hb, hp]
      exact (partialDot_succ _ _ _ _ _ _ _ _).symm
  obtain ⟨t, ht, T, run, hT⟩ := countedLoop_runs (storageBound Reg Arr M)
    Reg.k Reg.remaining Reg.inner Reg.one dotStep (S.scalar .inner) 9 (DotState S M) S₀
    (Store.size_le_of_bounded h₀) (Store.size_le_of_bounded h₁) hstart hcontrol
    (by decide) (by decide) hstep
  refine ⟨1+(t+0), by omega, T, ?_, hT.bounded, hT.accumulator⟩
  exact .seq (.atom trivial (Store.size_le_of_bounded bounded) (Store.size_le_of_bounded h₀))
    (.seq run (.skip run.end_bound))

def matrixEntry (S : State) (i : ℕ) : ℕ :=
  partialDot (S.array .left) (S.array .right) (S.scalar .inner) (S.scalar .cols)
    (i/S.scalar .cols) (i%S.scalar .cols) (S.scalar .modulus) (S.scalar .inner)

theorem multiplyCell_runs (S : State) (M : ℕ) (bounded : S.Bounded M)
    (one : S.scalar .one = 1) (positive : 0 < S.scalar .modulus)
    (small : S.scalar .modulus*S.scalar .modulus+S.scalar .modulus ≤ M)
    (leftLength : (S.array .left).length = S.scalar .rows*S.scalar .inner)
    (rightLength : (S.array .right).length = S.scalar .inner*S.scalar .cols)
    (outputLength : (S.array .output).length = S.scalar .rows*S.scalar .cols)
    (position : S.scalar .position < S.scalar .rows*S.scalar .cols)
    (leftSmall : ∀ x∈S.array .left, x<S.scalar .modulus)
    (rightSmall : ∀ x∈S.array .right, x<S.scalar .modulus) :
    ∃ t ≤ 12*S.scalar .inner+6, ∃ T,
      Runs (storageBound Reg Arr M) multiplyCell S t T ∧ T.Bounded M ∧
      T.array .output = (S.array .output).set (S.scalar .position) (matrixEntry S (S.scalar .position)) := by
  have hcols : 0 < S.scalar .cols := by nlinarith
  have hrow : S.scalar .position/S.scalar .cols < S.scalar .rows :=
    (Nat.div_lt_iff_lt_mul hcols).2 (by simpa [Nat.mul_comm] using position)
  have hcol : S.scalar .position%S.scalar .cols < S.scalar .cols := Nat.mod_lt _ hcols
  let a : Atom Reg Arr := .divmod .row .col .position .cols
  let S₀ := a.apply S
  have h₀ : S₀.Bounded M := a.apply_bounded bounded trivial
  have ra := atom_runs bounded a (show a.Valid S from ⟨by decide,hcols⟩) trivial
  have leftIndex : ∀ i < S₀.scalar .inner,
      S₀.scalar .row*S₀.scalar .inner+i < (S₀.array .left).length := by
    intro i hi
    simp only [S₀,a,Atom.apply,Store.setScalar,Function.update_apply] at hi ⊢
    simp only [reduceCtorEq,ite_false,ite_true] at hi ⊢
    rw [leftLength]
    have h := Nat.mul_le_mul_right (S.scalar .inner) (Nat.succ_le_of_lt hrow)
    nlinarith
  have rightIndex : ∀ i < S₀.scalar .inner,
      i*S₀.scalar .cols+S₀.scalar .col < (S₀.array .right).length := by
    intro i hi
    simp only [S₀,a,Atom.apply,Store.setScalar,Function.update_apply] at hi ⊢
    simp only [reduceCtorEq,ite_false,ite_true] at hi ⊢
    rw [rightLength]
    have h := Nat.mul_le_mul_right (S.scalar .cols) (Nat.succ_le_of_lt hi)
    nlinarith
  obtain ⟨t,ht,U,run,hU,hacc⟩ := dotProduct_runs S₀ M h₀
    (by simpa [S₀,a,Atom.apply,Store.setScalar] using one)
    (by simpa [S₀,a,Atom.apply,Store.setScalar] using positive)
    (by simpa [S₀,a,Atom.apply,Store.setScalar] using small)
    leftIndex rightIndex
    (by simpa [S₀,a,Atom.apply,Store.setScalar] using leftSmall)
    (by simpa [S₀,a,Atom.apply,Store.setScalar] using rightSmall)
  have hpos : U.scalar .position = S.scalar .position := by
    have h := run.scalar_eq_of_not_mem Reg.position (by decide)
    simpa [S₀,a,Atom.apply,Store.setScalar] using h
  have hout : U.array .output = S.array .output :=
    run.array_eq_of_not_mem Arr.output (by decide)
  have he : U.scalar .sum = matrixEntry S (S.scalar .position) := by
    simpa [matrixEntry,S₀,a,Atom.apply,Store.setScalar] using hacc
  have hin : S₀.scalar .inner = S.scalar .inner := by simp [S₀,a,Atom.apply,Store.setScalar]
  rw [hin] at ht
  let w : Atom Reg Arr := .write .output .position .sum
  have valid : w.Valid U := by
    change U.scalar .position < (U.array .output).length
    rw [hpos,hout,outputLength]
    exact position
  have last := atom_runs hU w valid trivial
  refine ⟨1+(t+(1+0)), by omega, w.apply U,
    .seq ra (.seq run (.seq last (.skip last.end_bound))), w.apply_bounded hU trivial, ?_⟩
  simp [w,Atom.apply,hout,hpos,he]

def multiplyInputs : Finset Reg := {.rows,.inner,.cols,.modulus,.one,.total}

structure MultiplyState (S : State) (M i : ℕ) (T : State) : Prop where
  bounded : T.Bounded M
  inputs : ∀ r∈multiplyInputs, T.scalar r = S.scalar r
  left : T.array .left = S.array .left
  right : T.array .right = S.array .right
  written : ArrayTabulation.Prefix (matrixEntry S) (S.scalar .total) i (T.array .output)
  position : T.scalar .position = i
  todo : T.scalar .todo = S.scalar .total-i

theorem matrixEntry_congr {S T : State} (inputs : ∀ r∈multiplyInputs, T.scalar r=S.scalar r)
    (left : T.array .left=S.array .left) (right : T.array .right=S.array .right) (i : ℕ) :
    matrixEntry T i = matrixEntry S i := by
  simp only [matrixEntry,inputs .inner (by decide),inputs .cols (by decide),
    inputs .modulus (by decide),left,right]

theorem multiplyLoop_runs (S : State) (M : ℕ) (bounded : S.Bounded M)
    (one : S.scalar .one=1) (positive : 0<S.scalar .modulus)
    (small : S.scalar .modulus*S.scalar .modulus+S.scalar .modulus≤M)
    (leftLength : (S.array .left).length=S.scalar .rows*S.scalar .inner)
    (rightLength : (S.array .right).length=S.scalar .inner*S.scalar .cols)
    (leftSmall : ∀ x∈S.array .left,x<S.scalar .modulus)
    (rightSmall : ∀ x∈S.array .right,x<S.scalar .modulus)
    (total : S.scalar .total=S.scalar .rows*S.scalar .cols)
    (output : S.array .output=List.replicate (S.scalar .total) 0) :
    ∃ t≤S.scalar .total*(12*S.scalar .inner+9)+3, ∃ T,
      Runs (storageBound Reg Arr M) (countedLoop .position .todo .total .one multiplyCell) S t T ∧
      T.Bounded M ∧ T.array .output=List.ofFn (fun i : Fin (S.scalar .total) => matrixEntry S i.val) := by
  let S₀ := S.setScalar .todo (S.scalar .total)
  let S₁ := S₀.setScalar .position 0
  have h₀ : S₀.Bounded M := bounded.setScalar _ (bounded.1 .total)
  have h₁ : S₁.Bounded M := h₀.setScalar _ (by omega)
  have start : MultiplyState S M 0 S₁ := by
    refine ⟨h₁,?_,rfl,rfl,?_,?_,?_⟩
    · intro r hr
      have hd : ∀ r∈multiplyInputs,r≠Reg.todo ∧ r≠Reg.position := by decide
      simp [S₁,S₀,Store.setScalar,(hd r hr).1,(hd r hr).2]
    · change ArrayTabulation.Prefix _ _ _ (S.array .output)
      rw [output]
      exact ArrayTabulation.Prefix.zero _ _
    · simp [S₁]
    · simp [S₁,S₀]
  have control : ∀ i≤S.scalar .total,∀ T,MultiplyState S M i T →
      T.scalar .position=i ∧ T.scalar .todo=S.scalar .total-i ∧ T.scalar .one=1 ∧
      T.size≤storageBound Reg Arr M := by
    intro i hi T hT
    exact ⟨hT.position,hT.todo,(hT.inputs .one (by decide)).trans one,
      Store.size_le_of_bounded hT.bounded⟩
  have step : ∀ i<S.scalar .total,∀ T,MultiplyState S M i T →
      ∃ t≤12*S.scalar .inner+6,∃ U,
        Runs (storageBound Reg Arr M) multiplyCell T t U ∧
        U.scalar .position=i ∧ U.scalar .todo=S.scalar .total-i ∧ U.scalar .one=1 ∧
        (U.setScalar .position (i+1)).size≤storageBound Reg Arr M ∧
        MultiplyState S M (i+1) (advance .position .todo U) := by
    intro i hi T hT
    have hrows := hT.inputs .rows (by decide)
    have hinner := hT.inputs .inner (by decide)
    have hcols := hT.inputs .cols (by decide)
    have hp := hT.inputs .modulus (by decide)
    obtain ⟨t,ht,U,run,hU,hout⟩ := multiplyCell_runs T M hT.bounded
      ((hT.inputs .one (by decide)).trans one) (by omega) (by rwa [hp])
      (by simpa only [hT.left,hrows,hinner] using leftLength)
      (by simpa only [hT.right,hinner,hcols] using rightLength)
      (by rw [hrows,hcols]; exact hT.written.1.trans total)
      (by simpa only [hT.position,hrows,hcols,←total] using hi)
      (by simpa only [hT.left,hp] using leftSmall)
      (by simpa only [hT.right,hp] using rightSmall)
    rw [hinner] at ht
    have frame (r : Reg) (hr : r∈multiplyInputs ∨ r=.position ∨ r=.todo) : U.scalar r=T.scalar r := by
      apply run.scalar_eq_of_not_mem
      have hd : ∀ r∈multiplyInputs,r∉multiplyCell.scalarWrites := by decide
      rcases hr with hr | hr | hr
      · exact hd r hr
      · subst r; decide
      · subst r; decide
    have hpos : U.scalar .position=i := (frame .position (by simp)).trans hT.position
    have htodo : U.scalar .todo=S.scalar .total-i := (frame .todo (by simp)).trans hT.todo
    have hone : U.scalar .one=1 :=
      (frame .one (by decide)).trans ((hT.inputs .one (by decide)).trans one)
    have hiM : i+1≤M := le_trans (by omega) (bounded.1 .total)
    have hmid := hU.setScalar Reg.position hiM
    have hfinal : (advance .position .todo U).Bounded M := by
      simpa only [advance,hpos] using hmid.setScalar Reg.todo
        ((Nat.sub_le (U.scalar .todo) 1).trans (hU.1 .todo))
    refine ⟨t,ht,U,run,hpos,htodo,hone,Store.size_le_of_bounded hmid,
      hfinal,?_,?_,?_,?_,?_,?_⟩
    · intro r hr
      have hd : ∀ r∈multiplyInputs,r≠Reg.position ∧ r≠Reg.todo := by decide
      simpa [advance,Store.setScalar,(hd r hr).1,(hd r hr).2] using
        (frame r (Or.inl hr)).trans (hT.inputs r hr)
    · exact (run.array_eq_of_not_mem Arr.left (by decide)).trans hT.left
    · exact (run.array_eq_of_not_mem Arr.right (by decide)).trans hT.right
    · change ArrayTabulation.Prefix _ _ _ (U.array .output)
      rw [hout,hT.position,matrixEntry_congr hT.inputs hT.left hT.right]
      exact hT.written.write hi
    · simp [advance,Store.setScalar,hpos]
    · simp [advance,Store.setScalar,htodo,Nat.sub_sub]
  obtain ⟨t,ht,T,run,hT⟩ := countedLoop_runs (storageBound Reg Arr M)
    Reg.position Reg.todo Reg.total Reg.one multiplyCell (S.scalar .total)
    (12*S.scalar .inner+6) (MultiplyState S M) S
    (Store.size_le_of_bounded bounded) (Store.size_le_of_bounded h₀) start control
    (by decide) (by decide) step
  exact ⟨t,by nlinarith,T,run,hT.bounded,hT.written.complete⟩

def multiplyPrelude : List (Atom Reg Arr) := [
  .const .one 1,.const .zero 0,.binary .mul .total .rows .cols,.allocate .output .total .zero]

theorem multiply_runs (S : State) (M : ℕ) (bounded : S.Bounded M) (nonzero : 1≤M)
    (positive : 0<S.scalar .modulus)
    (small : S.scalar .modulus*S.scalar .modulus+S.scalar .modulus≤M)
    (totalBound : S.scalar .rows*S.scalar .cols≤M)
    (leftLength : (S.array .left).length=S.scalar .rows*S.scalar .inner)
    (rightLength : (S.array .right).length=S.scalar .inner*S.scalar .cols)
    (leftSmall : ∀ x∈S.array .left,x<S.scalar .modulus)
    (rightSmall : ∀ x∈S.array .right,x<S.scalar .modulus) :
    ∃ t≤(S.scalar .rows*S.scalar .cols)*(12*S.scalar .inner+9)+7,∃ T,
      Runs (storageBound Reg Arr M) multiply S t T ∧ T.Bounded M ∧
      T.array .output=List.ofFn (fun i : Fin (S.scalar .rows*S.scalar .cols) => matrixEntry S i.val) := by
  have valid : ValidAtoms M multiplyPrelude S := by
    simpa [multiplyPrelude,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,
      BinaryOp.eval,Store.setScalar] using And.intro nonzero totalBound
  obtain ⟨pre,bound⟩ := atoms_runs bounded multiplyPrelude valid
  let U := applyAtoms multiplyPrelude S
  have eqs : ∀ r∈({Reg.rows,.inner,.cols,.modulus} : Finset Reg),U.scalar r=S.scalar r := by
    intro r hr
    apply pre.scalar_eq_of_not_mem
    have hd : ∀ r∈({Reg.rows,.inner,.cols,.modulus} : Finset Reg),r∉(atoms multiplyPrelude).scalarWrites := by decide
    exact hd r hr
  have hrows := eqs .rows (by decide)
  have hinner := eqs .inner (by decide)
  have hcols := eqs .cols (by decide)
  have hp := eqs .modulus (by decide)
  have hleft : U.array .left=S.array .left := pre.array_eq_of_not_mem _ (by decide)
  have hright : U.array .right=S.array .right := pre.array_eq_of_not_mem _ (by decide)
  have hone : U.scalar .one=1 := by simp [U,applyAtoms,multiplyPrelude,Atom.apply,Store.setScalar]
  have ht : U.scalar .total=S.scalar .rows*S.scalar .cols := by
    simp [U,applyAtoms,multiplyPrelude,Atom.apply,BinaryOp.eval,Store.setScalar]
  have ho : U.array .output=List.replicate (U.scalar .total) 0 := by
    simp [U,applyAtoms,multiplyPrelude,Atom.apply,BinaryOp.eval,Store.setScalar]
  obtain ⟨t,hbound,T,run,hT,hout⟩ := multiplyLoop_runs U M bound hone (by omega)
    (by rwa [hp]) (by simpa only [hleft,hrows,hinner] using leftLength)
    (by simpa only [hright,hinner,hcols] using rightLength)
    (by simpa only [hleft,hp] using leftSmall) (by simpa only [hright,hp] using rightSmall)
    (by simpa only [hrows,hcols] using ht) ho
  have hm : ∀ i,matrixEntry U i=matrixEntry S i := by
    intro i
    simp only [matrixEntry,hleft,hright,hinner,hcols,hp]
  rw [ht,hinner] at hbound
  have trace : Runs (storageBound Reg Arr M) multiply S (4+t) T := .seq pre run
  refine ⟨4+t,by omega,T,trace,hT,?_⟩
  simpa only [ht,hm] using hout

end GroupWL.MachinePrograms.MatrixArithmetic
