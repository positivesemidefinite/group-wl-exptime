import GroupWL.MachinePrograms.NatArrayProofs
import GroupWL.MachinePrograms.NatArrayCountedLoops
import GroupWL.MachinePrograms.NatArrayFrames
import GroupWL.MachinePrograms.ArrayTabulation

/-! A fixed finite-register client assembles an evaluation tensor from its
operator-basis and input-twist arrays. -/
namespace GroupWL.MachinePrograms.EvaluationAssembly

open NatArrayLanguage
set_option maxHeartbeats 1000000

inductive Reg where
  | xdim | ydim | zdim | modulus | inputdim | total | position | remaining | one | zero
  | ij | i | j | z | leftFlag | rightFlag | row | col | index | value | quotient
  deriving DecidableEq, Fintype
inductive Arr where | operators | twist | output deriving DecidableEq, Fintype
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def readAtoms (source : Arr) : List (Atom Reg Arr) := [
  .binary .mul .index .row .xdim,
  .binary .add .index .index .col,
  .binary .mul .index .index .zdim,
  .binary .add .index .index .z,
  .read .value source .index]

def readCoefficient (source : Arr) : Code := atoms (readAtoms source)

def operatorReadAtoms : List (Atom Reg Arr) := [
  .binary .mul .index .row .zdim,
  .binary .add .index .index .z,
  .binary .mul .index .index .ydim,
  .binary .add .index .index .col,
  .read .value .operators .index]

def leftLeftAtoms : List (Atom Reg Arr) :=
  [.copy .row .i,.copy .col .j] ++ readAtoms .twist
def leftRightAtoms : List (Atom Reg Arr) :=
  [.copy .row .i,.binary .sub .col .j .xdim] ++ operatorReadAtoms
def rightLeftAtoms : List (Atom Reg Arr) :=
  [.copy .row .j,.binary .sub .col .i .xdim] ++ operatorReadAtoms ++
    [.binary .sub .value .modulus .value,.divmod .quotient .value .value .modulus]
def leftLeft : Code := atoms leftLeftAtoms
def leftRight : Code := atoms leftRightAtoms
def rightLeft : Code := atoms rightLeftAtoms
def rightRight : Code := .atom (.const .value 0)

def selectCoefficient : Code :=
  .branch .leftFlag (.branch .rightFlag leftLeft leftRight)
    (.branch .rightFlag rightLeft rightRight)

def decodeAtoms : List (Atom Reg Arr) := [
  .divmod .ij .z .position .zdim,
  .divmod .i .j .ij .inputdim,
  .binary .lt .leftFlag .i .xdim,
  .binary .lt .rightFlag .j .xdim]

def cell : Code := .seq (atoms decodeAtoms)
  (.seq selectCoefficient (.atom (.write .output .position .value)))

def prelude : List (Atom Reg Arr) := [
  .const .one 1,.const .zero 0,
  .binary .add .inputdim .xdim .ydim,
  .binary .mul .total .inputdim .inputdim,
  .binary .mul .total .total .zdim,
  .allocate .output .total .zero]

def program : Code := .seq (atoms prelude)
  (countedLoop .position .remaining .total .one cell)

def read (xs : List ℕ) (i : ℕ) : ℕ := xs[i]?.getD 0

def coefficient (a b p : ℕ) (H E : List ℕ) (m i j z : ℕ) : ℕ :=
  if i<a then
    if j<a then read E ((i*a+j)*m+z) else read H ((i*m+z)*b+(j-a))
  else
    if j<a then (p-read H ((j*m+z)*b+(i-a)))%p else 0

def flatCoefficient (a b m p : ℕ) (H E : List ℕ) (k : ℕ) : ℕ :=
  coefficient a b p H E m (k/m/(a+b)) (k/m%(a+b)) (k%m)

theorem readCoefficient_runs (source : Arr) (S : State) (M : ℕ) (bounded : S.Bounded M)
    (depth : 0<S.scalar .zdim)
    (validIndex : (S.scalar .row*S.scalar .xdim+S.scalar .col)*S.scalar .zdim+S.scalar .z <
      (S.array source).length) :
    Runs (storageBound Reg Arr M) (readCoefficient source) S 5 (applyAtoms (readAtoms source) S) ∧
      (applyAtoms (readAtoms source) S).Bounded M ∧
      (applyAtoms (readAtoms source) S).scalar .value = read (S.array source)
        ((S.scalar .row*S.scalar .xdim+S.scalar .col)*S.scalar .zdim+S.scalar .z) := by
  have hlen := bounded.2.1 source
  have hmul : S.scalar .row*S.scalar .xdim ≤ M := by nlinarith
  have hadd : S.scalar .row*S.scalar .xdim+S.scalar .col ≤ M := by nlinarith
  have hmul' : (S.scalar .row*S.scalar .xdim+S.scalar .col)*S.scalar .zdim ≤ M := by omega
  have hadd' : (S.scalar .row*S.scalar .xdim+S.scalar .col)*S.scalar .zdim+S.scalar .z ≤ M := by omega
  have hv : ValidAtoms M (readAtoms source) S := by
    simp [readAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,Function.update_apply]
    exact ⟨hmul,hadd,hmul',hadd',validIndex⟩
  obtain ⟨hr,hb⟩ := atoms_runs bounded (readAtoms source) hv
  refine ⟨hr,hb,?_⟩
  simp [readAtoms,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,read,Function.update_apply]

theorem leftLeft_runs (S : State) (M : ℕ) (bounded : S.Bounded M)
    (depth : 0<S.scalar .zdim)
    (validIndex : (S.scalar .i*S.scalar .xdim+S.scalar .j)*S.scalar .zdim+S.scalar .z <
      (S.array .twist).length) :
    Runs (storageBound Reg Arr M) leftLeft S 7 (applyAtoms leftLeftAtoms S) ∧
      (applyAtoms leftLeftAtoms S).Bounded M ∧
      (applyAtoms leftLeftAtoms S).scalar .value = read (S.array .twist)
        ((S.scalar .i*S.scalar .xdim+S.scalar .j)*S.scalar .zdim+S.scalar .z) := by
  have hlen := bounded.2.1 Arr.twist
  have hmul : S.scalar .i*S.scalar .xdim ≤ M := by nlinarith
  have hadd : S.scalar .i*S.scalar .xdim+S.scalar .j ≤ M := by nlinarith
  have hmul' : (S.scalar .i*S.scalar .xdim+S.scalar .j)*S.scalar .zdim ≤ M := by omega
  have hadd' : (S.scalar .i*S.scalar .xdim+S.scalar .j)*S.scalar .zdim+S.scalar .z ≤ M := by omega
  have hv : ValidAtoms M leftLeftAtoms S := by
    simp [leftLeftAtoms,readAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,Function.update_apply]
    exact ⟨hmul,hadd,hmul',hadd',validIndex⟩
  obtain ⟨hr,hb⟩ := atoms_runs bounded leftLeftAtoms hv
  refine ⟨hr,hb,?_⟩
  simp [leftLeftAtoms,readAtoms,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,read,Function.update_apply]

theorem leftRight_runs (S : State) (M : ℕ) (bounded : S.Bounded M)
    (width : 0<S.scalar .ydim)
    (validIndex : (S.scalar .i*S.scalar .zdim+S.scalar .z)*S.scalar .ydim+(S.scalar .j-S.scalar .xdim) <
      (S.array .operators).length) :
    Runs (storageBound Reg Arr M) leftRight S 7 (applyAtoms leftRightAtoms S) ∧
      (applyAtoms leftRightAtoms S).Bounded M ∧
      (applyAtoms leftRightAtoms S).scalar .value = read (S.array .operators)
        ((S.scalar .i*S.scalar .zdim+S.scalar .z)*S.scalar .ydim+(S.scalar .j-S.scalar .xdim)) := by
  have hlen := bounded.2.1 Arr.operators
  have hsub : S.scalar .j-S.scalar .xdim ≤ M := (Nat.sub_le _ _).trans (bounded.1 .j)
  have hmul : S.scalar .i*S.scalar .zdim ≤ M := by nlinarith
  have hadd : S.scalar .i*S.scalar .zdim+S.scalar .z ≤ M := by nlinarith
  have hmul' : (S.scalar .i*S.scalar .zdim+S.scalar .z)*S.scalar .ydim ≤ M := by omega
  have hadd' : (S.scalar .i*S.scalar .zdim+S.scalar .z)*S.scalar .ydim+(S.scalar .j-S.scalar .xdim) ≤ M := by omega
  have hv : ValidAtoms M leftRightAtoms S := by
    simp [leftRightAtoms,operatorReadAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,Function.update_apply]
    exact ⟨by omega,hmul,hadd,hmul',hadd',validIndex⟩
  obtain ⟨hr,hb⟩ := atoms_runs bounded leftRightAtoms hv
  refine ⟨hr,hb,?_⟩
  simp [leftRightAtoms,operatorReadAtoms,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,read,Function.update_apply]

theorem rightLeft_runs (S : State) (M : ℕ) (bounded : S.Bounded M)
    (width : 0<S.scalar .ydim) (positive : 0<S.scalar .modulus)
    (validIndex : (S.scalar .j*S.scalar .zdim+S.scalar .z)*S.scalar .ydim+(S.scalar .i-S.scalar .xdim) <
      (S.array .operators).length) :
    Runs (storageBound Reg Arr M) rightLeft S 9 (applyAtoms rightLeftAtoms S) ∧
      (applyAtoms rightLeftAtoms S).Bounded M ∧
      (applyAtoms rightLeftAtoms S).scalar .value =
        (S.scalar .modulus-read (S.array .operators)
        ((S.scalar .j*S.scalar .zdim+S.scalar .z)*S.scalar .ydim+(S.scalar .i-S.scalar .xdim)))%S.scalar .modulus := by
  have hlen := bounded.2.1 Arr.operators
  have hsub : S.scalar .i-S.scalar .xdim ≤ M := (Nat.sub_le _ _).trans (bounded.1 .i)
  have hmul : S.scalar .j*S.scalar .zdim ≤ M := by nlinarith
  have hadd : S.scalar .j*S.scalar .zdim+S.scalar .z ≤ M := by nlinarith
  have hmul' : (S.scalar .j*S.scalar .zdim+S.scalar .z)*S.scalar .ydim ≤ M := by omega
  have hadd' : (S.scalar .j*S.scalar .zdim+S.scalar .z)*S.scalar .ydim+(S.scalar .i-S.scalar .xdim) ≤ M := by omega
  have hneg : S.scalar .modulus-read (S.array .operators)
        ((S.scalar .j*S.scalar .zdim+S.scalar .z)*S.scalar .ydim+(S.scalar .i-S.scalar .xdim)) ≤ M :=
    (Nat.sub_le _ _).trans (bounded.1 .modulus)
  have hv : ValidAtoms M rightLeftAtoms S := by
    simp [rightLeftAtoms,operatorReadAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,Function.update_apply]
    exact ⟨by omega,hmul,hadd,hmul',hadd',validIndex,by simpa [Nat.sub_le_iff_le_add,read] using hneg,positive⟩
  obtain ⟨hr,hb⟩ := atoms_runs bounded rightLeftAtoms hv
  refine ⟨hr,hb,?_⟩
  simp [rightLeftAtoms,operatorReadAtoms,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,read,Function.update_apply]

theorem index2_lt {i j n m : ℕ} (hi : i<n) (hj : j<m) : i*m+j<n*m := by
  have h := Nat.mul_le_mul_right m (Nat.succ_le_of_lt hi)
  nlinarith

theorem selectCoefficient_runs (S : State) (M : ℕ) (bounded : S.Bounded M)
    (positive : 0<S.scalar .modulus)
    (iBound : S.scalar .i<S.scalar .xdim+S.scalar .ydim)
    (jBound : S.scalar .j<S.scalar .xdim+S.scalar .ydim)
    (zBound : S.scalar .z<S.scalar .zdim)
    (operatorsLength : (S.array .operators).length=S.scalar .xdim*S.scalar .zdim*S.scalar .ydim)
    (twistLength : (S.array .twist).length=S.scalar .xdim*S.scalar .xdim*S.scalar .zdim)
    (leftFlag : S.scalar .leftFlag=if S.scalar .i<S.scalar .xdim then 1 else 0)
    (rightFlag : S.scalar .rightFlag=if S.scalar .j<S.scalar .xdim then 1 else 0) :
    ∃ t≤11, ∃ U, Runs (storageBound Reg Arr M) selectCoefficient S t U ∧ U.Bounded M ∧
      U.scalar .value=coefficient (S.scalar .xdim) (S.scalar .ydim) (S.scalar .modulus)
        (S.array .operators) (S.array .twist) (S.scalar .zdim) (S.scalar .i) (S.scalar .j) (S.scalar .z) := by
  by_cases hi : S.scalar .i<S.scalar .xdim
  · have hleft : S.scalar .leftFlag≠0 := by simp [leftFlag,hi]
    by_cases hj : S.scalar .j<S.scalar .xdim
    · have hright : S.scalar .rightFlag≠0 := by simp [rightFlag,hj]
      obtain ⟨hr,hb,hv⟩ := leftLeft_runs S M bounded (by omega) (by
        rw [twistLength]; exact index2_lt (index2_lt hi hj) zBound)
      refine ⟨9,by omega,_,.branch_nonzero hleft (.branch_nonzero hright hr),hb,?_⟩
      simpa [coefficient,hi,hj] using hv
    · have hright : S.scalar .rightFlag=0 := by simp [rightFlag,hj]
      have hj' : S.scalar .j-S.scalar .xdim<S.scalar .ydim := by omega
      obtain ⟨hr,hb,hv⟩ := leftRight_runs S M bounded (by omega) (by
        rw [operatorsLength]; exact index2_lt (index2_lt hi zBound) hj')
      refine ⟨9,by omega,_,.branch_nonzero hleft (.branch_zero hright hr),hb,?_⟩
      simpa [coefficient,hi,hj] using hv
  · have hleft : S.scalar .leftFlag=0 := by simp [leftFlag,hi]
    by_cases hj : S.scalar .j<S.scalar .xdim
    · have hright : S.scalar .rightFlag≠0 := by simp [rightFlag,hj]
      have hi' : S.scalar .i-S.scalar .xdim<S.scalar .ydim := by omega
      obtain ⟨hr,hb,hv⟩ := rightLeft_runs S M bounded (by omega) positive (by
        rw [operatorsLength]; exact index2_lt (index2_lt hj zBound) hi')
      refine ⟨11,by omega,_,.branch_zero hleft (.branch_nonzero hright hr),hb,?_⟩
      simpa [coefficient,hi,hj] using hv
    · have hright : S.scalar .rightFlag=0 := by simp [rightFlag,hj]
      have hr := atom_runs bounded (Atom.const Reg.value 0) trivial (by simp [Atom.SmallResult])
      refine ⟨3,by omega,_,.branch_zero hleft (.branch_zero hright hr),bounded.setScalar _ (by omega),?_⟩
      simp [Atom.apply,coefficient,hi,hj]

def entry (S : State) (k : ℕ) : ℕ :=
  flatCoefficient (S.scalar .xdim) (S.scalar .ydim) (S.scalar .zdim) (S.scalar .modulus)
    (S.array .operators) (S.array .twist) k

theorem cell_runs (S : State) (M : ℕ) (bounded : S.Bounded M)
    (positive : 0<S.scalar .modulus)
    (inputdim : S.scalar .inputdim=S.scalar .xdim+S.scalar .ydim)
    (operatorsLength : (S.array .operators).length=S.scalar .xdim*S.scalar .zdim*S.scalar .ydim)
    (twistLength : (S.array .twist).length=S.scalar .xdim*S.scalar .xdim*S.scalar .zdim)
    (outputLength : (S.array .output).length=S.scalar .inputdim*S.scalar .inputdim*S.scalar .zdim)
    (position : S.scalar .position<S.scalar .inputdim*S.scalar .inputdim*S.scalar .zdim) :
    ∃ t≤16, ∃ U, Runs (storageBound Reg Arr M) cell S t U ∧ U.Bounded M ∧
      U.array .output=(S.array .output).set (S.scalar .position) (entry S (S.scalar .position)) := by
  have hn : 0<S.scalar .inputdim := by
    by_contra h; have he := Nat.eq_zero_of_not_pos h; simp [he] at position
  have hm : 0<S.scalar .zdim := by
    by_contra h; have he := Nat.eq_zero_of_not_pos h; simp [he] at position
  have hM : 1≤M := le_trans positive (bounded.1 .modulus)
  have hrow : S.scalar .position/S.scalar .zdim<S.scalar .inputdim*S.scalar .inputdim :=
    (Nat.div_lt_iff_lt_mul hm).2 position
  have hi : S.scalar .position/S.scalar .zdim/S.scalar .inputdim<S.scalar .inputdim :=
    (Nat.div_lt_iff_lt_mul hn).2 hrow
  have hj := Nat.mod_lt (S.scalar .position/S.scalar .zdim) hn
  have hz := Nat.mod_lt (S.scalar .position) hm
  have hv : ValidAtoms M decodeAtoms S := by
    simp [decodeAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,Function.update_apply]
    split_ifs <;> omega
  obtain ⟨rd,bd⟩ := atoms_runs bounded decodeAtoms hv
  let S₀ := applyAtoms decodeAtoms S
  have sc (r : Reg) (hr : r∈({.xdim,.ydim,.zdim,.modulus,.inputdim,.position} : Finset Reg)) :
      S₀.scalar r=S.scalar r := rd.scalar_eq_of_not_mem r (by
    have hd : ∀r∈({.xdim,.ydim,.zdim,.modulus,.inputdim,.position} : Finset Reg),
      r∉(atoms decodeAtoms : Code).scalarWrites := by decide
    exact hd r hr)
  have ha (a : Arr) : S₀.array a=S.array a := rfl
  have si : S₀.scalar .i=S.scalar .position/S.scalar .zdim/S.scalar .inputdim := by
    simp [S₀,decodeAtoms,applyAtoms,Atom.apply,Store.setScalar]
  have sj : S₀.scalar .j=S.scalar .position/S.scalar .zdim%S.scalar .inputdim := by
    simp [S₀,decodeAtoms,applyAtoms,Atom.apply,Store.setScalar]
  have sz : S₀.scalar .z=S.scalar .position%S.scalar .zdim := by
    simp [S₀,decodeAtoms,applyAtoms,Atom.apply,Store.setScalar]
  obtain ⟨t,ht,U,run,hU,hvalue⟩ := selectCoefficient_runs S₀ M bd
    (by rwa [sc .modulus (by decide)])
    (by rw [si,sc .xdim (by decide),sc .ydim (by decide),←inputdim]; exact hi)
    (by rw [sj,sc .xdim (by decide),sc .ydim (by decide),←inputdim]; exact hj)
    (by rw [sz,sc .zdim (by decide)]; exact hz)
    (by simpa only [ha,sc .xdim (by decide),sc .zdim (by decide),sc .ydim (by decide)] using operatorsLength)
    (by simpa only [ha,sc .xdim (by decide),sc .zdim (by decide)] using twistLength)
    (by simp [S₀,decodeAtoms,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar])
    (by simp [S₀,decodeAtoms,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar])
  have hp : U.scalar .position=S.scalar .position :=
    (run.scalar_eq_of_not_mem .position (by decide)).trans (sc .position (by decide))
  have hout : U.array .output=S.array .output := run.array_eq_of_not_mem .output (by decide)
  have he : U.scalar .value=entry S (S.scalar .position) := by
    simpa only [entry,flatCoefficient,si,sj,sz,ha,sc .xdim (by decide),sc .ydim (by decide),
      sc .zdim (by decide),sc .modulus (by decide),inputdim] using hvalue
  let w : Atom Reg Arr := .write .output .position .value
  have valid : w.Valid U := by
    change U.scalar .position<(U.array .output).length
    rw [hp,hout,outputLength]
    exact position
  have last := atom_runs hU w valid trivial
  refine ⟨4+(t+1),by omega,w.apply U,.seq rd (.seq run last),w.apply_bounded hU trivial,?_⟩
  simp [w,Atom.apply,hout,hp,he]

def inputs : Finset Reg := {.xdim,.ydim,.zdim,.modulus,.inputdim,.total,.one}

structure LoopState (S : State) (M i : ℕ) (T : State) : Prop where
  bounded : T.Bounded M
  inputs : ∀r∈inputs,T.scalar r=S.scalar r
  operators : T.array .operators=S.array .operators
  twist : T.array .twist=S.array .twist
  written : ArrayTabulation.Prefix (entry S) (S.scalar .total) i (T.array .output)
  position : T.scalar .position=i
  remaining : T.scalar .remaining=S.scalar .total-i

theorem entry_congr {S T : State} (h : ∀r∈inputs,T.scalar r=S.scalar r)
    (hH : T.array .operators=S.array .operators) (hE : T.array .twist=S.array .twist) (k : ℕ) :
    entry T k=entry S k := by
  simp only [entry,h .xdim (by decide),h .ydim (by decide),h .zdim (by decide),h .modulus (by decide),hH,hE]

theorem loop_runs (S : State) (M : ℕ) (bounded : S.Bounded M)
    (one : S.scalar .one=1) (positive : 0<S.scalar .modulus)
    (inputdim : S.scalar .inputdim=S.scalar .xdim+S.scalar .ydim)
    (operatorsLength : (S.array .operators).length=S.scalar .xdim*S.scalar .zdim*S.scalar .ydim)
    (twistLength : (S.array .twist).length=S.scalar .xdim*S.scalar .xdim*S.scalar .zdim)
    (total : S.scalar .total=S.scalar .inputdim*S.scalar .inputdim*S.scalar .zdim)
    (output : S.array .output=List.replicate (S.scalar .total) 0) :
    ∃t≤19*S.scalar .total+3,∃T,
      Runs (storageBound Reg Arr M) (countedLoop .position .remaining .total .one cell) S t T ∧
      T.Bounded M ∧ T.array .output=List.ofFn (fun i : Fin (S.scalar .total) => entry S i.val) := by
  let S₀ := S.setScalar .remaining (S.scalar .total)
  let S₁ := S₀.setScalar .position 0
  have h₀ : S₀.Bounded M := bounded.setScalar _ (bounded.1 .total)
  have h₁ : S₁.Bounded M := h₀.setScalar _ (by omega)
  have start : LoopState S M 0 S₁ := by
    refine ⟨h₁,?_,rfl,rfl,?_,?_,?_⟩
    · intro r hr
      have hd : ∀r∈inputs,r≠Reg.remaining ∧ r≠Reg.position := by decide
      simp [S₁,S₀,Store.setScalar,(hd r hr).1,(hd r hr).2]
    · change ArrayTabulation.Prefix _ _ _ (S.array .output)
      rw [output]
      exact ArrayTabulation.Prefix.zero _ _
    · simp [S₁]
    · simp [S₁,S₀]
  have control : ∀i≤S.scalar .total,∀T,LoopState S M i T →
      T.scalar .position=i ∧ T.scalar .remaining=S.scalar .total-i ∧ T.scalar .one=1 ∧
      T.size≤storageBound Reg Arr M := by
    intro i hi T hT
    exact ⟨hT.position,hT.remaining,(hT.inputs .one (by decide)).trans one,
      Store.size_le_of_bounded hT.bounded⟩
  have step : ∀i<S.scalar .total,∀T,LoopState S M i T →
      ∃t≤16,∃U,Runs (storageBound Reg Arr M) cell T t U ∧
        U.scalar .position=i ∧ U.scalar .remaining=S.scalar .total-i ∧ U.scalar .one=1 ∧
        (U.setScalar .position (i+1)).size≤storageBound Reg Arr M ∧
        LoopState S M (i+1) (advance .position .remaining U) := by
    intro i hi T hT
    have ha := hT.inputs .xdim (by decide)
    have hb := hT.inputs .ydim (by decide)
    have hm := hT.inputs .zdim (by decide)
    have hp := hT.inputs .modulus (by decide)
    have hn := hT.inputs .inputdim (by decide)
    obtain ⟨t,ht,U,run,hU,hout⟩ := cell_runs T M hT.bounded (by omega)
      (by simpa only [ha,hb,hn] using inputdim)
      (by simpa only [hT.operators,ha,hm,hb] using operatorsLength)
      (by simpa only [hT.twist,ha,hm] using twistLength)
      (by rw [hn,hm]; exact hT.written.1.trans total)
      (by simpa only [hT.position,hn,hm,←total] using hi)
    have frame (r : Reg) (hr : r∈inputs ∨ r=.position ∨ r=.remaining) : U.scalar r=T.scalar r := by
      apply run.scalar_eq_of_not_mem
      have hd : ∀r∈inputs,r∉cell.scalarWrites := by decide
      rcases hr with hr | hr | hr
      · exact hd r hr
      · subst r; decide
      · subst r; decide
    have hpos : U.scalar .position=i := (frame .position (by simp)).trans hT.position
    have hrem : U.scalar .remaining=S.scalar .total-i := (frame .remaining (by simp)).trans hT.remaining
    have hone : U.scalar .one=1 :=
      (frame .one (by decide)).trans ((hT.inputs .one (by decide)).trans one)
    have hiM : i+1≤M := le_trans (by omega) (bounded.1 .total)
    have hmid := hU.setScalar Reg.position hiM
    have hfinal : (advance .position .remaining U).Bounded M := by
      simpa only [advance,hpos] using hmid.setScalar Reg.remaining
        ((Nat.sub_le (U.scalar .remaining) 1).trans (hU.1 .remaining))
    refine ⟨t,ht,U,run,hpos,hrem,hone,Store.size_le_of_bounded hmid,
      hfinal,?_,?_,?_,?_,?_,?_⟩
    · intro r hr
      have hd : ∀r∈inputs,r≠Reg.position ∧ r≠Reg.remaining := by decide
      simpa [advance,Store.setScalar,(hd r hr).1,(hd r hr).2] using
        (frame r (Or.inl hr)).trans (hT.inputs r hr)
    · exact (run.array_eq_of_not_mem Arr.operators (by decide)).trans hT.operators
    · exact (run.array_eq_of_not_mem Arr.twist (by decide)).trans hT.twist
    · change ArrayTabulation.Prefix _ _ _ (U.array .output)
      rw [hout,hT.position,entry_congr hT.inputs hT.operators hT.twist]
      exact hT.written.write hi
    · simp [advance,Store.setScalar,hpos]
    · simp [advance,Store.setScalar,hrem,Nat.sub_sub]
  obtain ⟨t,ht,T,run,hT⟩ := countedLoop_runs (storageBound Reg Arr M)
    Reg.position Reg.remaining Reg.total Reg.one cell (S.scalar .total) 16 (LoopState S M) S
    (Store.size_le_of_bounded bounded) (Store.size_le_of_bounded h₀) start control
    (by decide) (by decide) step
  exact ⟨t,by omega,T,run,hT.bounded,hT.written.complete⟩

theorem program_runs (S : State) (M : ℕ) (bounded : S.Bounded M)
    (positive : 0<S.scalar .modulus)
    (sizeBound : (S.scalar .xdim+S.scalar .ydim)+
      (S.scalar .xdim+S.scalar .ydim)*(S.scalar .xdim+S.scalar .ydim)+
      (S.scalar .xdim+S.scalar .ydim)*(S.scalar .xdim+S.scalar .ydim)*S.scalar .zdim≤M)
    (operatorsLength : (S.array .operators).length=S.scalar .xdim*S.scalar .zdim*S.scalar .ydim)
    (twistLength : (S.array .twist).length=S.scalar .xdim*S.scalar .xdim*S.scalar .zdim) :
    ∃t≤19*((S.scalar .xdim+S.scalar .ydim)*(S.scalar .xdim+S.scalar .ydim)*S.scalar .zdim)+9,
      ∃T,Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧
        T.scalar .inputdim=S.scalar .xdim+S.scalar .ydim ∧ T.scalar .zdim=S.scalar .zdim ∧
        T.array .output=List.ofFn (fun i : Fin
          ((S.scalar .xdim+S.scalar .ydim)*(S.scalar .xdim+S.scalar .ydim)*S.scalar .zdim) => entry S i.val) := by
  have nonzero : 1≤M := positive.trans_le (bounded.1 .modulus)
  have valid : ValidAtoms M prelude S := by
    simp [prelude,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar]
    omega
  obtain ⟨pre,bound⟩ := atoms_runs bounded prelude valid
  let U := applyAtoms prelude S
  have eqs : ∀r∈({Reg.xdim,.ydim,.zdim,.modulus} : Finset Reg),U.scalar r=S.scalar r := by
    intro r hr
    apply pre.scalar_eq_of_not_mem
    have hd : ∀r∈({Reg.xdim,.ydim,.zdim,.modulus} : Finset Reg),r∉(atoms prelude).scalarWrites := by decide
    exact hd r hr
  have ha := eqs .xdim (by decide)
  have hb := eqs .ydim (by decide)
  have hm := eqs .zdim (by decide)
  have hp := eqs .modulus (by decide)
  have hH : U.array .operators=S.array .operators := pre.array_eq_of_not_mem _ (by decide)
  have hE : U.array .twist=S.array .twist := pre.array_eq_of_not_mem _ (by decide)
  have hone : U.scalar .one=1 := by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar]
  have hn : U.scalar .inputdim=S.scalar .xdim+S.scalar .ydim := by
    simp [U,applyAtoms,prelude,Atom.apply,BinaryOp.eval,Store.setScalar]
  have ht : U.scalar .total=(S.scalar .xdim+S.scalar .ydim)*(S.scalar .xdim+S.scalar .ydim)*S.scalar .zdim := by
    simp [U,applyAtoms,prelude,Atom.apply,BinaryOp.eval,Store.setScalar]
  have ho : U.array .output=List.replicate (U.scalar .total) 0 := by
    simp [U,applyAtoms,prelude,Atom.apply,BinaryOp.eval,Store.setScalar]
  obtain ⟨t,hbound,T,run,hT,hout⟩ := loop_runs U M bound hone (by omega)
    (by simpa only [ha,hb] using hn)
    (by simpa only [hH,ha,hm,hb] using operatorsLength)
    (by simpa only [hE,ha,hm] using twistLength)
    (by simpa only [hn,hm] using ht) ho
  have he : ∀i,entry U i=entry S i := by
    intro i; simp only [entry,ha,hb,hm,hp,hH,hE]
  rw [ht] at hbound
  refine ⟨6+t,by omega,T,.seq pre run,hT,?_,?_,?_⟩
  · exact (run.scalar_eq_of_not_mem .inputdim (by decide)).trans hn
  · exact (run.scalar_eq_of_not_mem .zdim (by decide)).trans hm
  · simpa only [ht,he] using hout

end GroupWL.MachinePrograms.EvaluationAssembly
