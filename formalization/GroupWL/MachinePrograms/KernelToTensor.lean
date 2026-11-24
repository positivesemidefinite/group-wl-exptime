import GroupWL.MachinePrograms.ConstructiveTensorAssembly
import GroupWL.MachinePrograms.OperatorAssemblyEncoding
import GroupWL.WedgeOperatorClient
import GroupWL.MachinePrograms.NatArrayComponents
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
namespace GroupWL.MachinePrograms.NatArrayLanguage.Ports
variable {R A U V : Type} [DecidableEq R] [DecidableEq A] [DecidableEq U] [DecidableEq V]
variable [Fintype R] [Fintype A] [Fintype U] [Fintype V]

inductive Scalar (R A : Type)
  | literal (v : ℕ) | scalar (r : R) | length (a : A)

def target (s : U → Scalar R A) (a : V → Option A) (P : Store R A) : Store U V :=
  ⟨fun u => match s u with
    | .literal k => k
    | .scalar r => P.scalar r
    | .length i => (P.array i).length,
   fun v => match a v with | none => [] | some i => P.array i⟩

def op (s : U → Scalar R A) (a : V → Option A) :
    U ⊕ V → Atom (R ⊕ U) (A ⊕ V)
  | .inl u => match s u with
    | .literal k => .const (.inr u) k
    | .scalar r => .copy (.inr u) (.inl r)
    | .length i => .arrayLength (.inr u) (.inl i)
  | .inr v => match a v with
    | none => .clearArray (.inr v)
    | some i => .copyArray (.inr v) (.inl i)

noncomputable def fill (D : Store U V) (ls : List (U ⊕ V)) (Q : Store U V) : Store U V := by
  classical
  exact ⟨fun u => if Sum.inl u ∈ ls then D.scalar u else Q.scalar u,
   fun v => if Sum.inr v ∈ ls then D.array v else Q.array v⟩

theorem step (s : U → Scalar R A) (a : V → Option A) (P : Store R A) (Q : Store U V)
    (j : U ⊕ V) :
    (op s a j).apply (P.join Q) = P.join (fill (target s a P) [j] Q) := by
  classical
  cases j with
  | inl u =>
    cases hs : s u with
    | literal k =>
      apply Store.ext <;> intro i <;> cases i <;> simp only [op,hs,Atom.apply,fill,target,Store.join,Store.setScalar,Function.update_apply,Sum.elim_inl,Sum.elim_inr,List.mem_singleton,Sum.inr.injEq,Sum.inl.injEq,reduceCtorEq,ite_false] <;> split_ifs <;> subst_vars <;> simp_all
    | scalar r =>
      apply Store.ext <;> intro i <;> cases i <;> simp only [op,hs,Atom.apply,fill,target,Store.join,Store.setScalar,Function.update_apply,Sum.elim_inl,Sum.elim_inr,List.mem_singleton,Sum.inr.injEq,Sum.inl.injEq,reduceCtorEq,ite_false] <;> split_ifs <;> subst_vars <;> simp_all
    | length i =>
      apply Store.ext <;> intro j <;> cases j <;> simp only [op,hs,Atom.apply,fill,target,Store.join,Store.setScalar,Function.update_apply,Sum.elim_inl,Sum.elim_inr,List.mem_singleton,Sum.inr.injEq,Sum.inl.injEq,reduceCtorEq,ite_false] <;> split_ifs <;> subst_vars <;> simp_all
  | inr v =>
    cases ha : a v with
    | none =>
      apply Store.ext <;> intro i <;> cases i <;> simp only [op,ha,Atom.apply,fill,target,Store.join,Store.setArray,Function.update_apply,Sum.elim_inl,Sum.elim_inr,List.mem_singleton,Sum.inr.injEq,Sum.inl.injEq,reduceCtorEq,ite_false] <;> split_ifs <;> subst_vars <;> simp_all
    | some i =>
      apply Store.ext <;> intro j <;> cases j <;> simp only [op,ha,Atom.apply,fill,target,Store.join,Store.setArray,Function.update_apply,Sum.elim_inl,Sum.elim_inr,List.mem_singleton,Sum.inr.injEq,Sum.inl.injEq,reduceCtorEq,ite_false] <;> split_ifs <;> subst_vars <;> simp_all

theorem filled (s : U → Scalar R A) (a : V → Option A) (P : Store R A)
    (Q : Store U V) (ls : List (U ⊕ V)) :
    applyAtoms (ls.map (op s a)) (P.join Q) = P.join (fill (target s a P) ls Q) := by
  induction ls generalizing Q with
  | nil =>
    change P.join Q = P.join _
    congr 1
    apply Store.ext <;> intro i <;> simp [fill]
  | cons j ls ih =>
    change applyAtoms (ls.map (op s a)) ((op s a j).apply (P.join Q)) = _
    rw [step,ih]
    congr 1
    apply Store.ext <;> intro i <;> simp only [fill,List.mem_cons,List.mem_singleton] <;> split_ifs <;> simp_all

theorem valid (s : U → Scalar R A) (a : V → Option A) (m : ℕ)
    (small : ∀u k,s u = .literal k → k ≤ m) (ls : List (U⊕V)) (S : Store (R⊕U) (A⊕V)) :
    ValidAtoms m (ls.map (op s a)) S := by
  induction ls generalizing S with
  | nil => trivial
  | cons j js ih =>
    refine ⟨?_,?_,ih _⟩
    · cases j with
      | inl u => cases h : s u <;> simp [op,h,Atom.Valid]
      | inr v => cases h : a v <;> simp [op,h,Atom.Valid]
    · cases j with
      | inl u =>
        cases h : s u with
        | literal k => exact (by simpa [op,h,Atom.SmallResult] using small u k h)
        | scalar _ => simp [op,h,Atom.SmallResult]
        | length _ => simp [op,h,Atom.SmallResult]
      | inr v => cases h : a v <;> simp [op,h,Atom.SmallResult]

noncomputable def code (s : U → Scalar R A) (a : V → Option A) : Program (R⊕U) (A⊕V) :=
  atoms (Finset.univ.toList.map (op s a))

theorem code_runs (s : U → Scalar R A) (a : V → Option A) (P : Store R A) (Q : Store U V)
    (m : ℕ) (bounded : (P.join Q).Bounded m) (small : ∀u k,s u = .literal k → k ≤ m) :
    Runs (storageBound (R⊕U) (A⊕V) m) (code s a) (P.join Q) (Fintype.card U + Fintype.card V)
       (P.join (target s a P)) ∧ (target s a P).Bounded m := by
  classical
  let ls : List (U ⊕ V) := Finset.univ.toList
  obtain ⟨run,hT⟩ := atoms_runs bounded _ (valid s a m small ls (P.join Q))
  have hfill : fill (target s a P) ls Q = target s a P := by
    apply Store.ext <;> intro i <;> simp [fill,ls]
  rw [filled,hfill] at run hT
  exact ⟨by simpa [code,ls] using run,hT.right⟩

noncomputable def thenRun (first : Program R A) (s : U → Scalar R A)
    (a : V → Option A) (second : Program U V) : Program (R⊕U) (A⊕V) :=
  .seq (first.map Sum.inl Sum.inl) (.seq (code s a) (second.map Sum.inr Sum.inr))

theorem thenRun_runs (p : Program R A) (s : U → Scalar R A) (a : V → Option A)
    (q : Program U V) (S P : Store R A) (Q T : Store U V) (m t u : ℕ)
    (hs : S.Bounded m) (hp : P.Bounded m) (hq : Q.Bounded m)
    (small : ∀i k,s i = .literal k → k ≤ m)
    (first : Runs (storageBound R A m) p S t P)
    (second : Runs (storageBound U V m) q (target s a P) u T) :
    Runs (storageBound (R⊕U) (A⊕V) m) (thenRun p s a q) (S.join Q)
      (t + (Fintype.card U + Fintype.card V + u)) (P.join T) := by
  have first' := first.left_bounded (hs.join hq)
  obtain ⟨wire,hW⟩ := code_runs s a P Q m (hp.join hq) small
  have second' := second.right_bounded (hp.join hW)
  exact first'.seq (wire.seq second')


end GroupWL.MachinePrograms.NatArrayLanguage.Ports
set_option synthInstance.maxSize 65536
set_option maxRecDepth 8192
namespace GroupWL.ReuseKernel
open MachinePrograms ConstructiveCoordinates IncidenceTensor IncidenceGroup
variable (p : ℕ) [Fact p.Prime]
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [FiniteCode I] [FiniteCode J]
variable {V : J → Type} [∀j,AddCommGroup (V j)] [∀j,Module (ZMod p) (V j)]
variable (A : AffineSystem (ZMod p) I J V) (R : ∀j,Coordinates (ZMod p) (ReadoutRadical A j)) (q : ℕ)
local notation "XI" => ConstructiveIncidence.InputIndex A R q
local notation "ZI" => ConstructiveIncidence.OutputIndex A R q
theorem zeroArray :
    ConstructiveTensorAssembly.twistEntries p A R q AlternatingBilinearMap.zero =
        List.replicate (FiniteCode.size XI * FiniteCode.size XI * FiniteCode.size ZI) 0 := by
  have hz : (Coordinates.pi (F := ZMod p) ZI).equiv 0 = 0 := map_zero _
  simp only [ConstructiveTensorAssembly.twistEntries,EvaluationAssembly.twistEntries,EvaluationAssembly.entries3,
    twistCoordinates,LinearMap.mk₂_apply,AlternatingBilinearMap.zero_apply,map_zero,hz,Pi.zero_apply,ZMod.val_zero]
  exact List.ofFn_const _ 0
theorem operatorArray (hq : 0 < q) :
    ConstructiveTensorAssembly.operatorEntries p A R q hq =
      MatrixEncoding.word (CachedElimination.ofLinear
        (GeneratedCoordinateEntries.operatorChart (ConstructiveIncidence.chosenCoordinates A R q hq)
        (ConstructiveTensor.obstructionMap A R q hq)).lift) :=
  OperatorAssemblyEncoding.operatorEntries_eq_lift_word p _ _

open NatArrayLanguage EvaluationAssembly
def zeroPrep : List (Atom Reg Arr) :=
  [.binary .mul .total .xdim .xdim, .binary .mul .total .total .zdim,
   .const .zero 0, .allocate .twist .total .zero]

theorem zeroReady (S : EvaluationAssembly.State) (M : ℕ) (hS : S.Bounded M)
    (h1 : S.scalar .xdim * S.scalar .xdim ≤ M)
    (h2 : S.scalar .xdim * S.scalar .xdim * S.scalar .zdim ≤ M) :
    let U := applyAtoms zeroPrep S
    Runs (storageBound Reg Arr M) (atoms zeroPrep) S 4 U ∧ U.Bounded M ∧
    U.array .operators = S.array .operators ∧
    U.scalar .xdim = S.scalar .xdim ∧ U.scalar .ydim = S.scalar .ydim ∧
    U.scalar .zdim = S.scalar .zdim ∧ U.scalar .modulus = S.scalar .modulus ∧
    U.array .twist = List.replicate (S.scalar .xdim * S.scalar .xdim * S.scalar .zdim) 0 := by
  let ready : ValidAtoms M zeroPrep S := by
    simpa [zeroPrep,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar] using And.intro h1 h2
  refine ⟨(atoms_runs hS _ ready).1,(atoms_runs hS _ ready).2,?_⟩
  simp [applyAtoms,zeroPrep,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray]

local notation "H" => ConstructiveTensor.operatorCoordinates A R q
local notation "Y" => ConstructiveTensor.obstructionMap A R q
theorem baseFromKernel (hq : 0 < q) (gram : KernelProgram.State)
    (ready : KernelProgram.Represents p (FiniteCode.size XI * FiniteCode.size ZI) 0
      (ConstructiveIncidence.wedgeWord p A R q hq)
      (KernelProgramCorrectness.encode (GeneratedCoordinateEntries.operatorChart
        (ConstructiveIncidence.chosenCoordinates A R q hq) (Y hq))) gram)
    (S : EvaluationAssembly.State) (M : ℕ) (bounded : S.Bounded M)
    (hx : S.scalar .xdim = FiniteCode.size XI) (hz : S.scalar .zdim = FiniteCode.size ZI)
    (hy : S.scalar .ydim = gram.scalar (KernelProgram.wr .width))
    (hp : S.scalar .modulus = p) (hcopy : S.array .operators = gram.array (KernelProgram.wa .lift))
    (hsize : (FiniteCode.size XI+(H hq).dimension) +
      (FiniteCode.size XI+(H hq).dimension)*(FiniteCode.size XI+(H hq).dimension) +
      (FiniteCode.size XI+(H hq).dimension)*(FiniteCode.size XI+(H hq).dimension)*(FiniteCode.size ZI) ≤ M) :
    ∃ t ≤ 19*((FiniteCode.size XI+(H hq).dimension)*(FiniteCode.size XI+(H hq).dimension)*(FiniteCode.size ZI))+13,
    ∃ T : EvaluationAssembly.State,
      Runs (storageBound Reg Arr M) (.seq (atoms zeroPrep) EvaluationAssembly.program) S t T ∧
      T.Bounded M ∧ T.scalar .inputdim = (ConstructiveTensor.description q p A R hq AlternatingBilinearMap.zero).inputDimension ∧
      T.scalar .zdim = (ConstructiveTensor.description q p A R hq AlternatingBilinearMap.zero).outputDimension ∧
      T.array .output = TensorSerialization.coefficientList ((ConstructiveTensor.description q p A R hq AlternatingBilinearMap.zero).coefficient p) := by
  have hle : FiniteCode.size XI * FiniteCode.size XI ≤
      (FiniteCode.size XI+(H hq).dimension)*(FiniteCode.size XI+(H hq).dimension) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hle' := Nat.mul_le_mul_right (FiniteCode.size ZI) hle
  obtain ⟨r,b,op,x,y,z,prime,zero⟩ := zeroReady S M bounded (by rw [hx];omega) (by rw [hx,hz];omega)
  let U := applyAtoms zeroPrep S
  have hop : U.array .operators = ConstructiveTensorAssembly.operatorEntries p A R q hq := by
    rw [op,hcopy,ready.lift,operatorArray]
    rfl
  have ht : U.array .twist = ConstructiveTensorAssembly.twistEntries p A R q AlternatingBilinearMap.zero := by
    rw [zero,hx,hz,zeroArray]
  obtain ⟨t,bt,T,run,hB,hO⟩ := ConstructiveTensorAssembly.program_runs p A R q hq AlternatingBilinearMap.zero
    U M b (x.trans hx) (y.trans (hy.trans ready.width)) (z.trans hz) (prime.trans hp) hop ht hsize
  refine ⟨4+t,?_,T,r.seq run,hB,hO⟩
  change t ≤ 19 * ((FiniteCode.size XI + (H hq).dimension) * (FiniteCode.size XI + (H hq).dimension) * FiniteCode.size ZI) + 9 at bt
  omega

open NatArrayLanguage.Ports
abbrev KR := KernelProgram.Reg ⊕ Bool
abbrev KA := KernelProgram.Arr
def prev (K : KernelProgram.State) (x z : ℕ) : Store KR KA :=
  ⟨Sum.elim K.scalar (fun b => if b then z else x),K.array⟩
def scalars (p : ℕ) : EvaluationAssembly.Reg → Ports.Scalar KR KA
  | .xdim => .scalar (.inr false)
  | .zdim => .scalar (.inr true)
  | .ydim => .scalar (.inl (KernelProgram.wr .width))
  | .modulus => .literal p
  | _ => .literal 0
def arrays : EvaluationAssembly.Arr → Option KA
  | .operators => some (KernelProgram.wa .lift)
  | _ => none
noncomputable def baseCode (p : ℕ) : Program (KR⊕Reg) (KA⊕Arr) :=
  .seq (Ports.code (scalars p) arrays) ((.seq (atoms zeroPrep) EvaluationAssembly.program : EvaluationAssembly.Code).map Sum.inr Sum.inr)

theorem basePortRuns (hq : 0 < q) (K : KernelProgram.State) (Q : EvaluationAssembly.State) (M : ℕ)
    (ready : KernelProgram.Represents p (FiniteCode.size XI * FiniteCode.size ZI) 0
      (ConstructiveIncidence.wedgeWord p A R q hq)
      (KernelProgramCorrectness.encode (GeneratedCoordinateEntries.operatorChart
        (ConstructiveIncidence.chosenCoordinates A R q hq) (Y hq))) K)
    (hx : FiniteCode.size XI ≤ M) (hz : FiniteCode.size ZI ≤ M)
    (hK : K.Bounded M) (hQ : Q.Bounded M)
    (hsize : (FiniteCode.size XI+(H hq).dimension) +
      (FiniteCode.size XI+(H hq).dimension)*(FiniteCode.size XI+(H hq).dimension) +
      (FiniteCode.size XI+(H hq).dimension)*(FiniteCode.size XI+(H hq).dimension)*(FiniteCode.size ZI) ≤ M) :
    let P := prev K (FiniteCode.size XI) (FiniteCode.size ZI)
    ∃t ≤ (Fintype.card Reg+Fintype.card Arr)+19*((FiniteCode.size XI+(H hq).dimension)*(FiniteCode.size XI+(H hq).dimension)*(FiniteCode.size ZI))+13,
    ∃T : EvaluationAssembly.State,
      Runs (storageBound (KR⊕Reg) (KA⊕Arr) M) (baseCode p) (P.join Q) t (P.join T) ∧
      T.Bounded M ∧ T.scalar .inputdim = (ConstructiveTensor.description q p A R hq AlternatingBilinearMap.zero).inputDimension ∧
      T.scalar .zdim = (ConstructiveTensor.description q p A R hq AlternatingBilinearMap.zero).outputDimension ∧
      T.array .output = TensorSerialization.coefficientList ((ConstructiveTensor.description q p A R hq AlternatingBilinearMap.zero).coefficient p) := by
  dsimp only
  let P := prev K (FiniteCode.size XI) (FiniteCode.size ZI)
  have hpM : p ≤ M := ready.modulus ▸ hK.1 (KernelProgram.wr .modulus)
  have hP : P.Bounded M := by
    refine ⟨?_,hK.2⟩
    intro j
    cases j with
    | inl r => exact hK.1 r
    | inr b => cases b <;> simp [P,prev,hx,hz]
  obtain ⟨setup,bnd⟩ := Ports.code_runs (scalars p) arrays P Q M (hP.join hQ) (by
    intro reg n hn
    cases reg <;> simp [scalars] at hn <;> omega)
  obtain ⟨t,ht,T,run,bT,out⟩ := baseFromKernel p A R q hq K ready
    (Ports.target (scalars p) arrays P) M bnd rfl rfl rfl rfl rfl hsize
  exact ⟨_,by omega,T,setup.seq (run.right_bounded (hP.join bnd)),bT,out⟩


end GroupWL.ReuseKernel
