import GroupWL.MachinePrograms.AlternationProgram
import GroupWL.MachinePrograms.NatArrayComponents

/-! Raw tensor scanning and the concrete alternating-form validator, composed. -/
namespace GroupWL.MachinePrograms.ValidatedTensorProgram
open NatArrayLanguage NatArrayParser
open NatArrayLowering (bitNat)
set_option maxRecDepth 4096

abbrev Reg := Fin 13 ⊕ AlternationCheck.Reg
abbrev Arr := Fin 2 ⊕ AlternationCheck.Arr
abbrev State := Store Reg Arr
abbrev Code := NatArrayLanguage.Program Reg Arr

def r : Fin 13 ↪ Reg := ⟨Sum.inl,Sum.inl_injective⟩
def v (x : BilinearEvaluation.Reg) : Reg := .inr (.inl x)
def validSlot : Reg := .inr (.inr .valid)
def coefficients : Arr := .inr (.inl .coefficients)
def input : Arr := .inl 0
def output : Arr := .inl 1

def transfer (p : ℕ) : List (Atom Reg Arr) := [
  .const (v .modulus) p,.copy (v .inputDimension) (r 11),
  .copy (v .outputDimension) (r 12),.copyArray coefficients output]

def validate (p : ℕ) : Code := .seq (atoms (transfer p))
  (.seq (AlternationCheck.program.map Sum.inr Sum.inr) (.atom (.copy (r 3) validSlot)))

def program (p : ℕ) : Code := .seq (rawTensorScan r input output p)
  (.branch (r 3) (validate p) .skip)

def validationCost (p n m : ℕ) : ℕ := p^n*(m*(14*n^2+9*n+11)+7)+3*n+15

theorem validate_runs (p : ℕ) [Fact p.Prime] (R : RawTensor) (wf : R.WellFormed p)
    (S : State) (M : ℕ) (bounded : S.Bounded M)
    (n : S.scalar (r 11)=R.inputDimension) (m : S.scalar (r 12)=R.outputDimension)
    (data : S.array output=R.coefficients) (room : p^3+p≤M) (power : p^R.inputDimension≤M) :
    ∃t≤validationCost p R.inputDimension R.outputDimension,∃T,
      Runs (storageBound Reg Arr M) (validate p) S t T ∧ T.Bounded M ∧
      T.scalar (r 3)≤1 ∧ (T.scalar (r 3)=1 ↔ R.Alternating p) ∧
      (∀i : Fin 13,i≠3 → T.scalar (r i)=S.scalar (r i)) ∧
      (∀i : Fin 2,T.array (.inl i)=S.array (.inl i)) := by
  let V := applyAtoms (transfer p) S
  obtain ⟨first,hV⟩ := atoms_runs bounded (transfer p)
    (by simp [transfer,ValidAtoms,Atom.Valid,Atom.SmallResult];omega)
  have vp : V.right.scalar (AlternationCheck.l .modulus)=p := by
    simp [V,applyAtoms,transfer,Atom.apply,Store.setScalar,Store.setArray,Store.right,v,coefficients,r,output,AlternationCheck.l]
  have vn : V.right.scalar (AlternationCheck.l .inputDimension)=R.inputDimension := by
    simpa [V,applyAtoms,transfer,Atom.apply,Store.setScalar,Store.setArray,Store.right,v,coefficients,r,output,AlternationCheck.l] using n
  have vm : V.right.scalar (AlternationCheck.l .outputDimension)=R.outputDimension := by
    simpa [V,applyAtoms,transfer,Atom.apply,Store.setScalar,Store.setArray,Store.right,v,coefficients,r,output,AlternationCheck.l] using m
  have vc : V.right.array (.inl .coefficients)=R.coefficients := by
    simpa [V,applyAtoms,transfer,Atom.apply,Store.setScalar,Store.setArray,Store.right,v,coefficients,r,output] using data
  obtain ⟨t,ht,U,middle,hU,hvalid,hiff⟩ := AlternationCheck.rawTensor_runs p R wf V.right M hV.right vp vn vm vc room power
  let W := V.left.join U
  have hW : W.Bounded M := hV.left.join hU
  have middle' : Runs (storageBound Reg Arr M) (AlternationCheck.program.map Sum.inr Sum.inr) V t W :=
    middle.right_bounded hV
  let copy : Atom Reg Arr := .copy (r 3) validSlot
  have last := atom_runs hW copy trivial trivial
  refine ⟨4+(t+1),by unfold validationCost;omega,copy.apply W,.seq first (.seq middle' last),
    copy.apply_bounded hW trivial,?_,?_,?_,?_⟩
  · exact hvalid
  · exact hiff
  · intro i hi
    change (Function.update W.scalar (r 3) (W.scalar validSlot)) (r i)=S.scalar (r i)
    rw [Function.update_of_ne (r.injective.ne hi)]
    change V.scalar (r i)=S.scalar (r i)
    apply first.scalar_eq_of_not_mem
    simp [transfer,atoms,NatArrayLanguage.sequence,Program.scalarWrites,Atom.scalarWrites,r,v]
  · intro i
    change V.array (.inl i)=S.array (.inl i)
    apply first.array_eq_of_not_mem
    simp [transfer,atoms,NatArrayLanguage.sequence,Program.arrayWrites,Atom.arrayWrites,coefficients]

theorem validationCost_mono (p n m N : ℕ) (positive : 0<p) (hn : n≤N) (hm : m≤N) :
    validationCost p n m≤validationCost p N N := by
  unfold validationCost
  gcongr

def scanCost (p N : ℕ) : ℕ := (N+1)^3*(7*N+19)+14*N+34+validationCost p N N+1

theorem program_runs (p : ℕ) [Fact p.Prime] (S : State) (w : List Bool) (pos M : ℕ)
    (bounded : S.Bounded M) (room : (w.length+1)^3≤M) (fieldRoom : p^3+p≤M)
    (powerRoom : p^w.length≤M) (position : S.scalar (r 0)=pos) (posBound : pos≤w.length)
    (length : S.scalar (r 1)=w.length) (valid : S.scalar (r 3)=1)
    (inputEq : S.array input=w.map bitNat) :
    ∃T t,t≤scanCost p w.length ∧ Runs (storageBound Reg Arr M) (program p) S t T ∧
      T.Bounded M ∧ T.scalar (r 0)≤w.length ∧ T.scalar (r 1)=w.length ∧
      T.scalar (r 3)≤1 ∧ T.array input=w.map bitNat ∧
      match Statement.readTensor p (w.drop pos) with
      | none => T.scalar (r 3)=0
      | some (tensor,tail) => T.scalar (r 3)=1 ∧ T.scalar (r 11)=tensor.inputDimension ∧
          T.scalar (r 12)=tensor.outputDimension ∧
          T.array output=TensorSerialization.coefficientList (tensor.coefficient p) ∧
          w.drop (T.scalar (r 0))=tail := by
  obtain ⟨V,t,ht,first,hV,vpos,vvalid,vlen,vinput,spec⟩ := rawTensorScan_correct r input output p
    (by decide) S w pos M bounded room (by omega) position posBound length valid inputEq
  have hp : 0<p := (Fact.out : p.Prime).pos
  cases parsed : readRawTensor p (w.drop pos) with
  | none =>
    have vv : V.scalar (r 3)=0 := by simpa only [parsed] using spec
    have tensor : Statement.readTensor p (w.drop pos)=none := by
      rw [←readValidatedTensor_eq p]
      simp [readValidatedTensor,parsed]
    refine ⟨V,t+1,by unfold scanCost;omega,.seq first (.branch_zero vv (.skip (Store.size_le_of_bounded hV))),
      hV,vpos,vlen,vvalid,vinput,?_⟩
    simpa only [tensor] using vv
  | some val =>
    rcases val with ⟨R,tail⟩
    have hs : V.scalar (r 3)=1 ∧ V.scalar (r 11)=R.inputDimension ∧
        V.scalar (r 12)=R.outputDimension ∧ V.array output=R.coefficients ∧
        w.drop (V.scalar (r 0))=tail := by simpa only [parsed] using spec
    obtain ⟨word,wf⟩ := readRawTensor_sound parsed
    have size : R.inputDimension+R.outputDimension≤w.length := by
      have hh := congrArg List.length word
      simp only [RawTensor.word,List.length_append,Statement.unary,List.length_replicate,List.length_singleton,List.length_drop] at hh
      omega
    have pn : p^R.inputDimension≤M := (pow_le_pow_right' (by omega) (by omega : R.inputDimension≤w.length)).trans powerRoom
    obtain ⟨u,hu,T,last,hT,tvalid,tiff,frame,arrays⟩ := validate_runs p R wf V M hV hs.2.1 hs.2.2.1 hs.2.2.2.1 fieldRoom pn
    have tpos := (frame 0 (by decide))
    have tlen := (frame 1 (by decide))
    have tn := (frame 11 (by decide))
    have tm := (frame 12 (by decide))
    have tinc : T.array input=V.array input := arrays 0
    have tout : T.array output=R.coefficients := (arrays 1).trans hs.2.2.2.1
    have budget := validationCost_mono p R.inputDimension R.outputDimension w.length hp (by omega) (by omega)
    refine ⟨T,t+(u+1),by unfold scanCost;omega,.seq first (.branch_nonzero (by omega) last),
      hT,by omega,by omega,tvalid,tinc.trans vinput,?_⟩
    rw [word,readTensor_rawWord p R wf]
    by_cases alt : R.Alternating p
    · simp only [dif_pos alt]
      refine ⟨tiff.mpr alt,by change T.scalar (r 11)=R.inputDimension;omega,
        by change T.scalar (r 12)=R.outputDimension;omega,?_,?_⟩
      · rw [RawTensor.toTensor_coefficient]
        exact tout.trans (RawTensor.coefficientList p R wf).symm
      · simpa only [tpos] using hs.2.2.2.2
    · simp only [dif_neg alt]
      have hh : T.scalar (r 3)≠1 := fun h=>alt (tiff.mp h)
      omega

end GroupWL.MachinePrograms.ValidatedTensorProgram
