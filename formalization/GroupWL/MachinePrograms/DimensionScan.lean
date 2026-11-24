import GroupWL.MachinePrograms.DimensionParser

/-! Counted execution and total correctness of the dimension suffix scan. -/
namespace GroupWL.MachinePrograms.DimensionParser
open NatArrayLanguage
open NatArrayLowering (bitNat)
variable {Reg Arr : Type*} [DecidableEq Reg] [DecidableEq Arr] [Fintype Reg] [Fintype Arr]

private theorem drop_cons_info {w : List Bool} {pos : ℕ} {b : Bool} {tail : List Bool}
    (h : w.drop pos=b::tail) :
    ∃ hpos : pos<w.length,w[pos]=b ∧ w.drop (pos+1)=tail := by
  have hpos : pos<w.length := by have hh := congrArg List.length h;simp only [List.length_drop,List.length_cons] at hh;omega
  refine ⟨hpos,?_,?_⟩
  · have hh := congrArg (fun xs : List Bool=>xs[0]?) h
    simpa [List.getElem?_eq_getElem hpos] using hh
  · have hh := congrArg List.tail h
    simpa only [List.tail_drop,List.tail_cons] using hh

theorem bitStep_runs (e : Statement.DimensionEncoding) (r : Fin 9 ↪ Reg) (input : Arr)
    (S : Store Reg Arr) (w : List Bool) (pos acc v M : ℕ) (b : Bool)
    (bounded : S.Bounded M) (room : 1≤M) (position : S.scalar (r 0)=pos)
    (length : S.scalar (r 1)=w.length) (value : S.scalar (r 2)=acc)
    (valid : S.scalar (r 3)=v) (smallValid : v≤1)
    (one : S.scalar (r 7)=1) (two : S.scalar (r 8)=2)
    (inputEq : S.array input=w.map bitNat) (index : pos<w.length) (bit : w[pos]=b)
    (next : valueStep e acc b≤M) :
    ∃T,Runs (storageBound Reg Arr M) (bitStep e r input) S 5 T ∧ T.Bounded M ∧
      T.scalar (r 0)=pos+1 ∧ T.scalar (r 1)=w.length ∧
      T.scalar (r 2)=valueStep e acc b ∧ T.scalar (r 3)=validStep e v b ∧
      T.scalar (r 4)=(if pos+1<w.length then 1 else 0) ∧
      T.scalar (r 7)=1 ∧ T.scalar (r 8)=2 ∧ T.array input=w.map bitNat := by
  have hlen : w.length≤M := by simpa [length] using bounded.1 (r 1)
  have get : (w.map bitNat)[pos]?.getD 0=bitNat b := by simp [List.getElem?_eq_getElem index,bit]
  let as : List (Atom Reg Arr) := [.read (r 5) input (r 0),.binary .add (r 0) (r 0) (r 7)] ++
    (match e with
    | .binary => [.binary .mul (r 2) (r 2) (r 8),.binary .add (r 2) (r 2) (r 5)]
    | .unary => [.binary .add (r 2) (r 2) (r 7),.binary .mul (r 3) (r 3) (r 5)]) ++
    [.binary .lt (r 4) (r 0) (r 1)]
  have hv : ValidAtoms M as S := by
    cases e <;> cases b <;>
      simp only [valueStep,bitNat,Bool.false_eq_true,if_false,if_true] at next <;>
      simp [as,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
        Store.setScalar,r.injective.eq_iff,position,length,value,valid,one,two,inputEq,List.getElem?_eq_getElem index,bit,bitNat]
      <;> split_ifs <;> omega
  obtain ⟨run,hT⟩ := atoms_runs bounded as hv
  have hsize : as.length=5 := by cases e <;> rfl
  refine ⟨applyAtoms as S,?_,hT,?_⟩
  · simpa only [hsize] using run
  · cases e <;> cases b <;>
      simp [applyAtoms,as,Atom.apply,BinaryOp.eval,Store.setScalar,r.injective.eq_iff,
        position,length,value,valid,one,two,inputEq,List.getElem?_eq_getElem index,bit,valueStep,validStep,bitNat,Nat.mul_comm]

theorem suffixLoop_runs (e : Statement.DimensionEncoding) (r : Fin 9 ↪ Reg) (input : Arr)
    (bits : List Bool) (S : Store Reg Arr) (w : List Bool) (pos acc v M : ℕ)
    (bounded : S.Bounded M) (room : 1≤M) (position : S.scalar (r 0)=pos)
    (length : S.scalar (r 1)=w.length) (value : S.scalar (r 2)=acc)
    (valid : S.scalar (r 3)=v) (smallValid : v≤1)
    (scan : S.scalar (r 4)=(if pos<w.length then 1 else 0))
    (one : S.scalar (r 7)=1) (two : S.scalar (r 8)=2)
    (inputEq : S.array input=w.map bitNat) (posBound : pos≤w.length)
    (suffix : w.drop pos=bits) (budget : (acc+1)*2^bits.length≤M+1) :
    ∃T,Runs (storageBound Reg Arr M) (suffixLoop e r input) S (6*bits.length+1) T ∧
      T.Bounded M ∧ T.scalar (r 0)=w.length ∧ T.scalar (r 1)=w.length ∧
      T.scalar (r 2)=valueFold e acc bits ∧ T.scalar (r 3)=validFold e v bits ∧
      T.scalar (r 4)=0 ∧ T.scalar (r 7)=1 ∧ T.scalar (r 8)=2 ∧ T.array input=w.map bitNat := by
  induction bits generalizing S pos acc v with
  | nil =>
    have hp : pos=w.length := by
      have hh := congrArg List.length suffix
      simp only [List.length_drop,List.length_nil] at hh
      omega
    have hs : S.scalar (r 4)=0 := by simp [hp] at scan;exact scan
    refine ⟨S,?_,bounded,by omega,length,value,valid,hs,one,two,inputEq⟩
    exact .while_zero hs (Store.size_le_of_bounded bounded)
  | cons b bs ih =>
    obtain ⟨index,bit,tail⟩ := drop_cons_info suffix
    have hs : S.scalar (r 4)≠0 := by simp [index] at scan;omega
    have boundStep : valueStep e acc b+1≤2*(acc+1) := by
      cases e <;> cases b <;> simp [valueStep,bitNat] <;> omega
    have nextBudget : (valueStep e acc b+1)*2^bs.length≤M+1 := by
      calc
        _ ≤ (2*(acc+1))*2^bs.length := Nat.mul_le_mul_right _ boundStep
        _ = (acc+1)*2^(b::bs).length := by simp [pow_succ];ring
        _ ≤ M+1 := budget
    have next : valueStep e acc b≤M := by
      have hp : 1≤2^bs.length := one_le_pow₀ (by decide)
      nlinarith
    obtain ⟨U,first,hU,upos,ulen,uvalue,uvalid,uscan,uone,utwo,uinput⟩ :=
      bitStep_runs e r input S w pos acc v M b bounded room position length value valid smallValid
        one two inputEq index bit next
    have nextValid : validStep e v b≤1 := by cases e <;> cases b <;> simp [validStep,bitNat] <;> omega
    obtain ⟨T,last,hT,tpos,tlen,tvalue,tvalid,tscan,tone,ttwo,tinput⟩ :=
      ih U (pos+1) (valueStep e acc b) (validStep e v b) hU upos ulen uvalue uvalid nextValid
        uscan uone utwo uinput (by omega) tail nextBudget
    refine ⟨T,?_,hT,tpos,tlen,tvalue,tvalid,tscan,tone,ttwo,tinput⟩
    convert (show Runs (storageBound Reg Arr M) (.while (r 4) (bitStep e r input)) S
        (5+(6*bs.length+1)+1) T from .while_nonzero hs first last) using 1 <;> simp [suffixLoop] <;> omega
    /-simpa only [List.length_cons] using
      (show Runs (storageBound Reg Arr M) (.while (r 4) (bitStep e r input)) S
        (5+(6*bs.length+1)+1) T from .while_nonzero hs first last)-/

end GroupWL.MachinePrograms.DimensionParser
