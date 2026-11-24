import GroupWL.MachinePrograms.FieldParser
import Mathlib.Data.Fin.Embedding

/-! Materializing a fixed number of parsed field entries in an actual array. -/
namespace GroupWL.MachinePrograms.NatArrayParser

open NatArrayLanguage
open NatArrayLowering (bitNat)

def readNatFields (p : ℕ) : ℕ → List Bool → Option (List ℕ × List Bool)
  | 0,w => some ([],w)
  | n+1,w => do
    let (a,tail) ← readNatField p w
    let (as,rest) ← readNatFields p n tail
    pure (a::as,rest)

variable {Reg Arr : Type*} [DecidableEq Reg] [DecidableEq Arr]
  [Fintype Reg] [Fintype Arr]

def parserRegs (r : Fin 11 ↪ Reg) : Fin 8 ↪ Reg := (Fin.castLEEmb (by decide)).trans r

/-- Additional registers: 8 is the array index, 9 is the remaining count,
10 is the loop guard, the product of the count and the validity flag. -/
def fieldElement (r : Fin 11 ↪ Reg) (input output : Arr) (p : ℕ) :
    NatArrayLanguage.Program Reg Arr :=
  .seq (fieldScan (parserRegs r) input p) (atoms [
    .write output (r 8) (r 2),.binary .add (r 8) (r 8) (r 7),
    .binary .sub (r 9) (r 9) (r 7),.binary .mul (r 10) (r 9) (r 3)])

def fieldsLoop (r : Fin 11 ↪ Reg) (input output : Arr) (p : ℕ) :
    NatArrayLanguage.Program Reg Arr := .while (r 10) (fieldElement r input output p)

theorem fieldElement_correct (r : Fin 11 ↪ Reg) (input output : Arr) (p : ℕ)
    (hne : input≠output) (S : Store Reg Arr) (w : List Bool) (pre : List ℕ)
    (n pos m : ℕ) (hb : S.Bounded m) (hroom : 1≤m) (hp : p≤m)
    (hpos : S.scalar (r 0)=pos) (hle : pos≤w.length)
    (hlen : S.scalar (r 1)=w.length) (hvalid : S.scalar (r 3)=1)
    (hinput : S.array input=w.map bitNat)
    (houtput : S.array output=pre++List.replicate (n+1) 0)
    (hindex : S.scalar (r 8)=pre.length) (hcount : S.scalar (r 9)=n+1) :
    ∃ T t, t≤7*w.length+18 ∧ Runs (storageBound Reg Arr m) (fieldElement r input output p) S t T ∧
      T.Bounded m ∧ T.scalar (r 0)≤w.length ∧ T.scalar (r 3)≤1 ∧
      T.scalar (r 1)=w.length ∧ T.scalar (r 7)=1 ∧ T.array input=w.map bitNat ∧
      T.array output=pre++T.scalar (r 2)::List.replicate n 0 ∧
      T.scalar (r 8)=pre.length+1 ∧ T.scalar (r 9)=n ∧ T.scalar (r 10)=n*T.scalar (r 3) ∧
      readNatField p (w.drop pos) =
        if T.scalar (r 3)=0 then none else some (T.scalar (r 2),w.drop (T.scalar (r 0))) := by
  obtain ⟨U,u,hu,hr,hU,upos,uvalid,uscan,ulen,uone,uinput,hparse⟩ :=
    fieldScan_correct (parserRegs r) input p S w pos m hb hroom hp hpos hle hlen hvalid hinput
  have hUoutput : U.array output=pre++List.replicate (n+1) 0 :=
    (fieldScan_array_frame hr output).trans houtput
  have hUindex : U.scalar (r 8)=pre.length := by
    rw [hr.scalar_eq_of_not_mem (r 8)]
    · exact hindex
    · simp [fieldScan,unaryScan,unaryStep,atoms,NatArrayLanguage.sequence,
        Program.scalarWrites,Atom.scalarWrites,parserRegs,Function.Embedding.trans_apply,r.injective.eq_iff]
  have hUcount : U.scalar (r 9)=n+1 := by
    rw [hr.scalar_eq_of_not_mem (r 9)]
    · exact hcount
    · simp [fieldScan,unaryScan,unaryStep,atoms,NatArrayLanguage.sequence,
        Program.scalarWrites,Atom.scalarWrites,parserRegs,Function.Embedding.trans_apply,r.injective.eq_iff]
  change U.scalar (r 0)≤w.length at upos
  change U.scalar (r 3)≤1 at uvalid
  change U.scalar (r 1)=w.length at ulen
  change U.scalar (r 7)=1 at uone
  change readNatField p (w.drop pos)=
    if U.scalar (r 3)=0 then none else some (U.scalar (r 2),w.drop (U.scalar (r 0))) at hparse
  let as : List (Atom Reg Arr) := [
    .write output (r 8) (r 2),.binary .add (r 8) (r 8) (r 7),
    .binary .sub (r 9) (r 9) (r 7),.binary .mul (r 10) (r 9) (r 3)]
  have hsize : pre.length+(n+1)≤m := by
    simpa [hUoutput] using hU.2.1 output
  have hv : ValidAtoms m as U := by
    have hu0 : U.scalar (r 3)=0 ∨ U.scalar (r 3)=1 := by omega
    rcases hu0 with hu0 | hu0 <;>
      simp [as,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
        Store.setScalar,Store.setArray,Function.update_apply,r.injective.eq_iff,
        hUoutput,hUindex,hUcount,uone,hu0] <;> omega
  obtain ⟨last,hT⟩ := atoms_runs hU as hv
  let T := applyAtoms as U
  have tpos : T.scalar (r 0)=U.scalar (r 0) := by
    simp [T,applyAtoms,as,Atom.apply,Store.setScalar,Store.setArray,r.injective.eq_iff]
  have tvalue : T.scalar (r 2)=U.scalar (r 2) := by
    simp [T,applyAtoms,as,Atom.apply,Store.setScalar,Store.setArray,r.injective.eq_iff]
  have tvalid : T.scalar (r 3)=U.scalar (r 3) := by
    simp [T,applyAtoms,as,Atom.apply,Store.setScalar,Store.setArray,r.injective.eq_iff]
  refine ⟨T,u+4,by omega,.seq hr last,hT,by omega,by omega,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [T,applyAtoms,as,Atom.apply,Store.setScalar,Store.setArray,r.injective.eq_iff,ulen]
  · simp [T,applyAtoms,as,Atom.apply,Store.setScalar,Store.setArray,r.injective.eq_iff,uone]
  · simp [T,applyAtoms,as,Atom.apply,Store.setArray,hne,uinput]
  · simp [T,applyAtoms,as,Atom.apply,Store.setScalar,Store.setArray,
      r.injective.eq_iff,hUoutput,hUindex,List.replicate_succ]
  · simp [T,applyAtoms,as,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,
      r.injective.eq_iff,hUindex,uone]
  · simp [T,applyAtoms,as,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,
      r.injective.eq_iff,hUcount,uone]
  · simp [T,applyAtoms,as,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,
      r.injective.eq_iff,hUcount,uone]
  · simpa only [tpos,tvalue,tvalid] using hparse

end GroupWL.MachinePrograms.NatArrayParser
