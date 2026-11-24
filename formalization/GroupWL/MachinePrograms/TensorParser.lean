import GroupWL.MachinePrograms.FieldArrayParser

/-! The concrete parser for dimensions and the materialized coefficient array. -/
namespace GroupWL.MachinePrograms.NatArrayParser

open NatArrayLanguage
open NatArrayLowering (bitNat)

def readDimensions (w : List Bool) : Option (ℕ × ℕ × List Bool) := do
  let (n,rest) ← Statement.readUnary w
  let (m,tail) ← Statement.readUnary rest
  pure (n,m,tail)

structure RawTensor where
  inputDimension : ℕ
  outputDimension : ℕ
  coefficients : List ℕ

def readRawTensor (p : ℕ) (w : List Bool) : Option (RawTensor × List Bool) := do
  let (n,m,rest) ← readDimensions w
  let (entries,tail) ← readNatFields p (n*n*m) rest
  pure (⟨n,m,entries⟩,tail)

variable {Reg Arr : Type*} [DecidableEq Reg] [DecidableEq Arr]
  [Fintype Reg] [Fintype Arr]

def tensorUnaryRegs (r : Fin 13 ↪ Reg) : Fin 8 ↪ Reg :=
  (Fin.castLEEmb (by decide)).trans r

def tensorFieldRegs (r : Fin 13 ↪ Reg) : Fin 11 ↪ Reg :=
  (Fin.castLEEmb (by decide)).trans r

def tensorHeader (r : Fin 13 ↪ Reg) (input : Arr) : NatArrayLanguage.Program Reg Arr :=
  .seq (unaryScan (tensorUnaryRegs r) input)
    (.branch (r 3)
      (.seq (.atom (.copy (r 11) (r 2)))
        (.seq (unaryScan (tensorUnaryRegs r) input) (.atom (.copy (r 12) (r 2))))) .skip)

theorem tensorHeader_correct (r : Fin 13 ↪ Reg) (input : Arr)
    (S : Store Reg Arr) (w : List Bool) (pos m : ℕ)
    (hb : S.Bounded m) (hroom : 1≤m)
    (hpos : S.scalar (r 0)=pos) (hle : pos≤w.length)
    (hlen : S.scalar (r 1)=w.length) (hvalid : S.scalar (r 3)=1)
    (hinput : S.array input=w.map bitNat) :
    ∃ T t, t≤14*w.length+25 ∧ Runs (storageBound Reg Arr m) (tensorHeader r input) S t T ∧
      T.Bounded m ∧ T.scalar (r 0)≤w.length ∧ T.scalar (r 3)≤1 ∧
      T.scalar (r 1)=w.length ∧ T.array input=w.map bitNat ∧
      match readDimensions (w.drop pos) with
      | none => T.scalar (r 3)=0
      | some (n,k,tail) => T.scalar (r 3)=1 ∧ T.scalar (r 11)=n ∧ T.scalar (r 12)=k ∧
          w.drop (T.scalar (r 0))=tail := by
  obtain ⟨U,u,hu,first,hU,upos,uvalid,uscan,ulen,uone,uinput,hparse⟩ :=
    unaryScan_correct (tensorUnaryRegs r) input S w pos m hb hroom hpos hle hlen hvalid hinput
  change U.scalar (r 0)≤w.length at upos
  change U.scalar (r 3)≤1 at uvalid
  change U.scalar (r 1)=w.length at ulen
  change Statement.readUnary (w.drop pos)=
    if U.scalar (r 3)=0 then none else some (U.scalar (r 2),w.drop (U.scalar (r 0))) at hparse
  by_cases hz : U.scalar (r 3)=0
  · refine ⟨U,u+1,by omega,.seq first (.branch_zero hz (.skip (Store.size_le_of_bounded hU))),
      hU,upos,uvalid,ulen,uinput,?_⟩
    simp [readDimensions,hparse,hz]
  · have hok : U.scalar (r 3)=1 := by omega
    let V := (Atom.copy (Arr := Arr) (r 11) (r 2)).apply U
    have copyN : Runs (storageBound Reg Arr m) (.atom (.copy (r 11) (r 2))) U 1 V :=
      atom_runs hU _ trivial trivial
    have hV : V.Bounded m := Atom.apply_bounded hU _ trivial
    have vp : V.scalar (r 0)=U.scalar (r 0) := by simp [V,Atom.apply,Store.setScalar,r.injective.eq_iff]
    have vl : V.scalar (r 1)=w.length := by simp [V,Atom.apply,Store.setScalar,r.injective.eq_iff,ulen]
    have vv : V.scalar (r 3)=1 := by simp [V,Atom.apply,Store.setScalar,r.injective.eq_iff,hok]
    have va : V.array input=w.map bitNat := uinput
    obtain ⟨W,v,hv,second,hW,wpos,wvalid,wscan,wlen,wone,winput,hparse'⟩ :=
      unaryScan_correct (tensorUnaryRegs r) input V w (U.scalar (r 0)) m hV hroom vp upos vl vv va
    change W.scalar (r 0)≤w.length at wpos
    change W.scalar (r 3)≤1 at wvalid
    change W.scalar (r 1)=w.length at wlen
    change Statement.readUnary (w.drop (U.scalar (r 0)))=
      if W.scalar (r 3)=0 then none else some (W.scalar (r 2),w.drop (W.scalar (r 0))) at hparse'
    have wn : W.scalar (r 11)=U.scalar (r 2) := by
      rw [second.scalar_eq_of_not_mem (r 11)]
      · simp [V,Atom.apply,Store.setScalar]
      · simp [unaryScan,unaryStep,atoms,NatArrayLanguage.sequence,Program.scalarWrites,
          Atom.scalarWrites,tensorUnaryRegs,Function.Embedding.trans_apply,r.injective.eq_iff]
    let T := (Atom.copy (Arr := Arr) (r 12) (r 2)).apply W
    have last : Runs (storageBound Reg Arr m) (.atom (.copy (r 12) (r 2))) W 1 T :=
      atom_runs hW _ trivial trivial
    have hT : T.Bounded m := Atom.apply_bounded hW _ trivial
    have tp : T.scalar (r 0)=W.scalar (r 0) := by simp [T,Atom.apply,Store.setScalar,r.injective.eq_iff]
    have tv : T.scalar (r 3)=W.scalar (r 3) := by simp [T,Atom.apply,Store.setScalar,r.injective.eq_iff]
    have tn : T.scalar (r 11)=U.scalar (r 2) := by simp [T,Atom.apply,Store.setScalar,r.injective.eq_iff,wn]
    have tm : T.scalar (r 12)=W.scalar (r 2) := by simp [T,Atom.apply,Store.setScalar]
    refine ⟨T,u+(1+(v+1)+1),by omega,.seq first (.branch_nonzero hz (.seq copyN (.seq second last))),
      hT,by omega,by omega,?_,winput,?_⟩
    · simp [T,Atom.apply,Store.setScalar,r.injective.eq_iff,wlen]
    · simp only [readDimensions,hparse,if_neg hz,Option.bind_eq_bind,Option.bind_some]
      rw [hparse']
      by_cases hwz : W.scalar (r 3)=0
      · simpa [hwz,tv]
      · have hwok : W.scalar (r 3)=1 := by omega
        simp [hwz,hwok,tp,tv,tn,tm]

end GroupWL.MachinePrograms.NatArrayParser
