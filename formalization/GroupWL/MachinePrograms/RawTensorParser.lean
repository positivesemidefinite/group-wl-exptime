import GroupWL.MachinePrograms.TensorParser

/-! Counted parsing of the full materialized tensor data, before the
separate alternating-form validation. -/
namespace GroupWL.MachinePrograms.NatArrayParser

open NatArrayLanguage
open NatArrayLowering (bitNat)

theorem readUnary_size {w tail : List Bool} {n : ℕ}
    (h : Statement.readUnary w=some (n,tail)) : n+1+tail.length=w.length := by
  rw [Statement.readUnary_sound h]
  simp [Statement.unary,List.length_append]
  omega

theorem readDimensions_size {w tail : List Bool} {n k : ℕ}
    (h : readDimensions w=some (n,k,tail)) : n+k+2+tail.length=w.length := by
  cases hfirst : Statement.readUnary w with
  | none => simp [readDimensions,hfirst] at h
  | some first =>
    rcases first with ⟨a,rest⟩
    cases hsecond : Statement.readUnary rest with
    | none => simp [readDimensions,hfirst,hsecond] at h
    | some second =>
      rcases second with ⟨b,last⟩
      simp only [readDimensions,hfirst,hsecond,Option.bind_eq_bind,Option.bind_some,
        Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl,rfl⟩
      have ha := readUnary_size hfirst
      have hb := readUnary_size hsecond
      omega

variable {Reg Arr : Type*} [DecidableEq Reg] [DecidableEq Arr]
  [Fintype Reg] [Fintype Arr]

def tensorData (r : Fin 13 ↪ Reg) (input output : Arr) (p : ℕ) :
    NatArrayLanguage.Program Reg Arr :=
  .seq (atoms [.binary .mul (r 9) (r 11) (r 11),.binary .mul (r 9) (r 9) (r 12)])
    (fieldsScan (tensorFieldRegs r) input output p)

def rawTensorScan (r : Fin 13 ↪ Reg) (input output : Arr) (p : ℕ) :
    NatArrayLanguage.Program Reg Arr :=
  .seq (tensorHeader r input) (.branch (r 3) (tensorData r input output p) .skip)

theorem rawTensorScan_correct (r : Fin 13 ↪ Reg) (input output : Arr) (p : ℕ)
    (hne : input≠output) (S : Store Reg Arr) (w : List Bool) (pos m : ℕ)
    (hb : S.Bounded m) (hroom : (w.length+1)^3≤m) (hp : p≤m)
    (hpos : S.scalar (r 0)=pos) (hle : pos≤w.length)
    (hlen : S.scalar (r 1)=w.length) (hvalid : S.scalar (r 3)=1)
    (hinput : S.array input=w.map bitNat) :
    ∃ T t, t≤(w.length+1)^3*(7*w.length+19)+14*w.length+34 ∧
      Runs (storageBound Reg Arr m) (rawTensorScan r input output p) S t T ∧
      T.Bounded m ∧ T.scalar (r 0)≤w.length ∧ T.scalar (r 3)≤1 ∧
      T.scalar (r 1)=w.length ∧ T.array input=w.map bitNat ∧
      match readRawTensor p (w.drop pos) with
      | none => T.scalar (r 3)=0
      | some (raw,tail) => T.scalar (r 3)=1 ∧ T.scalar (r 11)=raw.inputDimension ∧
          T.scalar (r 12)=raw.outputDimension ∧ T.array output=raw.coefficients ∧
          w.drop (T.scalar (r 0))=tail := by
  have hm : 1≤m := (one_le_pow₀ (by omega : 1≤w.length+1)).trans hroom
  obtain ⟨U,u,hu,first,hU,upos,uvalid,ulen,uinput,header⟩ :=
    tensorHeader_correct r input S w pos m hb hm hpos hle hlen hvalid hinput
  cases hd : readDimensions (w.drop pos) with
  | none =>
    have hz : U.scalar (r 3)=0 := by simpa [hd] using header
    refine ⟨U,u+1,by omega,.seq first (.branch_zero hz (.skip (Store.size_le_of_bounded hU))),
      hU,upos,uvalid,ulen,uinput,?_⟩
    simpa [readRawTensor,hd] using hz
  | some dims =>
    rcases dims with ⟨n,k,tail⟩
    have hh : U.scalar (r 3)=1 ∧ U.scalar (r 11)=n ∧ U.scalar (r 12)=k ∧
        w.drop (U.scalar (r 0))=tail := by simpa [hd] using header
    have hn : n≤w.length := by have h := readDimensions_size hd; simp only [List.length_drop] at h; omega
    have hk : k≤w.length := by have h := readDimensions_size hd; simp only [List.length_drop] at h; omega
    have hsquare : n*n≤m := by
      apply le_trans (b := (w.length+1)^3) _ hroom
      have hpow : (w.length+1)^2≤(w.length+1)^3 := pow_le_pow_right' (by omega) (by decide)
      nlinarith
    have hcube : n*n*k≤(w.length+1)^3 := by
      calc
        n*n*k ≤ (w.length+1)*(w.length+1)*(w.length+1) := by gcongr <;> omega
        _ = (w.length+1)^3 := by ring
    let as : List (Atom Reg Arr) := [.binary .mul (r 9) (r 11) (r 11),.binary .mul (r 9) (r 9) (r 12)]
    let V := applyAtoms as U
    have valid : ValidAtoms m as U := by
      simp [as,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
        Store.setScalar,r.injective.eq_iff,hh.2.1,hh.2.2.1,hsquare,hcube.trans hroom]
    obtain ⟨countRun,hV⟩ := atoms_runs hU as valid
    have vp : V.scalar (r 0)=U.scalar (r 0) := by
      simp [V,applyAtoms,as,Atom.apply,Store.setScalar,r.injective.eq_iff]
    have vl : V.scalar (r 1)=w.length := by
      simp [V,applyAtoms,as,Atom.apply,Store.setScalar,r.injective.eq_iff,ulen]
    have vv : V.scalar (r 3)=1 := by
      simp [V,applyAtoms,as,Atom.apply,Store.setScalar,r.injective.eq_iff,hh.1]
    have vc : V.scalar (r 9)=n*n*k := by
      simp [V,applyAtoms,as,Atom.apply,BinaryOp.eval,Store.setScalar,r.injective.eq_iff,hh.2.1,hh.2.2.1]
    have va : V.array input=w.map bitNat := by simpa [V,applyAtoms,as,Atom.apply] using uinput
    obtain ⟨T,t,ht,last,hT,tpos,tvalid,tguard,tlen,tone,tinput,spec⟩ :=
      fieldsScan_correct (tensorFieldRegs r) input output p hne V w (n*n*k) (U.scalar (r 0)) m
        hV hm hp vp upos vl vv va vc
    change T.scalar (r 0)≤w.length at tpos
    change T.scalar (r 3)≤1 at tvalid
    change T.scalar (r 1)=w.length at tlen
    have tn : T.scalar (r 11)=n := by
      rw [last.scalar_eq_of_not_mem (r 11)]
      · simp [V,applyAtoms,as,Atom.apply,Store.setScalar,r.injective.eq_iff,hh.2.1]
      · simp [fieldsScan,fieldsLoop,fieldElement,fieldScan,unaryScan,unaryStep,atoms,
          NatArrayLanguage.sequence,Program.scalarWrites,Atom.scalarWrites,parserRegs,tensorFieldRegs,
          Function.Embedding.trans_apply,r.injective.eq_iff]
    have tk : T.scalar (r 12)=k := by
      rw [last.scalar_eq_of_not_mem (r 12)]
      · simp [V,applyAtoms,as,Atom.apply,Store.setScalar,r.injective.eq_iff,hh.2.2.1]
      · simp [fieldsScan,fieldsLoop,fieldElement,fieldScan,unaryScan,unaryStep,atoms,
          NatArrayLanguage.sequence,Program.scalarWrites,Atom.scalarWrites,parserRegs,tensorFieldRegs,
          Function.Embedding.trans_apply,r.injective.eq_iff]
    refine ⟨T,u+(2+t+1),?_,.seq first (.branch_nonzero (by omega) (.seq countRun last)),
      hT,tpos,tvalid,tlen,tinput,?_⟩
    · nlinarith
    · rw [readRawTensor,hd]
      simp only [Option.bind_eq_bind,Option.bind_some]
      rw [hh.2.2.2] at spec
      cases hf : readNatFields p (n*n*k) tail with
      | none => simpa [hf] using spec
      | some value =>
        rcases value with ⟨entries,rest⟩
        simp only [hf] at spec
        simpa [hf,tn,tk] using spec

end GroupWL.MachinePrograms.NatArrayParser
