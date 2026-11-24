import GroupWL.MachinePrograms.CoefficientParser

/-! Correctness and counted execution of the coefficient parsing loop. -/
namespace GroupWL.MachinePrograms.NatArrayParser

open NatArrayLanguage
open NatArrayLowering (bitNat)

variable {Reg Arr : Type*} [DecidableEq Reg] [DecidableEq Arr]
  [Fintype Reg] [Fintype Arr]

theorem fieldsLoop_correct (r : Fin 11 ↪ Reg) (input output : Arr) (p : ℕ)
    (hne : input≠output) (n : ℕ) (S : Store Reg Arr) (w : List Bool) (pre : List ℕ)
    (pos m : ℕ) (hb : S.Bounded m) (hroom : 1≤m) (hp : p≤m)
    (hpos : S.scalar (r 0)=pos) (hle : pos≤w.length)
    (hlen : S.scalar (r 1)=w.length) (hvalid : S.scalar (r 3)=1)
    (hone : S.scalar (r 7)=1) (hinput : S.array input=w.map bitNat)
    (houtput : S.array output=pre++List.replicate n 0)
    (hindex : S.scalar (r 8)=pre.length) (hcount : S.scalar (r 9)=n)
    (hguard : S.scalar (r 10)=n) :
    ∃ T t, t≤n*(7*w.length+19)+1 ∧
      Runs (storageBound Reg Arr m) (fieldsLoop r input output p) S t T ∧
      T.Bounded m ∧ T.scalar (r 0)≤w.length ∧ T.scalar (r 3)≤1 ∧ T.scalar (r 10)=0 ∧
      T.scalar (r 1)=w.length ∧ T.scalar (r 7)=1 ∧ T.array input=w.map bitNat ∧
      match readNatFields p n (w.drop pos) with
      | none => T.scalar (r 3)=0
      | some (values,tail) => T.scalar (r 3)=1 ∧ T.array output=pre++values ∧
          w.drop (T.scalar (r 0))=tail := by
  induction n generalizing S pre pos with
  | zero =>
    refine ⟨S,1,by simp,.while_zero hguard (Store.size_le_of_bounded hb),hb,
      by omega,by omega,hguard,hlen,hone,hinput,?_⟩
    exact ⟨hvalid,by simpa using houtput,by rw [hpos]⟩
  | succ n ih =>
    obtain ⟨U,u,hu,first,hU,upos,uvalid,ulen,uone,uinput,uoutput,uindex,ucount,uguard,hparse⟩ :=
      fieldElement_correct r input output p hne S w pre n pos m hb hroom hp
        hpos hle hlen hvalid hinput houtput hindex hcount
    by_cases hz : U.scalar (r 3)=0
    · have hg : U.scalar (r 10)=0 := by rw [uguard,hz]; simp
      refine ⟨U,u+2,?_,?_,hU,upos,uvalid,hg,ulen,uone,uinput,?_⟩
      · nlinarith
      · convert Runs.while_nonzero (by omega : S.scalar (r 10)≠0) first
          (Runs.while_zero hg (Store.size_le_of_bounded hU)) using 1 <;> omega
      · simp [readNatFields,hparse,hz]
    · have hok : U.scalar (r 3)=1 := by omega
      obtain ⟨T,t,ht,last,hT,tpos,tvalid,tguard,tlen,tone,tinput,spec⟩ :=
        ih U (pre++[U.scalar (r 2)]) (U.scalar (r 0)) hU rfl upos ulen hok uone uinput
          (by simpa [List.append_assoc] using uoutput)
          (by simpa using uindex) ucount (by simpa [hok] using uguard)
      refine ⟨T,u+t+1,by nlinarith,?_,hT,tpos,tvalid,tguard,tlen,tone,tinput,?_⟩
      · exact .while_nonzero (by omega) first last
      · rw [readNatFields,hparse,if_neg hz]
        simp only [Option.bind_eq_bind,Option.bind_some]
        cases hh : readNatFields p n (w.drop (U.scalar (r 0))) with
        | none => simpa [hh] using spec
        | some value =>
          rcases value with ⟨values,tail⟩
          simp only [hh] at spec
          simpa [hh,List.append_assoc] using spec

def fieldsScan (r : Fin 11 ↪ Reg) (input output : Arr) (p : ℕ) :
    NatArrayLanguage.Program Reg Arr :=
  .seq (atoms [.const (r 2) 0,.allocate output (r 9) (r 2),.const (r 8) 0,
    .const (r 7) 1,.copy (r 10) (r 9)]) (fieldsLoop r input output p)

theorem fieldsScan_correct (r : Fin 11 ↪ Reg) (input output : Arr) (p : ℕ)
    (hne : input≠output) (S : Store Reg Arr) (w : List Bool) (n pos m : ℕ)
    (hb : S.Bounded m) (hroom : 1≤m) (hp : p≤m)
    (hpos : S.scalar (r 0)=pos) (hle : pos≤w.length)
    (hlen : S.scalar (r 1)=w.length) (hvalid : S.scalar (r 3)=1)
    (hinput : S.array input=w.map bitNat) (hcount : S.scalar (r 9)=n) :
    ∃ T t, t≤n*(7*w.length+19)+6 ∧
      Runs (storageBound Reg Arr m) (fieldsScan r input output p) S t T ∧
      T.Bounded m ∧ T.scalar (r 0)≤w.length ∧ T.scalar (r 3)≤1 ∧ T.scalar (r 10)=0 ∧
      T.scalar (r 1)=w.length ∧ T.scalar (r 7)=1 ∧ T.array input=w.map bitNat ∧
      match readNatFields p n (w.drop pos) with
      | none => T.scalar (r 3)=0
      | some (values,tail) => T.scalar (r 3)=1 ∧ T.array output=values ∧
          w.drop (T.scalar (r 0))=tail := by
  let as : List (Atom Reg Arr) := [.const (r 2) 0,.allocate output (r 9) (r 2),.const (r 8) 0,
    .const (r 7) 1,.copy (r 10) (r 9)]
  let U := applyAtoms as S
  obtain ⟨first,hU⟩ := atoms_runs hb as
    (by simp [as,ValidAtoms,Atom.Valid,Atom.SmallResult,hroom])
  have upos : U.scalar (r 0)=pos := by
    simp [U,applyAtoms,as,Atom.apply,Store.setScalar,Store.setArray,r.injective.eq_iff,hpos]
  have ulen : U.scalar (r 1)=w.length := by
    simp [U,applyAtoms,as,Atom.apply,Store.setScalar,Store.setArray,r.injective.eq_iff,hlen]
  have uvalid : U.scalar (r 3)=1 := by
    simp [U,applyAtoms,as,Atom.apply,Store.setScalar,Store.setArray,r.injective.eq_iff,hvalid]
  have uone : U.scalar (r 7)=1 := by
    simp [U,applyAtoms,as,Atom.apply,Store.setScalar,Store.setArray,r.injective.eq_iff]
  have uinput : U.array input=w.map bitNat := by
    simp [U,applyAtoms,as,Atom.apply,Store.setArray,hne,hinput]
  have uoutput : U.array output=[]++List.replicate n 0 := by
    simp [U,applyAtoms,as,Atom.apply,Store.setScalar,Store.setArray,r.injective.eq_iff,hcount]
  have uindex : U.scalar (r 8)=0 := by
    simp [U,applyAtoms,as,Atom.apply,Store.setScalar,Store.setArray,r.injective.eq_iff]
  have ucount : U.scalar (r 9)=n := by
    simp [U,applyAtoms,as,Atom.apply,Store.setScalar,Store.setArray,r.injective.eq_iff,hcount]
  have uguard : U.scalar (r 10)=n := by
    simp [U,applyAtoms,as,Atom.apply,Store.setScalar,Store.setArray,r.injective.eq_iff,hcount]
  obtain ⟨T,t,ht,last,hT,tpos,tvalid,tguard,tlen,tone,tinput,spec⟩ :=
    fieldsLoop_correct r input output p hne n U w [] pos m hU hroom hp
      upos hle ulen uvalid uone uinput uoutput uindex ucount uguard
  refine ⟨T,5+t,by omega,.seq first last,hT,tpos,tvalid,tguard,tlen,tone,tinput,?_⟩
  simpa using spec

end GroupWL.MachinePrograms.NatArrayParser
