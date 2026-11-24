import GroupWL.MachinePrograms.NatArrayFrames
import GroupWL.MachinePrograms.NatArrayCountedLoops
import GroupWL.MachinePrograms.NatArrayIO
import GroupWL.DenseParsing

/-! Fixed-register scans of the raw dense bit encoding. Input bits are
materialized as natural entries 0 and 1; every access is bounds checked. -/
namespace GroupWL.MachinePrograms.NatArrayParser

open NatArrayLanguage
open NatArrayLowering (bitNat)

variable {Reg Arr : Type*} [DecidableEq Reg] [DecidableEq Arr]
  [Fintype Reg] [Fintype Arr]

/-- Register order: position, length, value, valid, scanning, bit, flag, one. -/
def unaryStep (r : Fin 8 ↪ Reg) (input : Arr) : NatArrayLanguage.Program Reg Arr :=
  .seq (.atom (.binary .lt (r 6) (r 0) (r 1)))
    (.branch (r 6)
      (.seq (atoms [.read (r 5) input (r 0), .binary .add (r 0) (r 0) (r 7)])
        (.branch (r 5) (.atom (.binary .add (r 2) (r 2) (r 7)))
          (.atom (.const (r 4) 0))))
      (atoms [.const (r 3) 0,.const (r 4) 0]))

def unaryScan (r : Fin 8 ↪ Reg) (input : Arr) : NatArrayLanguage.Program Reg Arr :=
  .seq (atoms [.const (r 2) 0,.const (r 4) 1,.const (r 7) 1])
    (.while (r 4) (unaryStep r input))

theorem unaryStep_bit (r : Fin 8 ↪ Reg) (input : Arr)
    (S : Store Reg Arr) (w : List Bool) (pos acc m : ℕ) (b : Bool)
    (hb : S.Bounded m) (hroom : 1 ≤ m) (hpos : S.scalar (r 0)=pos)
    (hlen : S.scalar (r 1)=w.length) (hvalue : S.scalar (r 2)=acc)
    (hvalid : S.scalar (r 3)=1) (hscan : S.scalar (r 4)=1)
    (hone : S.scalar (r 7)=1) (hinput : S.array input=w.map bitNat)
    (hindex : pos<w.length) (hbit : w[pos]=b)
    (hnext : acc+bitNat b ≤ m) :
    ∃ T, Runs (storageBound Reg Arr m) (unaryStep r input) S 6 T ∧
      T.Bounded m ∧ T.scalar (r 0)=pos+1 ∧ T.scalar (r 2)=acc+bitNat b ∧
      T.scalar (r 3)=1 ∧ T.scalar (r 4)=bitNat b ∧ T.scalar (r 1)=w.length ∧
      T.scalar (r 7)=1 ∧ T.array input=w.map bitNat := by
  have hn : w.length≤m := by simpa [hlen] using hb.1 (r 1)
  have hget : (w.map bitNat)[pos]?.getD 0=bitNat b := by
    simp [List.getElem?_eq_getElem hindex,hbit]
  let C := (Atom.binary BinaryOp.lt (r 6) (r 0) (r 1)).apply S
  have hc : (Atom.binary BinaryOp.lt (r 6) (r 0) (r 1)).SmallResult m S := by
    simp [Atom.SmallResult,BinaryOp.eval,hpos,hlen,hindex,hroom]
  have runC : Runs (storageBound Reg Arr m)
      (.atom (.binary .lt (r 6) (r 0) (r 1))) S 1 C := atom_runs hb _ trivial hc
  have boundC : C.Bounded m := Atom.apply_bounded hb _ hc
  have flagC : C.scalar (r 6)≠0 := by simp [C,Atom.apply,BinaryOp.eval,hpos,hlen,hindex]
  let T := applyAtoms [.read (r 5) input (r 0),.binary .add (r 0) (r 0) (r 7)] C
  have hv : ValidAtoms m [.read (r 5) input (r 0),.binary .add (r 0) (r 0) (r 7)] C := by
    simp [ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,C,
      Store.setScalar,Function.update_apply,r.injective.eq_iff,hpos,hlen,hinput,hone,hindex]
    omega
  obtain ⟨runT,boundT⟩ := atoms_runs boundC _ hv
  have valT : T.scalar (r 2)=acc := by
    simp [T,applyAtoms,C,Atom.apply,Store.setScalar,Function.update_apply,r.injective.eq_iff,hvalue]
  have oneT : T.scalar (r 7)=1 := by
    simp [T,applyAtoms,C,Atom.apply,Store.setScalar,Function.update_apply,r.injective.eq_iff,hone]
  have bitT : T.scalar (r 5)=bitNat b := by
    simp [T,applyAtoms,C,Atom.apply,Store.setScalar,Function.update_apply,r.injective.eq_iff,
      hpos,hinput,List.getElem?_eq_getElem hindex,hbit]
  cases b with
  | false =>
    let U := (Atom.const (Arr := Arr) (r 4) 0).apply T
    have last : Runs (storageBound Reg Arr m) (.atom (.const (r 4) 0)) T 1 U :=
      atom_runs boundT _ trivial (by simp [Atom.SmallResult])
    refine ⟨U,?_,Atom.apply_bounded boundT _ (by simp [Atom.SmallResult]),?_⟩
    · exact .seq runC (.branch_nonzero flagC (.seq runT (.branch_zero (by simpa [bitNat] using bitT) last)))
    · simp [U,T,applyAtoms,C,Atom.apply,BinaryOp.eval,Store.setScalar,Function.update_apply,
        r.injective.eq_iff,hpos,hvalue,hvalid,hscan,hlen,hone,hinput,bitNat]
  | true =>
    let U := (Atom.binary BinaryOp.add (r 2) (r 2) (r 7)).apply T
    have small : (Atom.binary BinaryOp.add (r 2) (r 2) (r 7)).SmallResult m T := by
      simpa [Atom.SmallResult,BinaryOp.eval,valT,oneT,bitNat] using hnext
    have last : Runs (storageBound Reg Arr m) (.atom (.binary .add (r 2) (r 2) (r 7))) T 1 U :=
      atom_runs boundT _ trivial small
    refine ⟨U,?_,Atom.apply_bounded boundT _ small,?_⟩
    · exact .seq runC (.branch_nonzero flagC (.seq runT (.branch_nonzero (by change T.scalar (r 5) ≠ 0; rw [bitT]; decide) last)))
    · simp [U,T,applyAtoms,C,Atom.apply,BinaryOp.eval,Store.setScalar,Function.update_apply,
        r.injective.eq_iff,hpos,hvalue,hvalid,hscan,hlen,hone,hinput,bitNat]

theorem unaryStep_end (r : Fin 8 ↪ Reg) (input : Arr)
    (S : Store Reg Arr) (w : List Bool) (acc m : ℕ)
    (hb : S.Bounded m) (hpos : S.scalar (r 0)=w.length)
    (hlen : S.scalar (r 1)=w.length) (hvalue : S.scalar (r 2)=acc)
    (hone : S.scalar (r 7)=1) (hinput : S.array input=w.map bitNat) :
    ∃ T, Runs (storageBound Reg Arr m) (unaryStep r input) S 4 T ∧
      T.Bounded m ∧ T.scalar (r 0)=w.length ∧ T.scalar (r 2)=acc ∧
      T.scalar (r 3)=0 ∧ T.scalar (r 4)=0 ∧ T.scalar (r 1)=w.length ∧
      T.scalar (r 7)=1 ∧ T.array input=w.map bitNat := by
  let C := (Atom.binary BinaryOp.lt (r 6) (r 0) (r 1)).apply S
  have small : (Atom.binary BinaryOp.lt (r 6) (r 0) (r 1)).SmallResult m S := by
    simp [Atom.SmallResult,BinaryOp.eval,hpos,hlen]
  have first : Runs (storageBound Reg Arr m)
      (.atom (.binary .lt (r 6) (r 0) (r 1))) S 1 C := atom_runs hb _ trivial small
  have hc : C.Bounded m := Atom.apply_bounded hb _ small
  obtain ⟨last,ht⟩ := atoms_runs hc [.const (r 3) 0,.const (r 4) 0]
    (by simp [ValidAtoms,Atom.Valid,Atom.SmallResult])
  refine ⟨_,.seq first (.branch_zero ?_ last),ht,?_⟩
  · simp [C,Atom.apply,BinaryOp.eval,hpos,hlen]
  · simp [applyAtoms,C,Atom.apply,Store.setScalar,Function.update_apply,
      r.injective.eq_iff,hpos,hvalue,hlen,hone,hinput]

private theorem drop_cons_info {w : List Bool} {pos : ℕ} {b : Bool} {tail : List Bool}
    (h : w.drop pos=b::tail) :
    ∃ hpos : pos<w.length, w[pos]=b ∧ w.drop (pos+1)=tail := by
  have hpos : pos<w.length := by
    have hh := congrArg List.length h
    simp only [List.length_drop,List.length_cons] at hh
    omega
  refine ⟨hpos,?_,?_⟩
  · have hh := congrArg (fun xs : List Bool => xs[0]?) h
    simpa [List.getElem?_eq_getElem hpos] using hh
  · have hh := congrArg List.tail h
    simpa only [List.tail_drop,List.tail_cons] using hh

theorem unaryLoop_success (r : Fin 8 ↪ Reg) (input : Arr)
    (n : ℕ) (S : Store Reg Arr) (w tail : List Bool) (pos acc m : ℕ)
    (hb : S.Bounded m) (hroom : 1≤m) (hpos : S.scalar (r 0)=pos)
    (hlen : S.scalar (r 1)=w.length) (hvalue : S.scalar (r 2)=acc)
    (hvalid : S.scalar (r 3)=1) (hscan : S.scalar (r 4)=1)
    (hone : S.scalar (r 7)=1) (hinput : S.array input=w.map bitNat)
    (hword : w.drop pos=List.replicate n true ++ false::tail) (hnext : acc+n≤m) :
    ∃ T, Runs (storageBound Reg Arr m) (.while (r 4) (unaryStep r input)) S (7*n+8) T ∧
      T.Bounded m ∧ T.scalar (r 0)=pos+n+1 ∧ T.scalar (r 2)=acc+n ∧
      T.scalar (r 3)=1 ∧ T.scalar (r 4)=0 ∧ T.scalar (r 1)=w.length ∧
      T.scalar (r 7)=1 ∧ T.array input=w.map bitNat := by
  induction n generalizing S pos acc with
  | zero =>
    have hw : w.drop pos=false::tail := by simpa using hword
    obtain ⟨hi,hbit,htail⟩ := drop_cons_info hw
    obtain ⟨T,hr,hT,hp,hv,hok,hs,hl,ho,ha⟩ := unaryStep_bit r input S w pos acc m false
      hb hroom hpos hlen hvalue hvalid hscan hone hinput hi hbit (by simpa [bitNat] using hnext)
    refine ⟨T,?_,hT,?_,?_,hok,?_,hl,ho,ha⟩
    · exact .while_nonzero (by omega) hr (.while_zero (by simpa [bitNat] using hs) (Store.size_le_of_bounded hT))
    · simpa using hp
    · simpa [bitNat] using hv
    · simpa [bitNat] using hs
  | succ n ih =>
    have hw : w.drop pos=true::(List.replicate n true ++ false::tail) := by
      simpa only [List.replicate_succ,List.cons_append] using hword
    obtain ⟨hi,hbit,htail⟩ := drop_cons_info hw
    obtain ⟨T,hr,hT,hp,hv,hok,hs,hl,ho,ha⟩ := unaryStep_bit r input S w pos acc m true
      hb hroom hpos hlen hvalue hvalid hscan hone hinput hi hbit (by simp [bitNat]; omega)
    obtain ⟨U,hu,hU,up,uv,uok,us,ul,uo,ua⟩ := ih T (pos+1) (acc+1) hT hp hl
      (by simpa [bitNat] using hv) hok (by simpa [bitNat] using hs) ho ha htail (by omega)
    refine ⟨U,?_,hU,?_,?_,uok,us,ul,uo,ua⟩
    · convert Runs.while_nonzero (by omega : S.scalar (r 4)≠0) hr hu using 1 <;> omega
    · omega
    · omega

theorem unaryLoop_failure (r : Fin 8 ↪ Reg) (input : Arr)
    (n : ℕ) (S : Store Reg Arr) (w : List Bool) (pos acc m : ℕ)
    (hb : S.Bounded m) (hroom : 1≤m) (hpos : S.scalar (r 0)=pos)
    (hle : pos≤w.length) (hlen : S.scalar (r 1)=w.length) (hvalue : S.scalar (r 2)=acc)
    (hvalid : S.scalar (r 3)=1) (hscan : S.scalar (r 4)=1)
    (hone : S.scalar (r 7)=1) (hinput : S.array input=w.map bitNat)
    (hword : w.drop pos=List.replicate n true) (hnext : acc+n≤m) :
    ∃ T, Runs (storageBound Reg Arr m) (.while (r 4) (unaryStep r input)) S (7*n+6) T ∧
      T.Bounded m ∧ T.scalar (r 0)=w.length ∧ T.scalar (r 2)=acc+n ∧
      T.scalar (r 3)=0 ∧ T.scalar (r 4)=0 ∧ T.scalar (r 1)=w.length ∧
      T.scalar (r 7)=1 ∧ T.array input=w.map bitNat := by
  induction n generalizing S pos acc with
  | zero =>
    have he : pos=w.length := by
      have hh := congrArg List.length hword
      simp only [List.length_drop,List.length_replicate] at hh
      omega
    obtain ⟨T,hr,hT,hp,hv,hok,hs,hl,ho,ha⟩ := unaryStep_end r input S w acc m
      hb (by omega) hlen hvalue hone hinput
    refine ⟨T,?_,hT,hp,?_,hok,hs,hl,ho,ha⟩
    · exact .while_nonzero (by omega) hr (.while_zero hs (Store.size_le_of_bounded hT))
    · simpa using hv
  | succ n ih =>
    have hw : w.drop pos=true::List.replicate n true := by
      simpa only [List.replicate_succ] using hword
    obtain ⟨hi,hbit,htail⟩ := drop_cons_info hw
    obtain ⟨T,hr,hT,hp,hv,hok,hs,hl,ho,ha⟩ := unaryStep_bit r input S w pos acc m true
      hb hroom hpos hlen hvalue hvalid hscan hone hinput hi hbit (by simp [bitNat]; omega)
    obtain ⟨U,hu,hU,up,uv,uok,us,ul,uo,ua⟩ := ih T (pos+1) (acc+1) hT hp (by omega) hl
      (by simpa [bitNat] using hv) hok (by simpa [bitNat] using hs) ho ha htail (by omega)
    refine ⟨U,?_,hU,up,?_,uok,us,ul,uo,ua⟩
    · convert Runs.while_nonzero (by omega : S.scalar (r 4)≠0) hr hu using 1 <;> omega
    · omega

theorem unaryScan_success (r : Fin 8 ↪ Reg) (input : Arr)
    (S : Store Reg Arr) (w tail : List Bool) (pos n m : ℕ)
    (hb : S.Bounded m) (hroom : 1≤m) (hpos : S.scalar (r 0)=pos)
    (hlen : S.scalar (r 1)=w.length) (hvalid : S.scalar (r 3)=1)
    (hinput : S.array input=w.map bitNat)
    (hword : w.drop pos=List.replicate n true ++ false::tail) :
    ∃ T, Runs (storageBound Reg Arr m) (unaryScan r input) S (7*n+11) T ∧
      T.Bounded m ∧ T.scalar (r 0)=pos+n+1 ∧ T.scalar (r 2)=n ∧
      T.scalar (r 3)=1 ∧ T.scalar (r 4)=0 ∧ T.scalar (r 1)=w.length ∧
      T.scalar (r 7)=1 ∧ T.array input=w.map bitNat := by
  let T := applyAtoms [.const (r 2) 0,.const (r 4) 1,.const (r 7) 1] S
  obtain ⟨first,hT⟩ := atoms_runs hb [.const (r 2) 0,.const (r 4) 1,.const (r 7) 1]
    (by simp [ValidAtoms,Atom.Valid,Atom.SmallResult,hroom])
  have hn : n≤m := by
    have hh := congrArg List.length hword
    have hm : w.length≤m := by simpa [hlen] using hb.1 (r 1)
    simp only [List.length_drop,List.length_append,List.length_replicate,List.length_cons] at hh
    omega
  obtain ⟨U,last,hU,up,uv,uok,us,ul,uo,ua⟩ := unaryLoop_success r input n T w tail pos 0 m hT hroom
    (by simp [T,applyAtoms,Atom.apply,Store.setScalar,Function.update_apply,r.injective.eq_iff,hpos])
    (by simp [T,applyAtoms,Atom.apply,Store.setScalar,Function.update_apply,r.injective.eq_iff,hlen])
    (by simp [T,applyAtoms,Atom.apply,Store.setScalar,Function.update_apply,r.injective.eq_iff])
    (by simp [T,applyAtoms,Atom.apply,Store.setScalar,Function.update_apply,r.injective.eq_iff,hvalid])
    (by simp [T,applyAtoms,Atom.apply,Store.setScalar,Function.update_apply,r.injective.eq_iff])
    (by simp [T,applyAtoms,Atom.apply,Store.setScalar,Function.update_apply,r.injective.eq_iff])
    (by simp [T,applyAtoms,Atom.apply,hinput]) hword (by simpa using hn)
  refine ⟨U,?_,hU,up,by simpa using uv,uok,us,ul,uo,ua⟩
  convert Runs.seq first last using 1 <;> simp <;> omega

theorem unaryScan_failure (r : Fin 8 ↪ Reg) (input : Arr)
    (S : Store Reg Arr) (w : List Bool) (pos n m : ℕ)
    (hb : S.Bounded m) (hroom : 1≤m) (hpos : S.scalar (r 0)=pos) (hle : pos≤w.length)
    (hlen : S.scalar (r 1)=w.length) (hvalid : S.scalar (r 3)=1)
    (hinput : S.array input=w.map bitNat) (hword : w.drop pos=List.replicate n true) :
    ∃ T, Runs (storageBound Reg Arr m) (unaryScan r input) S (7*n+9) T ∧
      T.Bounded m ∧ T.scalar (r 0)=w.length ∧ T.scalar (r 2)=n ∧
      T.scalar (r 3)=0 ∧ T.scalar (r 4)=0 ∧ T.scalar (r 1)=w.length ∧
      T.scalar (r 7)=1 ∧ T.array input=w.map bitNat := by
  let T := applyAtoms [.const (r 2) 0,.const (r 4) 1,.const (r 7) 1] S
  obtain ⟨first,hT⟩ := atoms_runs hb [.const (r 2) 0,.const (r 4) 1,.const (r 7) 1]
    (by simp [ValidAtoms,Atom.Valid,Atom.SmallResult,hroom])
  have hn : n≤m := by
    have hh := congrArg List.length hword
    have hm : w.length≤m := by simpa [hlen] using hb.1 (r 1)
    simp only [List.length_drop,List.length_replicate] at hh
    omega
  obtain ⟨U,last,hU,up,uv,uok,us,ul,uo,ua⟩ := unaryLoop_failure r input n T w pos 0 m hT hroom
    (by simp [T,applyAtoms,Atom.apply,Store.setScalar,Function.update_apply,r.injective.eq_iff,hpos]) hle
    (by simp [T,applyAtoms,Atom.apply,Store.setScalar,Function.update_apply,r.injective.eq_iff,hlen])
    (by simp [T,applyAtoms,Atom.apply,Store.setScalar,Function.update_apply,r.injective.eq_iff])
    (by simp [T,applyAtoms,Atom.apply,Store.setScalar,Function.update_apply,r.injective.eq_iff,hvalid])
    (by simp [T,applyAtoms,Atom.apply,Store.setScalar,Function.update_apply,r.injective.eq_iff])
    (by simp [T,applyAtoms,Atom.apply,Store.setScalar,Function.update_apply,r.injective.eq_iff])
    (by simp [T,applyAtoms,Atom.apply,hinput]) hword (by simpa using hn)
  refine ⟨U,?_,hU,up,by simpa using uv,uok,us,ul,uo,ua⟩
  convert Runs.seq first last using 1 <;> simp <;> omega

private theorem unary_cases (w : List Bool) :
    (∃ n tail,w=List.replicate n true ++ false::tail) ∨
      ∃ n,w=List.replicate n true := by
  induction w with
  | nil => exact .inr ⟨0,rfl⟩
  | cons b w ih =>
    cases b with
    | false => exact .inl ⟨0,w,rfl⟩
    | true =>
      rcases ih with ⟨n,tail,h⟩ | ⟨n,h⟩
      · exact .inl ⟨n+1,tail,by simp [List.replicate_succ,h]⟩
      · exact .inr ⟨n+1,by simp [List.replicate_succ,h]⟩

private theorem readUnary_replicate (n : ℕ) :
    Statement.readUnary (List.replicate n true)=none := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,Statement.readUnary,ih]

/-- The concrete scan agrees with the manuscript encoding parser on every
raw input, including missing unary delimiters. -/
theorem unaryScan_correct (r : Fin 8 ↪ Reg) (input : Arr)
    (S : Store Reg Arr) (w : List Bool) (pos m : ℕ)
    (hb : S.Bounded m) (hroom : 1≤m) (hpos : S.scalar (r 0)=pos) (hle : pos≤w.length)
    (hlen : S.scalar (r 1)=w.length) (hvalid : S.scalar (r 3)=1)
    (hinput : S.array input=w.map bitNat) :
    ∃ T t, t≤7*w.length+11 ∧ Runs (storageBound Reg Arr m) (unaryScan r input) S t T ∧
      T.Bounded m ∧ T.scalar (r 0)≤w.length ∧ T.scalar (r 3)≤1 ∧ T.scalar (r 4)=0 ∧
      T.scalar (r 1)=w.length ∧ T.scalar (r 7)=1 ∧ T.array input=w.map bitNat ∧
      Statement.readUnary (w.drop pos) =
        if T.scalar (r 3)=0 then none else some (T.scalar (r 2),w.drop (T.scalar (r 0))) := by
  rcases unary_cases (w.drop pos) with ⟨n,tail,hw⟩ | ⟨n,hw⟩
  · obtain ⟨T,hr,hT,hp,hv,hok,hs,hl,ho,ha⟩ :=
      unaryScan_success r input S w tail pos n m hb hroom hpos hlen hvalid hinput hw
    have hh := congrArg List.length hw
    simp only [List.length_drop,List.length_append,List.length_replicate,List.length_cons] at hh
    have htail : w.drop (pos+n+1)=tail := by
      have hx := congrArg (List.drop (n+1)) hw
      simpa [List.drop_drop,List.drop_append,List.drop_replicate,Nat.add_assoc] using hx
    refine ⟨T,7*n+11,by omega,hr,hT,by omega,by omega,hs,hl,ho,ha,?_⟩
    rw [hp,hv,hok,if_neg (by decide),htail,hw]
    simpa [Statement.unary,List.append_assoc] using Statement.readUnary_unary n tail
  · obtain ⟨T,hr,hT,hp,hv,hok,hs,hl,ho,ha⟩ :=
      unaryScan_failure r input S w pos n m hb hroom hpos hle hlen hvalid hinput hw
    have hh := congrArg List.length hw
    simp only [List.length_drop,List.length_replicate] at hh
    refine ⟨T,7*n+9,by omega,hr,hT,by omega,by omega,hs,hl,ho,ha,?_⟩
    simp [hok,hw,readUnary_replicate]

end GroupWL.MachinePrograms.NatArrayParser
