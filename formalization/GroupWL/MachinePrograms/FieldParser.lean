import GroupWL.MachinePrograms.NatArrayParser

/-! Parsing bounded field representatives by a concrete array program. -/
namespace GroupWL.MachinePrograms.NatArrayParser

open NatArrayLanguage
open NatArrayLowering (bitNat)

def readNatField (p : ℕ) (w : List Bool) : Option (ℕ × List Bool) := do
  let (n,tail) ← Statement.readUnary w
  if n<p then some (n,tail) else none

theorem readNatField_some {p n : ℕ} {w tail : List Bool} :
    readNatField p w=some (n,tail) ↔ Statement.readUnary w=some (n,tail) ∧ n<p := by
  unfold readNatField
  cases h : Statement.readUnary w with
  | none => simp
  | some v =>
    rcases v with ⟨a,xs⟩
    by_cases ha : a<p <;> simp [ha,Prod.mk.injEq] <;> aesop

variable {Reg Arr : Type*} [DecidableEq Reg] [DecidableEq Arr]
  [Fintype Reg] [Fintype Arr]

def fieldScan (r : Fin 8 ↪ Reg) (input : Arr) (p : ℕ) : NatArrayLanguage.Program Reg Arr :=
  .seq (unaryScan r input) (atoms [.const (r 6) p,
    .binary .lt (r 6) (r 2) (r 6),.binary .mul (r 3) (r 3) (r 6)])

theorem fieldScan_correct (r : Fin 8 ↪ Reg) (input : Arr) (p : ℕ)
    (S : Store Reg Arr) (w : List Bool) (pos m : ℕ)
    (hb : S.Bounded m) (hroom : 1≤m) (hp : p≤m)
    (hpos : S.scalar (r 0)=pos) (hle : pos≤w.length)
    (hlen : S.scalar (r 1)=w.length) (hvalid : S.scalar (r 3)=1)
    (hinput : S.array input=w.map bitNat) :
    ∃ T t, t≤7*w.length+14 ∧ Runs (storageBound Reg Arr m) (fieldScan r input p) S t T ∧
      T.Bounded m ∧ T.scalar (r 0)≤w.length ∧ T.scalar (r 3)≤1 ∧ T.scalar (r 4)=0 ∧
      T.scalar (r 1)=w.length ∧ T.scalar (r 7)=1 ∧ T.array input=w.map bitNat ∧
      readNatField p (w.drop pos) =
        if T.scalar (r 3)=0 then none else some (T.scalar (r 2),w.drop (T.scalar (r 0))) := by
  obtain ⟨U,u,hu,hr,hU,upos,uvalid,uscan,ulen,uone,uinput,hparse⟩ :=
    unaryScan_correct r input S w pos m hb hroom hpos hle hlen hvalid hinput
  let as : List (Atom Reg Arr) := [.const (r 6) p,
    .binary .lt (r 6) (r 2) (r 6),.binary .mul (r 3) (r 3) (r 6)]
  have hv : ValidAtoms m as U := by
    by_cases hx : U.scalar (r 2)<p <;>
      simp [as,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
        Store.setScalar,Function.update_apply,r.injective.eq_iff,hx,hp,hroom] <;> omega
  obtain ⟨last,hT⟩ := atoms_runs hU as hv
  let T := applyAtoms as U
  have tpos : T.scalar (r 0)=U.scalar (r 0) := by
    simp [T,applyAtoms,as,Atom.apply,Store.setScalar,r.injective.eq_iff]
  have tvalue : T.scalar (r 2)=U.scalar (r 2) := by
    simp [T,applyAtoms,as,Atom.apply,Store.setScalar,r.injective.eq_iff]
  have tvalid : T.scalar (r 3)=U.scalar (r 3)*(if U.scalar (r 2)<p then 1 else 0) := by
    simp [T,applyAtoms,as,Atom.apply,BinaryOp.eval,Store.setScalar,r.injective.eq_iff]
  refine ⟨T,u+3,by omega,?_,hT,by omega,?_,?_,?_,?_,?_,?_⟩
  · exact .seq hr last
  · rw [tvalid]; split <;> simp_all
  · simp [T,applyAtoms,as,Atom.apply,Store.setScalar,r.injective.eq_iff,uscan]
  · simp [T,applyAtoms,as,Atom.apply,Store.setScalar,r.injective.eq_iff,ulen]
  · simp [T,applyAtoms,as,Atom.apply,Store.setScalar,r.injective.eq_iff,uone]
  · simpa [T,applyAtoms,as,Atom.apply] using uinput
  · rw [tpos,tvalue,tvalid]
    unfold readNatField
    rw [hparse]
    by_cases hz : U.scalar (r 3)=0
    · simp [hz]
    · have hv : U.scalar (r 3)=1 := by omega
      by_cases ha : U.scalar (r 2)<p <;> simp [hv,ha]

theorem fieldScan_array_frame {r : Fin 8 ↪ Reg} {input : Arr} {p B S T t}
    (h : Runs B (fieldScan r input p) S t T) (a : Arr) : T.array a=S.array a := by
  apply h.array_eq_of_not_mem a
  simp [fieldScan,unaryScan,unaryStep,atoms,NatArrayLanguage.sequence,Program.arrayWrites,Atom.arrayWrites]

end GroupWL.MachinePrograms.NatArrayParser
