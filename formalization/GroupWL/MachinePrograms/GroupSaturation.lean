import GroupWL.MachinePrograms.FiniteSetArrays
import GroupWL.MachinePrograms.NatArrayFrames
import GroupWL.MachinePrograms.NatArrayCountedLoops
import GroupWL.PositiveWordTypes

/-! Finite subgroup saturation by explicit multiplication-table reads. A
characteristic array is copied once per round and filled by a quadratic scan. -/
namespace GroupWL.MachinePrograms.GroupSaturation

open NatArrayLanguage FiniteSetArrays
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

inductive Reg where
  | order | one | total | position | todo | round | roundTodo | u | v | left | right | flag | product
  deriving DecidableEq, Fintype

inductive Arr where
  | table | current | next
  deriving DecidableEq, Fintype

abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def pairAtoms : List (Atom Reg Arr) := [
  .divmod .u .v .position .order,
  .read .left .current .u, .read .right .current .v,
  .binary .mul .flag .left .right, .read .product .table .position]

def stepPair : Code := .seq (atoms pairAtoms)
  (.branch .flag (.atom (.write .next .product .one)) .skip)

def step : Code := sequence [
  .atom (.copyArray .next .current),
  countedLoop .position .todo .total .one stepPair,
  .atom (.copyArray .current .next)]

def saturate : Code := sequence [
  .atom (.const .one 1), .atom (.binary .mul .total .order .order),
  countedLoop .round .roundTodo .order .one step]

theorem stepPair_runs (S : State) (n M : ℕ) (C R : Finset (Fin n))
    (op : Fin n → Fin n → Fin n) (i : Fin (n*n))
    (hb : S.Bounded M) (hn : S.scalar .order=n) (h1 : S.scalar .one=1)
    (hi : S.scalar .position=i.val) (hcurrent : S.array .current=word C)
    (hnext : S.array .next=word R) (hlen : (S.array .table).length=n*n)
    (hread : (S.array .table)[i.val]?.getD 0=
      (op (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2).val)
    (hroom : n*n≤M) :
    ∃ t≤7,∃ T,Runs (storageBound Reg Arr M) stepPair S t T ∧ T.Bounded M ∧
      T.array .next=word (addPair C op R (finProdFinEquiv.symm i)) := by
  let a := (finProdFinEquiv.symm i).1
  let b := (finProdFinEquiv.symm i).2
  have hpos : 0<n := by have := a.isLt; omega
  have hM : 1≤M := by nlinarith
  have ha : i.val/n=a.val := rfl
  have hb' : i.val%n=b.val := rfl
  have hleft : (S.array .current)[i.val/n]?.getD 0=if a∈C then 1 else 0 := by
    rw [hcurrent,ha,read_word]
  have hright : (S.array .current)[i.val%n]?.getD 0=if b∈C then 1 else 0 := by
    rw [hcurrent,hb',read_word]
  have hclen : (S.array .current).length=n := by simp [hcurrent]
  have hv : ValidAtoms M pairAtoms S := by
    simp [pairAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,hn,hi,hpos,hleft,hright,hclen,ha,hb',hlen,i.isLt,a.isLt,b.isLt,word]
    by_cases hca : a∈C <;> by_cases hcb : b∈C <;> simp [hcurrent,word,hca,hcb,hM]
  obtain ⟨pre,hU⟩ := atoms_runs hb pairAtoms hv
  let U := applyAtoms pairAtoms S
  have hflag : U.scalar .flag=if a∈C ∧ b∈C then 1 else 0 := by
    simp [U,applyAtoms,pairAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,hn,hi,hleft,hright]
    by_cases hca : a∈C <;> by_cases hcb : b∈C <;> simp [hca,hcb]
  have hprod : U.scalar .product=(op a b).val := by
    simpa [U,applyAtoms,pairAtoms,Atom.apply,Store.setScalar,hi] using hread
  have hone : U.scalar .one=1 := by
    simp [U,applyAtoms,pairAtoms,Atom.apply,Store.setScalar,h1]
  have hunext : U.array .next=word R := hnext
  by_cases hab : a∈C ∧ b∈C
  · let V := (Atom.write Arr.next Reg.product Reg.one).apply U
    have hvalid : (Atom.write Arr.next Reg.product Reg.one).Valid U := by
      simpa [Atom.Valid,hprod,hunext] using (op a b).isLt
    have hV : V.Bounded M := (Atom.apply_bounded hU _ trivial)
    have writeRun := atom_runs hU (.write .next .product .one) hvalid trivial
    refine ⟨7,le_rfl,V,.seq pre (.branch_nonzero (by rw [hflag,if_pos hab]; omega) writeRun),hV,?_⟩
    change V.array .next=word (addPair C op R (a,b))
    simp [V,Atom.apply,Store.setArray,hprod,hone,hunext,addPair,hab,word_insert]
  · refine ⟨6,by omega,U,.seq pre (.branch_zero (by rw [hflag,if_neg hab])
      (.skip (Store.size_le_of_bounded hU))),hU,?_⟩
    change U.array .next=word (addPair C op R (a,b))
    simpa [addPair,hab] using hunext

end GroupWL.MachinePrograms.GroupSaturation
