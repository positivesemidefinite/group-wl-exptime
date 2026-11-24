import GroupWL.MachinePrograms.NatArrayProofs
import GroupWL.MachinePrograms.NatArrayFrames

/-! Decode a first, middle, or last private-wire link from its canonical code. -/
namespace GroupWL.MachinePrograms.LinkIndex
open NatArrayLanguage

inductive Reg where
  | comparisons | length | link | kind | comparison | offset | cutoff | flag
  deriving DecidableEq,Fintype
inductive Arr where
  | unused
  deriving DecidableEq,Fintype
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def kind (e L i : ℕ) : ℕ := if i<e then 0 else if i<e+e*L then 1 else 2
def comparison (e L i : ℕ) : ℕ := if i<e then i else if i<e+e*L then (i-e)/L else i-(e+e*L)
def offset (e L i : ℕ) : ℕ := if i<e then 0 else if i<e+e*L then (i-e)%L else 0
def prelude : List (Atom Reg Arr) := [
  .binary .mul .cutoff .comparisons .length,.binary .add .cutoff .cutoff .comparisons,
  .copy .comparison .link,.const .offset 0,.const .kind 0]
def middle : List (Atom Reg Arr) := [
  .binary .sub .comparison .link .comparisons,
  .divmod .comparison .offset .comparison .length,.const .kind 1]
def last : List (Atom Reg Arr) := [.binary .sub .comparison .link .cutoff,.const .kind 2]
def program : Code := .seq (atoms prelude)
  (.seq (.atom (.binary .lt .flag .link .comparisons))
    (.branch .flag .skip (.seq (.atom (.binary .lt .flag .link .cutoff))
      (.branch .flag (atoms middle) (atoms last)))))

theorem program_runs (S : State) (M : ℕ) (bounded : S.Bounded M) (room : 2≤M)
    (positive : 0<S.scalar .length)
    (small : S.scalar .comparisons+S.scalar .comparisons*S.scalar .length≤M) :
    ∃ t≤12,∃ T,Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧
      T.scalar .kind=kind (S.scalar .comparisons) (S.scalar .length) (S.scalar .link) ∧
      T.scalar .comparison=comparison (S.scalar .comparisons) (S.scalar .length) (S.scalar .link) ∧
      T.scalar .offset=offset (S.scalar .comparisons) (S.scalar .length) (S.scalar .link) := by
  have hlink := bounded.1 Reg.link
  have preValid : ValidAtoms M prelude S := by
    simp [prelude,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar]
    omega
  obtain ⟨pre,hU⟩ := atoms_runs bounded prelude preValid
  let U := applyAtoms prelude S
  let a : Atom Reg Arr := .binary .lt .flag .link .comparisons
  have asmall : a.SmallResult M U := by
    simp [a,Atom.SmallResult,BinaryOp.eval]; split_ifs <;> omega
  have first := atom_runs hU a trivial asmall
  have hV := a.apply_bounded hU asmall
  let V := a.apply U
  have vf : V.scalar .flag=if S.scalar .link<S.scalar .comparisons then 1 else 0 := by
    simp [V,a,U,applyAtoms,prelude,Atom.apply,BinaryOp.eval,Store.setScalar]
  by_cases hf : S.scalar .link<S.scalar .comparisons
  · refine ⟨7,by omega,V,.seq pre (.seq first (.branch_nonzero (by rw [vf]; simp [hf])
      (.skip (Store.size_le_of_bounded hV)))),hV,?_,?_,?_⟩ <;>
      simp [V,a,U,applyAtoms,prelude,Atom.apply,BinaryOp.eval,Store.setScalar,kind,comparison,offset,hf]
  · let b : Atom Reg Arr := .binary .lt .flag .link .cutoff
    have bsmall : b.SmallResult M V := by
      simp [b,Atom.SmallResult,BinaryOp.eval]; split_ifs <;> omega
    have second := atom_runs hV b trivial bsmall
    have hW := b.apply_bounded hV bsmall
    let W := b.apply V
    have wf : W.scalar .flag=if S.scalar .link<S.scalar .comparisons+S.scalar .comparisons*S.scalar .length then 1 else 0 := by
      simp [W,b,V,a,U,applyAtoms,prelude,Atom.apply,BinaryOp.eval,Store.setScalar,Nat.add_comm]
    by_cases hm : S.scalar .link<S.scalar .comparisons+S.scalar .comparisons*S.scalar .length
    · have middleValid : ValidAtoms M middle W := by
        simp [middle,ValidAtoms,Atom.Valid,Atom.SmallResult,W,b,V,a,U,applyAtoms,prelude,
          Atom.apply,BinaryOp.eval,Store.setScalar]
        exact ⟨by omega,positive,by omega⟩
      obtain ⟨run,hT⟩ := atoms_runs hW middle middleValid
      refine ⟨12,by omega,applyAtoms middle W,
        .seq pre (.seq first (.branch_zero (by rw [vf]; simp [hf])
          (.seq second (.branch_nonzero (by rw [wf]; simp [hm]) run)))),hT,?_,?_,?_⟩ <;>
        simp [applyAtoms,middle,W,b,V,a,U,prelude,Atom.apply,BinaryOp.eval,Store.setScalar,kind,comparison,offset,hf,hm]
    · have lastValid : ValidAtoms M last W := by
        simp [last,ValidAtoms,Atom.Valid,Atom.SmallResult,W,b,V,a,U,applyAtoms,prelude,
          Atom.apply,BinaryOp.eval,Store.setScalar]
        omega
      obtain ⟨run,hT⟩ := atoms_runs hW last lastValid
      refine ⟨11,by omega,applyAtoms last W,
        .seq pre (.seq first (.branch_zero (by rw [vf]; simp [hf])
          (.seq second (.branch_zero (by rw [wf]; simp [hm]) run)))),hT,?_,?_,?_⟩ <;>
        simp [applyAtoms,last,W,b,V,a,U,prelude,Atom.apply,BinaryOp.eval,Store.setScalar,
          kind,comparison,offset,hf,hm,Nat.add_comm]

theorem comparison_lt {e L i : ℕ} (positive : 0<L) (valid : i<e+e*L+e) : comparison e L i<e := by
  unfold comparison
  split_ifs with h₁ h₂
  · exact h₁
  · apply (Nat.div_lt_iff_lt_mul positive).mpr
    omega
  · omega

end GroupWL.MachinePrograms.LinkIndex
