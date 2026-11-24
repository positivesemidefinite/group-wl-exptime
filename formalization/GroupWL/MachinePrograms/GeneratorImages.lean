import GroupWL.MachinePrograms.FirstNonzeroLoop
import GroupWL.MachinePrograms.NatArrayComponents
import GroupWL.MachinePrograms.ArrayTabulation

/-! Expand proposed generator images from a materialized paired-subgroup
mask, by finding the first target entry in each source row. -/
namespace GroupWL.MachinePrograms.GeneratorImages

open NatArrayLanguage
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

inductive Control where
  | rows | cols | identity | one | row | todo
  deriving DecidableEq, Fintype
inductive Output where
  | images
  deriving DecidableEq, Fintype
abbrev Reg := FirstNonzero.Reg ⊕ Control
abbrev Arr := FirstNonzero.Arr ⊕ Output
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def rowPrelude : List (Atom Reg Arr) := [
  .binary .mul (.inl .base) (.inr .row) (.inr .cols),
  .copy (.inl .length) (.inr .cols),.copy (.inl .fallback) (.inr .identity)]
def rowCode : Code := .seq (atoms rowPrelude)
  (.seq (FirstNonzero.search.map Sum.inl Sum.inl)
    (.atom (.write (.inr .images) (.inr .row) (.inl .result))))
def expand : Code := sequence [
  .atom (.const (.inr .one) 1),
  .atom (.allocate (.inr .images) (.inr .rows) (.inr .identity)),
  countedLoop (.inr .row) (.inr .todo) (.inr .rows) (.inr .one) rowCode]

def rowImage (xs : List ℕ) (cols identity row : ℕ) : ℕ :=
  (FirstNonzero.hit xs (row*cols) cols).getD identity

theorem rowCode_runs (S : State) (M rows cols identity row : ℕ)
    (hb : S.Bounded M) (hc : S.scalar (.inr .cols)=cols)
    (he : S.scalar (.inr .identity)=identity) (hr : S.scalar (.inr .row)=row)
    (hrow : row<rows) (helt : identity<cols)
    (hlen : (S.array (.inl .input)).length=rows*cols)
    (hout : (S.array (.inr .images)).length=rows) (hroom : rows*cols≤M) :
    ∃ t≤9*cols+10,∃ T,Runs (storageBound Reg Arr M) rowCode S t T ∧ T.Bounded M ∧
      T.array (.inr .images)=(S.array (.inr .images)).set row
        (rowImage (S.array (.inl .input)) cols identity row) := by
  have hM : 1≤M := by nlinarith
  have hbase : row*cols≤M := by nlinarith
  have hv : ValidAtoms M rowPrelude S := by
    simp [rowPrelude,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,hc,he,hr,hbase]
  obtain ⟨pre,hU⟩ := atoms_runs hb rowPrelude hv
  let U := applyAtoms rowPrelude S
  obtain ⟨t,ht,V,search,hV,hfound,hresult⟩ := FirstNonzero.search_runs U.left M cols (row*cols) identity hU.left
    (by simp [U,applyAtoms,rowPrelude,Atom.apply,BinaryOp.eval,Store.setScalar,Store.left,hr,hc])
    (by simp [U,applyAtoms,rowPrelude,Atom.apply,Store.setScalar,Store.left,hc])
    (by simp [U,applyAtoms,rowPrelude,Atom.apply,Store.setScalar,Store.left,he])
    (by change row*cols+cols≤(S.array (.inl .input)).length; rw [hlen]; nlinarith) hM
  let W := V.join U.right
  have hw : W.Bounded M := hV.join hU.right
  have hrowW : W.scalar (.inr .row)=row := by
    simp [W,U,applyAtoms,rowPrelude,Atom.apply,Store.setScalar,Store.right,hr]
  have himages : W.array (.inr .images)=S.array (.inr .images) := rfl
  let T := (Atom.write (.inr Output.images) (.inr Control.row) (.inl FirstNonzero.Reg.result)).apply W
  have hwrite : (Atom.write (.inr Output.images) (.inr Control.row)
      (.inl FirstNonzero.Reg.result)).Valid W := by
    simpa [Atom.Valid,hrowW,himages,hout] using hrow
  have post := atom_runs hw (.write (.inr .images) (.inr .row) (.inl .result)) hwrite trivial
  have hT : T.Bounded M := Atom.apply_bounded hw _ trivial
  refine ⟨3+(t+1),by omega,T,.seq pre (.seq (search.left_bounded hU) post),hT,?_⟩
  change (W.array (.inr .images)).set (W.scalar (.inr .row))
    (V.scalar .result) = _
  rw [hrowW,himages]
  simpa [rowImage,Store.left,U,applyAtoms,rowPrelude,Atom.apply,Store.setScalar] using
    congrArg (fun v => (S.array (.inr .images)).set row v) hresult

end GroupWL.MachinePrograms.GeneratorImages
