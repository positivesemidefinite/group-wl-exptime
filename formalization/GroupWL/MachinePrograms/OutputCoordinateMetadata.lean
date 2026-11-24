import GroupWL.MachinePrograms.ArrayScaledOffsets

/-! Internal output offsets, incidence output size, and both padded dimensions. -/
namespace GroupWL.MachinePrograms.OutputCoordinateMetadata
open NatArrayLanguage
inductive Admin where | frames | incidences | oldInput | two | edges | oldOutput | input | output
  deriving DecidableEq,Fintype
abbrev Reg := ArrayScaledOffsets.Reg ⊕ Admin
abbrev Arr := ArrayScaledOffsets.Arr ⊕ Unit
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr
def internal (dims : List ℕ) (pairs : ℕ) :=
  FilterRanks.count (ArrayScaledOffsets.scaled dims pairs) dims.length
def oldOutput (dims : List ℕ) (pairs edges q : ℕ) := internal dims pairs+edges*q*q*2
def finish : List (Atom Reg Arr) := [
  .const (.inr .two) 2,
  .binary .mul (.inr .edges) (.inr .incidences) (.inr .frames),
  .binary .mul (.inr .edges) (.inr .edges) (.inr .frames),
  .binary .mul (.inr .edges) (.inr .edges) (.inr .two),
  .binary .add (.inr .oldOutput) (.inl (.inr .count)) (.inr .edges),
  .binary .add (.inr .input) (.inr .oldInput) (.inr .oldOutput),
  .binary .add (.inr .output) (.inr .oldOutput) (.inr .input)]
def program : Code := .seq (ArrayScaledOffsets.program.map Sum.inl Sum.inl) (atoms finish)

theorem program_runs (dims : List ℕ) (pairs edges q oldN M : ℕ) (hq : 1≤q) (hM : 2≤M)
    (small : ∀ i<dims.length,dims[i]?.getD 0*pairs≤M)
    (size : oldN+2*oldOutput dims pairs edges q≤M)
    (S : State) (bounded : S.Bounded M) (hdims : S.left.left.array .input=dims)
    (hpairs : S.left.left.scalar .factor=pairs) (hedges : S.scalar (.inr .incidences)=edges)
    (hframes : S.scalar (.inr .frames)=q) (hold : S.scalar (.inr .oldInput)=oldN) :
    ∃ t≤dims.length*12+23, ∃ T, Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧
      T.left.left.array .input=dims ∧
      T.left.right.array .ranks=List.ofFn (fun i : Fin dims.length =>
        FilterRanks.count (ArrayScaledOffsets.scaled dims pairs) i.val) ∧
      T.scalar (.inr .oldOutput)=oldOutput dims pairs edges q ∧
      T.scalar (.inr .input)=oldN+oldOutput dims pairs edges q ∧
      T.scalar (.inr .output)=oldOutput dims pairs edges q+(oldN+oldOutput dims pairs edges q) := by
  have total : FilterRanks.count (ArrayScaledOffsets.scaled dims pairs)
      (ArrayScaledOffsets.scaled dims pairs).length≤M := by
    simpa only [ArrayScaledOffsets.scaled,List.length_ofFn] using
      (show internal dims pairs≤M by unfold oldOutput at size; omega)
  obtain ⟨t,ht,U,offsets,hUB,hUi,hUout,hUtotal,hUranks⟩ :=
    ArrayScaledOffsets.program_runs dims pairs M (by omega) small total S.left bounded.left hdims hpairs
  have first := offsets.left_bounded bounded
  let V := U.join S.right
  have hVB := hUB.join bounded.right
  have hedgesV : V.scalar (.inr .incidences)=edges := hedges
  have hframesV : V.scalar (.inr .frames)=q := hframes
  have holdV : V.scalar (.inr .oldInput)=oldN := hold
  have htotalV : V.scalar (.inl (.inr .count))=internal dims pairs := by
    simpa only [ArrayScaledOffsets.scaled,List.length_ofFn] using hUtotal
  have he1 : edges*q≤edges*q*q*2 := by
    have h := Nat.mul_le_mul_left (edges*q) hq
    nlinarith
  have he2 : edges*q*q≤edges*q*q*2 := by omega
  have valid : ValidAtoms M finish V := by
    simp [finish,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar,
      hedgesV,hframesV,holdV,htotalV]
    unfold oldOutput at size
    omega
  obtain ⟨last,hWB⟩ := atoms_runs hVB finish valid
  let W := applyAtoms finish V
  have hWL : W.left=U := by
    apply Store.ext
    · intro r; rfl
    · intro a; rfl
  refine ⟨t+7,by omega,W,first.seq last,hWB,?_,?_,?_,?_,?_⟩
  · change W.left.left.array .input=dims
    rw [hWL]
    exact hUi
  · change W.left.right.array .ranks=_
    rw [hWL]
    simpa only [ArrayScaledOffsets.scaled,List.length_ofFn] using hUranks
  all_goals simp [W,finish,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,
    hedgesV,hframesV,holdV,htotalV,oldOutput]

end GroupWL.MachinePrograms.OutputCoordinateMetadata
