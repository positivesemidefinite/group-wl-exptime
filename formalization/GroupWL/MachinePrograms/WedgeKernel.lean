import GroupWL.MachinePrograms.WedgeConstraints
import GroupWL.MachinePrograms.KernelCost

/-! Materialize the obstruction equations and execute their Gaussian kernel. -/
namespace GroupWL.MachinePrograms.WedgeKernel
open NatArrayLanguage NatArrayExpressions
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 4096
abbrev Reg := Registers WedgeConstraints.Reg WedgeConstraints.expression.need ⊕ KernelProgram.Reg
abbrev Arr := WedgeConstraints.Arr ⊕ KernelProgram.Arr
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr
def word (D : WedgeConstraints.Descriptors) (E H : List ℕ) (p n oldOut k ni no : ℕ) :=
  List.ofFn (fun i : Fin (k*ni*no)=>WedgeConstraints.entry D E H p n oldOut k ni no i.val)
def data (D : WedgeConstraints.Descriptors) (E H : List ℕ) (p n oldOut k ni no : ℕ) :=
  KernelProgram.executeRows (word D E H p n oldOut k ni no) p (ni*no) k (KernelProgram.initial (ni*no))
def setup : List (Atom Reg Arr) := [
  .binary .mul (.inr (KernelProgram.wr .ambient)) (.inl (.inl .input)) (.inl (.inl .output)),
  .copy (.inr (KernelProgram.wr .rows)) (.inl (.inl .width)),
  .copy (.inr (KernelProgram.wr .modulus)) (.inl (.inl .modulus)),
  .copyArray (.inr (KernelProgram.wa .input)) (.inl .result)]
def program (p : ℕ) : Code := .seq (WedgeConstraints.program.map Sum.inl Sum.inl)
  (.seq (atoms setup) ((KernelProgram.program p).map Sum.inr Sum.inr))

theorem word_values (D : WedgeConstraints.Descriptors) (E H : List ℕ) (p n oldOut k ni no : ℕ)
    (hp : 0<p) : ∀x∈word D E H p n oldOut k ni no,x<p := by
  intro x hx
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  unfold WedgeConstraints.entry
  split_ifs
  · exact Nat.mod_lt _ hp
  · exact hp

theorem program_runs (D : WedgeConstraints.Descriptors) (E H : List ℕ) (p n oldOut k ni no f M : ℕ)
    [NeZero p] (hp : 1<p) (hM : 1≤M) (hpM : p*p+2*p≤M) (hnino : ni*no≤M)
    (square : (ni*no)*(ni*no)≤M) (hE : E.length=f*n) (hH : H.length=f*k)
    (ev : ∀x∈E,x<p) (hv : ∀x∈H,x<p) (valid : D.Valid oldOut f)
    (S : State) (bounded : S.Bounded M)
    (ready : WedgeConstraints.Ready D E H p n oldOut k ni no (inputs S.left))
    (length : S.left.scalar (.inl .total)=k*ni*no) :
    ∃t≤(k*ni*no)*(WedgeConstraints.expression.cost+4)+10+220*(k+ni*no+p+1)^4,∃T,
      Runs (storageBound Reg Arr M) (program p) S t T ∧ T.Bounded M ∧
      KernelProgram.Represents p (ni*no) 0 (word D E H p n oldOut k ni no)
        (data D E H p n oldOut k ni no) T.right := by
  obtain ⟨t,ht,U,wedge,hUB,hUR,hUout⟩ := WedgeConstraints.program_runs D E H p n oldOut k ni no f M
    (by omega) hM hpM hnino hE hH ev hv valid S.left bounded.left ready length
  have first := wedge.left_bounded bounded
  let V := U.join S.right
  have hVB := hUB.join bounded.right
  have hsni : V.scalar (.inl (.inl .input))=ni := hUR.2.2.2.2.1
  have hsno : V.scalar (.inl (.inl .output))=no := hUR.2.2.2.2.2.1
  have hsk : V.scalar (.inl (.inl .width))=k := hUR.2.2.2.1
  have hsp : V.scalar (.inl (.inl .modulus))=p := hUR.1
  have prepValid : ValidAtoms M setup V := by
    simp [setup,ValidAtoms,Atom.Valid,Atom.SmallResult,BinaryOp.eval,hsni,hsno,hnino]
  obtain ⟨prepared,hWB⟩ := atoms_runs hVB setup prepValid
  let W := applyAtoms setup V
  have ambient : W.right.scalar (KernelProgram.wr .ambient)=ni*no := by
    simp [W,setup,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,Store.right,hsni,hsno]
  have rows : W.right.scalar (KernelProgram.wr .rows)=k := by
    simp [W,setup,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,Store.right,hsk]
  have modulus : W.right.scalar (KernelProgram.wr .modulus)=p := by
    simp [W,setup,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,Store.right,hsp]
  have input : W.right.array (KernelProgram.wa .input)=word D E H p n oldOut k ni no := hUout
  obtain ⟨u,hu,X,kernel,hXB,hrep⟩ := KernelProgram.program_runs p (ni*no) k M
    (word D E H p n oldOut k ni no) W.right hWB.right ambient rows modulus input hp (by omega)
    square (by simp [word,Nat.mul_assoc]) (word_values D E H p n oldOut k ni no (by omega))
  refine ⟨t+(4+u),?_,W.left.join X,first.seq (prepared.seq (kernel.right_bounded hWB)),hWB.left.join hXB,hrep⟩
  have hu' := hu.trans (KernelProgram.programCost_le k (ni*no) p)
  omega

end GroupWL.MachinePrograms.WedgeKernel
