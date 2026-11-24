import GroupWL.MachinePrograms.ExtensionTableAssembly
import GroupWL.MachinePrograms.GroupTableValidation
import GroupWL.MachinePrograms.NatArrayComponents

/-! Construct one cyclic-extension table and validate every finite group law. -/
namespace GroupWL.MachinePrograms.ExtensionCheck
open NatArrayLanguage
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

abbrev Reg := ExtensionTablePrograms.Reg ⊕ GroupTablePrograms.Reg
abbrev Arr := ExtensionTablePrograms.Arr ⊕ GroupTablePrograms.Arr
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def prepare : List (Atom Reg Arr) := [
  .binary .mul (.inr .order) (.inl .prime) (.inl .tail),
  .copy (.inr .identity) (.inl .identity),.copyArray (.inr .table) (.inl .output)]
def compute : Code := sequence [ExtensionTablePrograms.generate.map Sum.inl Sum.inl,
  atoms prepare,GroupTablePrograms.validate.map Sum.inr Sum.inr]

theorem compute_runs {p n : ℕ} (hp : 0<p) (hn : 0<n)
    (op : Fin n→Fin n→Fin n) (θ : Fin n→Fin n) (c e : Fin n) (S : State) (M : ℕ)
    (hb : S.Bounded M) (hinput : ExtensionTablePrograms.Input (p:=p) op θ c e M S.left)
    (hexp : 2*p≤M) (htable : n*n≤M) (hroom : (p*n)^3≤M) :
    ∃t≤36*(p*n)^3+(p*n)*(p*n)*(4*p+23)+18,∃T,
      Runs (storageBound Reg Arr M) compute S t T ∧ T.Bounded M ∧
      T.array (.inl .output)=GroupInitial.tableWord (ExtensionTablePrograms.operation hp op θ c e) ∧
      T.scalar (.inr .result)=(if VerifiedGroupTable.Valid
        (finProdFinEquiv ((⟨0,hp⟩ : Fin p),e)) (ExtensionTablePrograms.operation hp op θ c e) then 1 else 0) := by
  have hpos : 0<p*n := Nat.mul_pos hp hn
  have hsq : (p*n)*(p*n)≤M := by
    have h := Nat.mul_le_mul_left ((p*n)*(p*n)) (show 1≤p*n by omega)
    nlinarith
  have hN : p*n≤M := (Nat.le_mul_self _).trans hsq
  obtain ⟨t,ht,U,generate,hU,ho⟩ := ExtensionTablePrograms.generate_runs hp hn op θ c e S.left hinput hexp htable hsq
  let V := U.join S.right
  have hV : V.Bounded M := hU.join hb.right
  have hpV : V.scalar (.inl .prime)=p := (generate.scalar_eq_of_not_mem _ (by decide)).trans hinput.prime_eq
  have hnV : V.scalar (.inl .tail)=n := (generate.scalar_eq_of_not_mem _ (by decide)).trans hinput.tail_eq
  have heV : V.scalar (.inl .identity)=e.val := (generate.scalar_eq_of_not_mem _ (by decide)).trans hinput.identity_eq
  have hv : ValidAtoms M prepare V := by
    simp [prepare,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar,hpV,hnV,hN]
  obtain ⟨prep,hW⟩ := atoms_runs hV prepare hv
  let W := applyAtoms prepare V
  let identity : Fin (p*n) := finProdFinEquiv ((⟨0,hp⟩ : Fin p),e)
  have he : identity.val=e.val := by simp [identity,finProdFinEquiv]
  have hword : W.right.array .table=GroupInitial.tableWord (ExtensionTablePrograms.operation hp op θ c e) := by
    simpa [W,applyAtoms,prepare,Atom.apply,Store.setScalar,Store.setArray,Store.right,V] using ho
  obtain ⟨u,hu,X,validate,hX,hout⟩ := GroupTablePrograms.validate_runs W.right (p*n) M identity.val hW.right
    (by simp [W,applyAtoms,prepare,Atom.apply,Store.setScalar,Store.setArray,Store.right,BinaryOp.eval,hpV,hnV])
    (by simp [W,applyAtoms,prepare,Atom.apply,Store.setScalar,Store.setArray,Store.right,heV,he]) identity.isLt
    (by simp [hword])
    (by intro z hz; rw [hword,GroupInitial.tableWord] at hz
        obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz; exact (ExtensionTablePrograms.operation hp op θ c e _ _).isLt) hroom
  have hvalid := (GroupTablePrograms.prefixValid_complete hpos (W.right.array .table)).trans
    (GroupTablePrograms.tripleValid_iff hpos identity (ExtensionTablePrograms.operation hp op θ c e)
      (W.right.array .table) (by
        intro x y
        simpa [GroupTablePrograms.operation,GroupTablePrograms.read,hword,Nat.add_comm,Nat.mul_comm]
          using GroupInitial.tableWord_read (ExtensionTablePrograms.operation hp op θ c e) x y))
  have checked := validate.right_bounded hW
  refine ⟨t+(3+(u+0)),by omega,W.left.join X,
    .seq (generate.left_bounded hb) (.seq prep (.seq checked (.skip checked.end_bound))),hW.left.join hX,?_,?_⟩
  · simpa [W,applyAtoms,prepare,Atom.apply,Store.setScalar,Store.setArray,Store.left,V] using ho
  · change X.scalar .result=_
    rw [hout]
    simp only [hvalid]
    rfl

end GroupWL.MachinePrograms.ExtensionCheck
