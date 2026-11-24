import GroupWL.MachinePrograms.TupleTargetWords
import GroupWL.MachinePrograms.NatArrayConcat
import GroupWL.MachinePrograms.NatArrayComponents

/-! Complete materialization of the disjoint group-tuple replacement array. -/
namespace GroupWL.MachinePrograms.GroupTargetBuilder
open NatArrayLanguage
abbrev Reg := TupleTargets.Reg ⊕ NatArrayConcat.Reg
abbrev Arr := TupleTargets.Arr ⊕ NatArrayConcat.Arr
abbrev Code := Program Reg Arr
set_option maxRecDepth 4096

def between : List (Atom Reg Arr) := [
  .copyArray (.inr 0) (.inl ()),.copy (.inl 14) (.inl 13),.copy (.inl 0) (.inr 0)]

def generate : Code := .seq (TupleTargets.generate.map Sum.inl Sum.inl)
  (.seq (atoms between)
    (.seq (TupleTargets.generate.map Sum.inl Sum.inl)
      (.seq (.atom (.copyArray (.inr 1) (.inl ()))) (NatArrayConcat.concat.map Sum.inr Sum.inr))))

theorem generate_runs (n m k : ℕ) (hn : 0<n) (hm : 0<m) (S : Store Reg Arr) (B : ℕ)
    (hS : S.Bounded B) (hleft : S.scalar (.inl 0)=n) (hright : S.scalar (.inr 0)=m)
    (hk : S.scalar (.inl 11)=k) (hb : S.scalar (.inl 12)=max n m) (hoff : S.scalar (.inl 14)=0)
    (huniverse : n^k+m^k≤B) (hslots : (n^k+m^k)*max n m≤B)
    (hsize : ((n^k+m^k)*max n m)*k≤B) :
    ∃ t≤(((n^k+m^k)*max n m)*k)*(3*k+27)+6*k+37,∃ T,
      Runs (storageBound Reg Arr B) generate S t T ∧ T.Bounded B ∧
      T.array (.inr 2)=(IndexedTuples.data n m k hn).targetWord := by
  have hleftSlots : n^k*max n m≤B := (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)).trans hslots
  have hrightSlots : m^k*max n m≤B := (Nat.mul_le_mul_right _ (Nat.le_add_left _ _)).trans hslots
  have hleftSize : (n^k*max n m)*k≤B := by
    exact (Nat.mul_le_mul_right k (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))).trans hsize
  have hrightSize : (m^k*max n m)*k≤B := by
    exact (Nat.mul_le_mul_right k (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))).trans hsize
  obtain ⟨t,ht,U,first,hU,hwordU,hcountU⟩ := TupleTargets.generate_runs_with_count n k (max n m) 0 hn
    S.left B hS.left hleft hk hb hoff (by omega) hleftSlots hleftSize
  let A := U.join S.right
  have first' : Runs (storageBound Reg Arr B) (TupleTargets.generate.map Sum.inl Sum.inl) S t A :=
    first.left_bounded hS
  have hA : A.Bounded B := hU.join hS.right
  have frames (r : TupleTargets.Reg) (hr : r=11 ∨ r=12) : U.scalar r=S.left.scalar r := by
    apply first.scalar_eq_of_not_mem
    rcases hr with rfl|rfl <;>
      simp [TupleTargets.generate,TupleTargets.prelude,TupleTargets.fill,TupleTargets.body,
        TupleTargets.compute,TupleTargets.addOffset,TupleTargets.decodeAtoms,TupleTargets.countRegisters,
        TupleTargets.replacementRegisters,replaceTuple,replacementAtoms,replacementPowerRegisters,
        power,powerLoop,powerBody,atoms,countedLoop,NatArrayLanguage.sequence,
        Program.scalarWrites,Atom.scalarWrites]
  have hvalid : ValidAtoms B between A := by
    simp [between,ValidAtoms,Atom.Valid,Atom.SmallResult]
  obtain ⟨middle,hV⟩ := atoms_runs hA between hvalid
  let V := applyAtoms between A
  have vl : V.left.scalar 0=m := by
    simp [V,applyAtoms,between,Atom.apply,Store.left,Store.setScalar,A,Store.right,hright]
  have vk : V.left.scalar 11=k := by
    simpa [V,applyAtoms,between,Atom.apply,Store.left,Store.setScalar,A] using
      (frames 11 (Or.inl rfl)).trans hk
  have vb : V.left.scalar 12=max n m := by
    simpa [V,applyAtoms,between,Atom.apply,Store.left,Store.setScalar,A] using
      (frames 12 (Or.inr rfl)).trans hb
  have voff : V.left.scalar 14=n^k := by
    simp [V,applyAtoms,between,Atom.apply,Store.left,Store.setScalar,A,hcountU]
  have vsaved : V.right.array 0=TupleTargets.word n k (max n m) 0 := by
    simp [V,applyAtoms,between,Atom.apply,Store.right,Store.setArray,A,hwordU]
  obtain ⟨u,hu,W,second,hW,hwordW⟩ := TupleTargets.generate_runs m k (max n m) (n^k) hm
    V.left B hV.left vl vk vb voff huniverse hrightSlots hrightSize
  let C := W.join V.right
  have second' : Runs (storageBound Reg Arr B) (TupleTargets.generate.map Sum.inl Sum.inl) V u C :=
    second.left_bounded hV
  have hC : C.Bounded B := hW.join hV.right
  have copy := atom_runs hC (.copyArray (.inr 1) (.inl ())) trivial trivial
  let D := C.setArray (.inr 1) (W.array ())
  have hD : D.Bounded B := by
    change ((Atom.copyArray (.inr 1) (.inl ())).apply C).Bounded B
    exact (Atom.copyArray (.inr 1) (.inl ())).apply_bounded hC trivial
  have copy' : Runs (storageBound Reg Arr B) (.atom (.copyArray (.inr 1) (.inl ()))) C 1 D := copy
  have dl : D.right.array 0=TupleTargets.word n k (max n m) 0 := by
    simpa [D,C,Store.right,Store.setArray] using vsaved
  have dr : D.right.array 1=TupleTargets.word m k (max n m) (n^k) := by
    simp [D,Store.right,Store.setArray,hwordW]
  have hlen : (D.right.array 0).length+(D.right.array 1).length≤B := by
    rw [dl,dr,TupleTargets.word_length,TupleTargets.word_length]
    nlinarith
  have h1 : 1≤B := by have hp : 0<n^k := pow_pos hn _; omega
  obtain ⟨v,hv,X,last,hX,hout,_,_⟩ := NatArrayConcat.concat_runs D.right B hD.right hlen h1
  have last' := last.right_bounded hD
  refine ⟨t+(3+(u+(1+v))),?_,D.left.join X,
    Runs.seq first' (Runs.seq middle (Runs.seq second' (Runs.seq copy' last'))),hD.left.join hX,?_⟩
  · rw [dl,dr,TupleTargets.word_length,TupleTargets.word_length] at hv
    nlinarith
  · change X.array 2=_
    rw [hout,dl,dr,TupleTargets.targetWord_eq_append]

end GroupWL.MachinePrograms.GroupTargetBuilder
