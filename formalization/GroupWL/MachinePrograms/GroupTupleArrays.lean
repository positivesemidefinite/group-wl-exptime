import GroupWL.MachinePrograms.GroupFanoutBuilder
import GroupWL.MachinePrograms.GroupSelectionBuilder

/-! All three replacement/selection arrays, materialized by fixed finite programs. -/
namespace GroupWL.MachinePrograms.GroupTupleArrays
open NatArrayLanguage
abbrev Reg := (GroupTargetBuilder.Reg ⊕ GroupFanoutBuilder.Reg) ⊕ GroupSelectionBuilder.Reg
abbrev Arr := (GroupTargetBuilder.Arr ⊕ GroupFanoutBuilder.Arr) ⊕ GroupSelectionBuilder.Arr
abbrev Code := Program Reg Arr
abbrev State := Store Reg Arr
set_option maxRecDepth 8192
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 1600000

def target (r : GroupTargetBuilder.Reg) : Reg := .inl (.inl r)
def fanout (r : GroupFanoutBuilder.Reg) : Reg := .inl (.inr r)
def selection (r : GroupSelectionBuilder.Reg) : Reg := .inr r

def prepare : List (Atom Reg Arr) := [
  .copy (fanout (.inl 0)) (target (.inl 0)),
  .copy (fanout (.inr 0)) (target (.inr 0)),
  .copy (fanout (.inl 1)) (target (.inl 11)),
  .const (target (.inl 14)) 0,.const (selection (.inl 1)) 0]

def generate : Code := .seq (atoms prepare)
  (.seq ((GroupTargetBuilder.generate.map Sum.inl Sum.inl).map Sum.inl Sum.inl)
    (.seq ((GroupFanoutBuilder.generate.map Sum.inr Sum.inr).map Sum.inl Sum.inl)
      (GroupSelectionBuilder.generate.map Sum.inr Sum.inr)))

theorem generate_runs (n m k : ℕ) (hn : 0<n) (hm : 0<m) (S : State) (B : ℕ)
    (hS : S.Bounded B) (hleft : S.scalar (target (.inl 0))=n)
    (hright : S.scalar (target (.inr 0))=m) (hk : S.scalar (target (.inl 11))=k)
    (hwidth : S.scalar (target (.inl 12))=max n m)
    (hlcount : S.scalar (selection (.inl 0))=n^k)
    (hrcount : S.scalar (selection (.inr ()))=m^k)
    (huniverse : n^k+m^k≤B) (hslots : (n^k+m^k)*max n m≤B)
    (hsize : ((n^k+m^k)*max n m)*k≤B) :
    ∃t≤100*(B+1)^2,∃T,Runs (storageBound Reg Arr B) generate S t T ∧ T.Bounded B ∧
      T.array (.inl (.inl (.inr 2)))=(IndexedTuples.data n m k hn).targetWord ∧
      T.array (.inl (.inr (.inr 2)))=(IndexedTuples.data n m k hn).fanoutWord ∧
      T.array (.inr (.inr ()))=(IndexedTuples.leftSelection n m k).map Fin.val ∧
      T.array (.inr (.inl ()))=(IndexedTuples.rightSelection n m k).map Fin.val := by
  have h1 : 1≤B := (one_le_pow₀ hn).trans (by omega : n^k≤B)
  have hkB : k≤B := by simpa only [hk] using hS.1 (target (.inl 11))
  have valid : ValidAtoms B prepare S := by
    simp [prepare,ValidAtoms,Atom.Valid,Atom.SmallResult]
  obtain ⟨pre,hA⟩ := atoms_runs hS prepare valid
  let A := applyAtoms prepare S
  have al : A.left.left.scalar (.inl 0)=n := by
    simpa [A,applyAtoms,prepare,Atom.apply,Store.left,Store.setScalar,target,fanout,selection] using hleft
  have ar : A.left.left.scalar (.inr 0)=m := by
    simpa [A,applyAtoms,prepare,Atom.apply,Store.left,Store.setScalar,target,fanout,selection] using hright
  have ak : A.left.left.scalar (.inl 11)=k := by
    simpa [A,applyAtoms,prepare,Atom.apply,Store.left,Store.setScalar,target,fanout,selection] using hk
  have aw : A.left.left.scalar (.inl 12)=max n m := by
    simpa [A,applyAtoms,prepare,Atom.apply,Store.left,Store.setScalar,target,fanout,selection] using hwidth
  have az : A.left.left.scalar (.inl 14)=0 := by
    simp [A,applyAtoms,prepare,Atom.apply,Store.left,Store.setScalar,target,fanout,selection]
  have afl : A.left.right.scalar (.inl 0)=n := by
    simpa [A,applyAtoms,prepare,Atom.apply,Store.left,Store.right,Store.setScalar,target,fanout,selection] using hleft
  have afr : A.left.right.scalar (.inr 0)=m := by
    simpa [A,applyAtoms,prepare,Atom.apply,Store.left,Store.right,Store.setScalar,target,fanout,selection] using hright
  have afk : A.left.right.scalar (.inl 1)=k := by
    simpa [A,applyAtoms,prepare,Atom.apply,Store.left,Store.right,Store.setScalar,target,fanout,selection] using hk
  have asl : A.right.scalar (.inl 0)=n^k := by
    simpa [A,applyAtoms,prepare,Atom.apply,Store.right,Store.setScalar,target,fanout,selection] using hlcount
  have asr : A.right.scalar (.inr ())=m^k := by
    simpa [A,applyAtoms,prepare,Atom.apply,Store.right,Store.setScalar,target,fanout,selection] using hrcount
  have asz : A.right.scalar (.inl 1)=0 := by
    simp [A,applyAtoms,prepare,Atom.apply,Store.right,Store.setScalar,target,fanout,selection]
  obtain ⟨t,ht,U,first,hU,targets⟩ := GroupTargetBuilder.generate_runs n m k hn hm A.left.left B
    hA.left.left al ar ak aw az huniverse hslots hsize
  let C := (U.join A.left.right).join A.right
  have first' : Runs (storageBound Reg Arr B)
      ((GroupTargetBuilder.generate.map Sum.inl Sum.inl).map Sum.inl Sum.inl) A t C :=
    (first.left_bounded hA.left).left_bounded hA
  have hC : C.Bounded B := (hU.join hA.left.right).join hA.right
  obtain ⟨u,hu,V,second,hV,fanouts⟩ := GroupFanoutBuilder.generate_runs n m k hn hm C.left.right B
    hC.left.right afl afr afk huniverse
  let D := (C.left.left.join V).join C.right
  have second' : Runs (storageBound Reg Arr B)
      ((GroupFanoutBuilder.generate.map Sum.inr Sum.inr).map Sum.inl Sum.inl) C u D :=
    (second.right_bounded hC.left).left_bounded hC
  have hD : D.Bounded B := (hC.left.left.join hV).join hC.right
  obtain ⟨v,hv,W,last,hW,lefts,rights⟩ := GroupSelectionBuilder.generate_runs n m k D.right B
    hD.right asl asr asz huniverse h1
  have last' := last.right_bounded hD
  refine ⟨5+(t+(u+v)),?_,D.left.join W,.seq pre (.seq first' (.seq second' last')),
    hD.left.join hW,targets,fanouts,lefts,rights⟩
  have bound := Nat.mul_le_mul_right (3*k+27) hsize
  have bound' := Nat.mul_le_mul_left B (show 3*k+27≤3*B+27 by omega)
  nlinarith

end GroupWL.MachinePrograms.GroupTupleArrays
