import GroupWL.MachinePrograms.NatArrayProjection
import GroupWL.MachinePrograms.NatArrayCountedLoops
import GroupWL.MachinePrograms.NatArrayFrames

/-! First successful index in a bounded range, with a concrete program as the
predicate evaluator. The evaluator is embedded on disjoint finite registers. -/
namespace GroupWL.MachinePrograms.NatArrayPredicateSearch
open NatArrayLanguage
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

inductive Control where
  | limit | one | index | todo | flag | found | result
  deriving DecidableEq,Fintype
abbrev Reg (R : Type*) := R⊕Control
abbrev Arr (A : Type*) := A⊕PUnit.{1}
abbrev State (R A : Type*) := Store (Reg R) (Arr A)
abbrev Code (R A : Type*) := Program (Reg R) (Arr A)
variable {R A : Type*} [DecidableEq R] [DecidableEq A] [Fintype R] [Fintype A]

def hit (P : ℕ → Prop) [DecidablePred P] (i : ℕ) : Option ℕ :=
  (List.range i).find? (fun j => decide (P j))
@[simp] theorem hit_zero (P : ℕ → Prop) [DecidablePred P] : hit P 0=none := rfl
theorem hit_succ (P : ℕ → Prop) [DecidablePred P] (i : ℕ) :
    hit P (i+1)=(hit P i).or (if P i then some i else none) := by
  simp [hit,List.range_succ]

def latch : Code R A := .branch (.inr .flag)
  (.branch (.inr .found) .skip (atoms [.const (.inr .found) 1,.copy (.inr .result) (.inr .index)])) .skip

def body (p : Program R A) (input output : R) : Code R A :=
  .seq (.atom (.copy (.inl input) (.inr .index)))
    (.seq (p.map Sum.inl Sum.inl)
      (.seq (.atom (.binary .eq (.inr .flag) (.inl output) (.inr .one))) latch))

def search (p : Program R A) (input output : R) : Code R A :=
  .seq (atoms [.const (.inr .one) 1,.const (.inr .found) 0,.const (.inr .result) 0])
    (countedLoop (.inr .index) (.inr .todo) (.inr .limit) (.inr .one) (body p input output))

theorem latch_runs (S : State R A) (M i : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hb : S.Bounded M) (hM : 1≤M) (hi : S.scalar (.inr .index)=i)
    (hflag : S.scalar (.inr .flag)=if P i then 1 else 0)
    (hfound : S.scalar (.inr .found)=if (hit P i).isSome then 1 else 0)
    (hresult : S.scalar (.inr .result)=(hit P i).getD 0) :
    ∃t≤4,∃T,Runs (storageBound (Reg R) (Arr A) M) latch S t T ∧ T.Bounded M ∧
      T.left=S.left ∧ T.scalar (.inr .found)=(if (hit P (i+1)).isSome then 1 else 0) ∧
      T.scalar (.inr .result)=(hit P (i+1)).getD 0 := by
  by_cases hp : P i
  · cases hh : hit P i with
    | none =>
      have hz : S.scalar (.inr .found)=0 := by simp [hfound,hh]
      have hv : ValidAtoms M [.const (Sum.inr Control.found) 1,.copy (.inr .result) (.inr .index)] S := by
        simp [ValidAtoms,Atom.Valid,Atom.SmallResult,hM]
      obtain ⟨write,hT⟩ := atoms_runs hb _ hv
      let T := applyAtoms [.const (Sum.inr Control.found) 1,.copy (.inr .result) (.inr .index)] S
      refine ⟨4,le_rfl,T,.branch_nonzero (by simp [hflag,hp]) (.branch_zero hz write),hT,?_,?_,?_⟩
      · simp [T,applyAtoms,Atom.apply]
      · simp [T,applyAtoms,Atom.apply,hit_succ,hh,hp]
      · simp [T,applyAtoms,Atom.apply,hit_succ,hh,hp,hi]
    | some j =>
      refine ⟨2,by omega,S,.branch_nonzero (by simp [hflag,hp])
        (.branch_nonzero (by simp [hfound,hh]) (.skip (Store.size_le_of_bounded hb))),hb,rfl,?_,?_⟩
      · simp [hit_succ,hh,hfound]
      · simp [hit_succ,hh,hresult]
  · refine ⟨1,by omega,S,.branch_zero (by simp [hflag,hp])
      (.skip (Store.size_le_of_bounded hb)),hb,rfl,?_,?_⟩
    · simpa [hit_succ,hp] using hfound
    · simpa [hit_succ,hp] using hresult

theorem body_runs (p : Program R A) (input output : R)
    (Good : Store R A → Prop) (P : ℕ → Prop) [DecidablePred P]
    (S : State R A) (M N c i : ℕ) (hb : S.Bounded M) (hM : 1≤M) (hiN : i<N)
    (hg : Good S.left) (hsetup : ∀S i,Good S → Good (S.setScalar input i))
    (hcode : ∀U i, U.Bounded M → Good U → U.scalar input=i → i<N →
      ∃t≤c,∃V,Runs (storageBound R A M) p U t V ∧ V.Bounded M ∧ Good V ∧ (V.scalar output=1 ↔ P i))
    (hi : S.scalar (.inr .index)=i) (hone : S.scalar (.inr .one)=1)
    (hfound : S.scalar (.inr .found)=if (hit P i).isSome then 1 else 0)
    (hresult : S.scalar (.inr .result)=(hit P i).getD 0) :
    ∃t≤c+6,∃T,Runs (storageBound (Reg R) (Arr A) M) (body p input output) S t T ∧
      T.Bounded M ∧ Good T.left ∧ T.scalar (.inr .found)=(if (hit P (i+1)).isSome then 1 else 0) ∧
      T.scalar (.inr .result)=(hit P (i+1)).getD 0 := by
  let U := S.setScalar (.inl input) i
  have hU : U.Bounded M := hb.setScalar _ (by simpa [hi] using hb.1 (.inr .index))
  have hgU : Good U.left := by simpa [U] using hsetup S.left i hg
  have copy : Runs (storageBound (Reg R) (Arr A) M) (.atom (.copy (.inl input) (.inr .index))) S 1 U := by
    simpa [U,Atom.apply,hi] using atom_runs hb (.copy (.inl input) (.inr .index)) trivial trivial
  obtain ⟨t,ht,V,run,hV,hgV,hout⟩ := hcode U.left i hU.left hgU (by simp [U,Store.left,Store.setScalar]) hiN
  let W := V.join U.right
  have hW : W.Bounded M := hV.join hU.right
  let X := W.setScalar (.inr .flag) (if V.scalar output=1 then 1 else 0)
  have hX : X.Bounded M := hW.setScalar _ (by split_ifs <;> omega)
  have flag : Runs (storageBound (Reg R) (Arr A) M)
      (.atom (.binary .eq (.inr .flag) (.inl output) (.inr .one))) W 1 X := by
    have hwone : W.scalar (.inr .one)=1 := by simp [W,U,Store.right,Store.setScalar,hone]
    simpa [X,Atom.apply,BinaryOp.eval,W,hwone] using
      atom_runs hW (.binary .eq (.inr .flag) (.inl output) (.inr .one)) trivial
        (by change (if W.scalar (.inl output)=W.scalar (.inr .one) then 1 else 0)≤M; split_ifs <;> omega)
  obtain ⟨u,hu,T,select,hT,hleft,hf,hr⟩ := latch_runs X M i P hX hM
    (by simp [X,W,U,Store.right,Store.setScalar,hi])
    (by simp only [X,Store.setScalar_same]; simp only [hout])
    (by simpa [X,W,U,Store.right,Store.setScalar] using hfound)
    (by simpa [X,W,U,Store.right,Store.setScalar] using hresult)
  refine ⟨1+(t+(1+u)),by omega,T,.seq copy (.seq (run.left_bounded hU) (.seq flag select)),hT,?_,hf,hr⟩
  rw [hleft]
  simpa [X,W] using hgV

end GroupWL.MachinePrograms.NatArrayPredicateSearch
