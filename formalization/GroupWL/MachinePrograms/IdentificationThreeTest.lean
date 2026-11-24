import GroupWL.MachinePrograms.IdentificationCandidate
import GroupWL.MachinePrograms.FullGadgetWL

/-! Concrete counterexample test: decode a candidate, discard isomorphic
candidates, and compare the remaining candidate with the source by WL. -/
namespace GroupWL.MachinePrograms.IdentificationThreeTest
open NatArrayLanguage
set_option maxHeartbeats 2500000
set_option maxRecDepth 16000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false

abbrev Reg := IdentificationCandidate.Reg ⊕ SimpleGadget.Reg
abbrev Arr := IdentificationCandidate.Arr ⊕ SimpleGadget.Arr
abbrev State := Store Reg Arr
abbrev Code := NatArrayLanguage.Program Reg Arr
instance : DecidableEq Reg := inferInstance
instance : DecidableEq Arr := inferInstance
instance : Fintype Reg := inferInstance
instance : Fintype Arr := inferInstance

private def leftCount : SimpleGadget.Reg := .inl (.inl (.inl 0))
private def rightCount : SimpleGadget.Reg := .inl (.inr (.inl 0))
private def arity : SimpleGadget.Reg := .inr (GraphWLCore.wl .arity)
private def leftTable : SimpleGadget.Arr := .inl (.inl (.inl ()))
private def rightTable : SimpleGadget.Arr := .inl (.inr (.inl ()))
private def wlResult : SimpleGadget.Reg := .inr (GraphWLCore.wl .result)
def result : Reg := .inl IdentificationCandidate.isomorphic
def inputCode : Reg := .inl (.inr .code)
def zero : Reg := .inl (IdentificationCandidate.decReg (.inr .zero))
def prepare : List (Atom Reg Arr) := [
  .copy (.inr (leftCount)) (.inl (.inr .order)),
  .copy (.inr (rightCount)) (.inl (.inr .order)),
  .copy (.inr (arity)) (.inl (.inr .arity)),
  .copyArray (.inr (leftTable)) (.inl (.inr .table)),
  .copyArray (.inr (rightTable)) (.inl (IdentificationCandidate.decArr (.inr .table)))]
def normalize : List (Atom Reg Arr) := [
  .const zero 0,.binary .eq result (.inr (wlResult)) zero,
  .binary .eq result result zero]
def wlPhase : Code := .seq (atoms prepare)
  (.seq ((SimpleGadget.decide).map Sum.inr Sum.inr) (atoms normalize))
def finish : Code := .branch (.inl IdentificationCandidate.valid)
  (.branch result (.atom (.const result 0)) (wlPhase)) (.atom (.const result 0))
def test (p : ℕ) : Code := .seq ((IdentificationCandidate.program p).map Sum.inl Sum.inl) (finish)

def wlCost (B : ℕ) : ℕ := 1500*(B+1)^7

def testCost (p D B : ℕ) : ℕ := IdentificationCandidate.cost p D+wlCost B+10

variable {p D : ℕ} [Fact p.Prime]
variable {G : Type} [Group G] [Fintype G] [DecidableEq G]

/-- The input contract for the concrete WL phase. A client theorem supplies
this specification for the full gadget comparison; the syntax above always executes that
fixed program. -/
def WLContract (version : Refinement.Version) (k B : ℕ)
    (e : G≃Fin (p^D)) : Prop :=
  ∀ (g : Group (Fin (p^D))) (S : SimpleGadget.State),
    (NumericGroupGenerators.identity g).val=0 → S.Bounded B →
    S.scalar (leftCount)=p^D → S.scalar (rightCount)=p^D →
    S.scalar (arity)=k →
    S.array (leftTable)=GroupInitial.tableWord (fun x y=>e (e.symm x*e.symm y)) →
    S.array (rightTable)=GroupInitial.tableWord (NumericGroupGenerators.operation g) →
    ∃t≤wlCost B,∃T,Runs (storageBound SimpleGadget.Reg SimpleGadget.Arr B) (SimpleGadget.decide) S t T ∧
      T.Bounded B ∧
      (letI := g; letI : Mul (Fin (p^D)) := g.toMul
       T.scalar (wlResult)≠0 ↔ Refinement.GroupEquivalent version k G (Fin (p^D)))

theorem contract {k B : ℕ} (e : G≃Fin (p^D)) (positive : 0<k)
    (sq : (IndexedGadget.size (p^D))^2≤B)
    (matrix : GraphMatrixPrograms.Room (IndexedGadget.size (p^D)) (IndexedGadget.size (p^D)) k B)
    (room : IndexedWL.Room ((IndexedGadget.size (p^D))^k+(IndexedGadget.size (p^D))^k) k
      (IndexedGadget.size (p^D)) B) : WLContract .three k B e := by
  intro g S _ hb hn hm hk hs ht
  letI := g
  letI : Mul (Fin (p^D)) := g.toMul
  exact SimpleGadget.pair_runs_III e (Equiv.refl _) S B positive hb hn hm hk hs ht sq sq matrix (by simpa using room)

theorem wlPhase_runs (version : Refinement.Version) (k B : ℕ)
    (e : G≃Fin (p^D)) (a : Fin D→Fin (p^D))
    (contract : WLContract version k B e)
    (g : Group (Fin (p^D))) (hg : (NumericGroupGenerators.identity g).val=0)
    (S : State) (hb : S.Bounded B) (hB : 1≤B) (input : IdentificationCandidate.Input e a S.left)
    (hk : S.scalar (.inl (.inr .arity))=k)
    (table : S.array (.inl (IdentificationCandidate.decArr (.inr .table)))=
      GroupInitial.tableWord (NumericGroupGenerators.operation g)) :
    ∃t≤wlCost B+8,∃T,Runs (storageBound Reg Arr B) (wlPhase) S t T ∧ T.Bounded B ∧
      T.left.right=S.left.right ∧ T.scalar result≤1 ∧
      (letI := g; letI : Mul (Fin (p^D)) := g.toMul
       T.scalar result=1 ↔ Refinement.GroupEquivalent version k G (Fin (p^D))) := by
  letI := g
  letI : Mul (Fin (p^D)) := g.toMul
  obtain ⟨prep,hU⟩ := atoms_runs hb prepare
    (by simp [prepare,ValidAtoms,Atom.Valid,Atom.SmallResult])
  let U := applyAtoms prepare S
  have hin : U.right.scalar (leftCount)=p^D ∧
      U.right.scalar (rightCount)=p^D ∧ U.right.scalar (arity)=k ∧
      U.right.array (leftTable)=GroupInitial.tableWord (fun x y=>e (e.symm x*e.symm y)) ∧
      U.right.array (rightTable)=GroupInitial.tableWord (NumericGroupGenerators.operation g) := by
    simp [U,prepare,applyAtoms,Atom.apply,Store.right,Store.left,Store.setScalar,Store.setArray,
      leftCount,rightCount,arity,leftTable,rightTable,GraphWLCore.wl,IdentificationCandidate.decArr]
    exact ⟨input.order,hk,input.table,table⟩
  obtain ⟨t,ht,V,run,hV,correct⟩ := contract g U.right hg hU.right hin.1 hin.2.1 hin.2.2.1 hin.2.2.2.1 hin.2.2.2.2
  let W := U.left.join V
  have hW : W.Bounded B := hU.left.join hV
  have norm : ValidAtoms B normalize W := by
    simp [normalize,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar,
      result,zero,IdentificationCandidate.isomorphic,IdentificationCandidate.decReg,IdentificationCandidate.isoReg,hB]
    split_ifs <;> omega
  obtain ⟨last,hT⟩ := atoms_runs hW normalize norm
  let T := applyAtoms normalize W
  have out : T.scalar result=if V.scalar (wlResult)=0 then 0 else 1 := by
    simp [T,applyAtoms,normalize,Atom.apply,BinaryOp.eval,Store.setScalar,result,zero,
      IdentificationCandidate.isomorphic,IdentificationCandidate.decReg,IdentificationCandidate.isoReg,W]
  refine ⟨5+(t+3),by omega,T,.seq prep (.seq (run.right_bounded hU) last),hT,?_,?_,?_⟩
  · apply Store.ext <;> intro r <;>
      simp [T,W,U,applyAtoms,normalize,prepare,Atom.apply,Store.left,Store.right,Store.setScalar,Store.setArray,
        result,zero,IdentificationCandidate.isomorphic,IdentificationCandidate.decReg,IdentificationCandidate.isoReg]
  · rw [out]; split_ifs <;> omega
  · rw [out]; simpa using correct

theorem test_runs (version : Refinement.Version) (k B : ℕ)
    (e : G≃Fin (p^D)) (a : Fin D→Fin (p^D))
    (ha : Refinement.Generates (e.symm ∘ a)) (he : (e 1).val=0)
    (contract : WLContract version k B e)
    (S : State) (q : ℕ) (hb : S.Bounded B) (input : IdentificationCandidate.Input e a S.left)
    (hk : S.scalar (.inl (.inr .arity))=k) (hq : S.scalar inputCode=q)
    (hroom : ((p^D)*(p^D))*((p^D)*(p^D))≤B) (hpow : (p^D)^D≤B) (hexp : 2*p≤B) :
    ∃t≤testCost p D B,∃T,Runs (storageBound Reg Arr B) (test p) S t T ∧ T.Bounded B ∧
      T.left.right=S.left.right ∧ T.scalar result≤1 ∧
      (T.scalar result=1 ↔ ¬NumericPGroupCandidates.CandidateGood (p:=p) version k D G q) := by
  have hB : 1≤B := (one_le_pow₀ (pow_pos (Fact.out : p.Prime).pos D)).trans hpow
  obtain ⟨t,ht,U,run,hU,fixed,data,iso⟩ := IdentificationCandidate.program_runs e a ha he S.left B q hb.left input hq hroom hpow hexp
  let W := U.join S.right
  have hW : W.Bounded B := hU.join hb.right
  have run' := run.left_bounded hb
  have fixedW : W.left.right=S.left.right := fixed
  have clear := atom_runs hW (.const result 0) trivial (show 0≤B by omega)
  have hclear : ((Atom.const result 0).apply W).Bounded B := Atom.apply_bounded hW (.const result 0) (Nat.zero_le B)
  have fixedClear : ((Atom.const result 0).apply W).left.right=S.left.right := by
    simpa [Atom.apply,result,IdentificationCandidate.isomorphic,IdentificationCandidate.isoReg,
      Store.left,Store.right,Store.setScalar] using congrArg (fun T=>T) fixedW
  cases h : NumericPGroupCandidates.decode (p:=p) D q with
  | none =>
    have zero : W.scalar (.inl IdentificationCandidate.valid)=0 := by simpa [W,IdentificationCandidate.valid,IdentificationCandidate.decReg,h] using data.valid
    refine ⟨t+2,by unfold testCost;omega,_,.seq run' (.branch_zero zero clear),hclear,fixedClear,?_,?_⟩
    · simp [Atom.apply]
    · simp [Atom.apply,NumericPGroupCandidates.CandidateGood,h]
  | some g =>
    letI := g
    letI : Mul (Fin (p^D)) := g.toMul
    have valid : W.scalar (.inl IdentificationCandidate.valid)≠0 := by
      have hv : W.scalar (.inl IdentificationCandidate.valid)=1 := by simpa [W,IdentificationCandidate.valid,IdentificationCandidate.decReg,h] using data.valid
      omega
    obtain ⟨bit,correct⟩ := iso g h
    change W.scalar result≤1 at bit
    change W.scalar result=1 ↔ Nonempty (G≃*Fin (p^D)) at correct
    by_cases hiso : W.scalar result=0
    · have notIso : ¬Nonempty (G≃*Fin (p^D)) := by rw [←correct,hiso]; omega
      have inp : IdentificationCandidate.Input e a W.left := by
        constructor
        · change W.left.right.scalar .dimension=D; rw [fixedW]; exact input.dimension
        · change W.left.right.scalar .order=p^D; rw [fixedW]; exact input.order
        · change W.left.right.array .table=_; rw [fixedW]; exact input.table
        · change W.left.right.array .generators=_; rw [fixedW]; exact input.generators
      have arity : W.scalar (.inl (.inr .arity))=k := by
        change W.left.right.scalar .arity=k; rw [fixedW]; exact hk
      obtain ⟨u,hu,T,wl,hT,fixT,outbit,out⟩ := wlPhase_runs version k B e a contract g
        (by simpa [NumericGroupGenerators.identity,NumericPGroupCandidates.identity,NumericPGroupCandidates.zero] using congrArg Fin.val (NumericPGroupCandidates.decode_identity D q g h))
        W hW hB inp arity (data.table g h)
      refine ⟨t+((u+1)+1),by unfold testCost;omega,T,.seq run' (.branch_nonzero valid (.branch_zero hiso wl)),
        hT,fixT.trans fixedW,outbit,?_⟩
      rw [out]
      simp only [NumericPGroupCandidates.CandidateGood,h]
      exact ⟨fun h hi=>notIso (hi h),fun h=>Classical.byContradiction (fun hn=>h (fun hh=>False.elim (hn hh)))⟩
    · have isIso : Nonempty (G≃*Fin (p^D)) := correct.mp (by omega)
      refine ⟨t+3,by unfold testCost;omega,_,.seq run' (.branch_nonzero valid (.branch_nonzero hiso clear)),
        hclear,fixedClear,?_,?_⟩
      · simp [Atom.apply]
      · simp [Atom.apply,NumericPGroupCandidates.CandidateGood,h,isIso]

end GroupWL.MachinePrograms.IdentificationThreeTest
