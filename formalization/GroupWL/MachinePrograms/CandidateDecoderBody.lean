import GroupWL.MachinePrograms.CandidateDecoderBranch

namespace GroupWL.MachinePrograms.CandidateDecoder
open NatArrayLanguage
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

theorem Data.transport {p j q : ℕ} [Fact p.Prime] {S T : State} (h : Data p j q S)
    (hv : T.scalar (.inr .valid)=S.scalar (.inr .valid)) (ht : T.array (.inr .table)=S.array (.inr .table)) :
    Data p j q T := ⟨hv.trans h.valid,fun g hg => ht.trans (h.table g hg)⟩

theorem Data.scalarUpdate {p j q : ℕ} [Fact p.Prime] {S : State} (h : Data p j q S)
    (r : Control) (v : ℕ) (hr : r≠.valid) : Data p j q (S.setScalar (.inr r) v) :=
  h.transport (by simp [Store.setScalar,Ne.symm hr]) rfl

theorem body_runs {p j : ℕ} [Fact p.Prime] (S : State) (M q : ℕ)
    (hb : S.Bounded M) (hdata : Data p j q S)
    (hn : S.scalar (.inr .order)=p^j) (hj : S.scalar (.inr .level)=j)
    (hp : S.scalar (.inr .prime)=p) (hq : S.scalar (.inr .code)=q/NumericCandidateCodes.radix p j)
    (hroom : ((p^j)*(p^j))*((p^j)*(p^j))≤M) (hpow : (p^j)^j≤M)
    (hexp : 2*p≤M) (hcube : (p*(p^j))^3≤M) (hnext : p^(j+1)≤M) :
    ∃t≤CandidateExtend.budget p (p^j) j+3*j+17,∃T,Runs (storageBound Reg Arr M) body S t T ∧
      T.Bounded M ∧ Data p (j+1) q T ∧ T.scalar (.inr .order)=p^(j+1) ∧
      T.scalar (.inr .code)=q/NumericCandidateCodes.radix p (j+1) := by
  have hnpos : 0<p^j := pow_pos (Fact.out : p.Prime).pos j
  obtain ⟨P,powerRun,hP,hpower⟩ := power_runs powerRegisters S (p^j) j M hb hnpos
    (by simpa [powerRegisters] using hn) (by simpa [powerRegisters] using hj) hpow
  have pframe (r : Control) (hr : r∈({.order,.level,.prime,.code,.valid} : Finset Control)) :
      P.scalar (.inr r)=S.scalar (.inr r) := powerRun.scalar_eq_of_not_mem _
        ((by decide : ∀r∈({.order,.level,.prime,.code,.valid} : Finset Control),
          (Sum.inr r : Reg)∉(power powerRegisters : Code).scalarWrites) r hr)
  have hdataP := hdata.transport (pframe .valid (by decide))
    (powerRun.array_eq_of_not_mem (.inr .table) (by decide))
  obtain ⟨extract,hQ,himage,hcarry,hcode⟩ := extract_runs P M (p^j) j
    (q/NumericCandidateCodes.radix p j) hP ((pframe .order (by decide)).trans hn)
    (by simpa [powerRegisters] using hpower) ((pframe .code (by decide)).trans hq) hnpos
  let Q := applyAtoms extractAtoms P
  have qframe (r : Control) (hr : r∈({.order,.level,.prime,.valid} : Finset Control)) :
      Q.scalar (.inr r)=S.scalar (.inr r) :=
    (extract.scalar_eq_of_not_mem _ ((by decide : ∀r∈({.order,.level,.prime,.valid} : Finset Control),
      (Sum.inr r : Reg)∉(atoms extractAtoms : Code).scalarWrites) r hr)).trans
      (pframe r (by simp only [Finset.mem_insert,Finset.mem_singleton] at hr ⊢; tauto))
  have hdataQ := hdataP.transport (extract.scalar_eq_of_not_mem (.inr .valid) (by decide))
    (extract.array_eq_of_not_mem (.inr .table) (by decide))
  obtain ⟨t,ht,U,branchRun,hU,hdataU⟩ := branch_runs Q M q hQ hdataQ
    ((qframe .order (by decide)).trans hn) ((qframe .level (by decide)).trans hj)
    ((qframe .prime (by decide)).trans hp) himage hcarry hroom hpow hexp hcube
  have hnU : U.scalar (.inr .order)=p^j := (branch_frame branchRun .order (by decide)).trans ((qframe .order (by decide)).trans hn)
  have hpU : U.scalar (.inr .prime)=p := (branch_frame branchRun .prime (by decide)).trans ((qframe .prime (by decide)).trans hp)
  have hqU : U.scalar (.inr .code)=q/NumericCandidateCodes.radix p (j+1) := by
    rw [branch_frame branchRun .code (by decide),hcode,NumericPGroupCandidates.quotient_next]
  let T := U.setScalar (.inr .order) (p^(j+1))
  have hT : T.Bounded M := hU.setScalar _ hnext
  have post : Runs (storageBound Reg Arr M)
      (.atom (.binary .mul (.inr .order) (.inr .order) (.inr .prime))) U 1 T := by
    simpa [T,Atom.apply,BinaryOp.eval,hnU,hpU,pow_succ] using
      atom_runs hU (.binary .mul (.inr .order) (.inr .order) (.inr .prime)) trivial
        (by simpa [Atom.SmallResult,BinaryOp.eval,hnU,hpU,pow_succ] using hnext)
  refine ⟨(3*j+4)+(2+(t+(1+0))),by omega,T,
    .seq powerRun (.seq extract (.seq branchRun (.seq post (.skip post.end_bound)))),hT,?_,?_,?_⟩
  · exact hdataU.scalarUpdate .order _ (by decide)
  · simp [T]
  · simpa [T] using hqU

theorem body_frame {B S T t} (h : Runs B body S t T) (r : Control)
    (hr : r∈({.level,.todo,.dimension,.one,.prime} : Finset Control)) :
    T.scalar (.inr r)=S.scalar (.inr r) := h.scalar_eq_of_not_mem _
      ((by decide : ∀r∈({.level,.todo,.dimension,.one,.prime} : Finset Control),
        (Sum.inr r : Reg)∉body.scalarWrites) r hr)

end GroupWL.MachinePrograms.CandidateDecoder
