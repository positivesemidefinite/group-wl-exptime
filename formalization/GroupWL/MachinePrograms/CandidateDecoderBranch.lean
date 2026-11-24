import GroupWL.MachinePrograms.CandidateDecoderStep

namespace GroupWL.MachinePrograms.CandidateDecoder
open NatArrayLanguage
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

structure Data (p j q : ℕ) [Fact p.Prime] (S : State) : Prop where
  valid : S.scalar (.inr .valid)=(if (NumericPGroupCandidates.decode (p:=p) j q).isSome then 1 else 0)
  table : ∀g,NumericPGroupCandidates.decode (p:=p) j q=some g →
    S.array (.inr .table)=GroupInitial.tableWord (NumericGroupGenerators.operation g)

def branch : Code := .branch (.inr .valid) extend .skip

theorem branch_runs {p j : ℕ} [Fact p.Prime] (S : State) (M q : ℕ)
    (hb : S.Bounded M) (hdata : Data p j q S)
    (hn : S.scalar (.inr .order)=p^j) (hj : S.scalar (.inr .level)=j)
    (hp : S.scalar (.inr .prime)=p)
    (hv : S.scalar (.inr .imageCode)=(q/NumericCandidateCodes.radix p j)%((p^j)^j))
    (hc : S.scalar (.inr .carry)=(q/NumericCandidateCodes.radix p j)/((p^j)^j)%(p^j))
    (hroom : ((p^j)*(p^j))*((p^j)*(p^j))≤M) (hpow : (p^j)^j≤M)
    (hexp : 2*p≤M) (hcube : (p*(p^j))^3≤M) :
    ∃t≤CandidateExtend.budget p (p^j) j+10,∃T,Runs (storageBound Reg Arr M) branch S t T ∧
      T.Bounded M ∧ Data p (j+1) q T := by
  cases h : NumericPGroupCandidates.decode (p:=p) j q with
  | none =>
    have hv0 : S.scalar (.inr .valid)=0 := by simpa [h] using hdata.valid
    refine ⟨1,by omega,S,.branch_zero hv0 (.skip (Store.size_le_of_bounded hb)),hb,?_,?_⟩
    · simp [NumericPGroupCandidates.decode_succ,h,hv0]
    · intro g hg
      simp [NumericPGroupCandidates.decode_succ,h] at hg
  | some g =>
    let v : Fin ((p^j)^j) := ⟨(q/NumericCandidateCodes.radix p j)%((p^j)^j),
      Nat.mod_lt _ (pow_pos (pow_pos (Fact.out : p.Prime).pos j) j)⟩
    let c := NumericPGroupCandidates.carryAt p j (q/NumericCandidateCodes.radix p j)
    have hvid : S.scalar (.inr .valid)≠0 := by simp [hdata.valid,h]
    obtain ⟨t,ht,T,run,hT,ho,hr⟩ := extend_runs g S M v c
      (NumericPGroupCandidates.decode_identity j q g h) hb hn hj hp (hdata.table g h) hv hc hroom hpow hexp hcube
    refine ⟨t+1,by omega,T,.branch_nonzero hvid run,hT,?_,?_⟩
    · simpa [NumericPGroupCandidates.decode_succ,h,NumericPGroupCandidates.imagesAt,v,c] using hr
    · intro g' hg'
      have hgext : NumericPGroupCandidates.extend g (finFunctionFinEquiv.symm v) c=some g' := by
        simpa [NumericPGroupCandidates.decode_succ,h,NumericPGroupCandidates.imagesAt,v,c] using hg'
      have hop := (NumericPGroupCandidates.extend_properties g (finFunctionFinEquiv.symm v) c g' hgext).2
      simpa only [hop] using ho

theorem branch_frame {B S T t} (h : Runs B branch S t T) (r : Control) (hr : r≠.valid) :
    T.scalar (.inr r)=S.scalar (.inr r) :=
  h.scalar_eq_of_not_mem _ ((by decide : ∀r:Control,r≠.valid → (Sum.inr r : Reg)∉branch.scalarWrites) r hr)

end GroupWL.MachinePrograms.CandidateDecoder
