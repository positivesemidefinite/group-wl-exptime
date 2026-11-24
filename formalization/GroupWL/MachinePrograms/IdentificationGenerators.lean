import GroupWL.MachinePrograms.GeneratorChoice
import GroupWL.NumericPGroupCandidates

/-! Compute a generating tuple directly from the numeric multiplication table
of any source group of order p^D. -/
namespace GroupWL.MachinePrograms.IdentificationGenerators
open NatArrayLanguage
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
variable {p D : ℕ} [Fact p.Prime]
variable {G : Type} [Group G] [Fintype G] [DecidableEq G]

@[reducible] def numericGroup (e : G≃Fin (p^D)) : Group (Fin (p^D)) :=
  NumericPGroupCandidates.transportedGroup e.symm inferInstance

def generators (e : G≃Fin (p^D)) : Fin D→Fin (p^D) :=
  NumericGroupGenerators.generators (numericGroup e)

theorem generates (e : G≃Fin (p^D)) : Refinement.Generates (e.symm ∘ generators e) := by
  letI := numericGroup e
  let f := NumericPGroupCandidates.transportEquiv e.symm (inferInstance : Group G)
  have hgen := NumericGroupGenerators.generators_generate (numericGroup e)
  intro x
  obtain ⟨w,hw⟩ := hgen (e x)
  refine ⟨w,?_⟩
  change w.eval (f.toMonoidHom ∘ generators e)=x
  rw [Refinement.GroupWord.eval_hom,generators,hw]
  exact e.symm_apply_apply x

theorem choose_runs (e : G≃Fin (p^D)) (S : GeneratorChoice.State) (B : ℕ)
    (hb : S.Bounded B)
    (hn : S.scalar (GeneratorChoice.decoderReg .n)=p^D)
    (hd : S.scalar (GeneratorChoice.decoderReg .arity)=D)
    (he : S.scalar (GeneratorChoice.seedReg .identity)=(e 1).val)
    (table : S.array (GeneratorChoice.closureArr .table)=
      GroupInitial.tableWord (fun x y=>e (e.symm x*e.symm y)))
    (hroom : (p^D)*(p^D)≤B) (hpow : (p^D)^D≤B) :
    ∃t≤(p^D)^D*(10*(p^D)^3+13*(p^D)+11*D+35)+9*D+20,∃T,
      Runs (storageBound GeneratorChoice.Reg GeneratorChoice.Arr B) GeneratorChoice.choose S t T ∧
      T.Bounded B ∧ T.array (GeneratorChoice.decoderArr .vector)=GroupInitial.tupleWord (generators e) := by
  obtain ⟨t,ht,T,run,hT,ready,found,index,out,limit⟩ :=
    GeneratorChoice.choose_numeric_runs (numericGroup e) S B hb hn hd he table hroom hpow
  exact ⟨t,ht,T,run,hT,out⟩

end GroupWL.MachinePrograms.IdentificationGenerators
