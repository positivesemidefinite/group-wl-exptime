import GroupWL.MachinePrograms.CircuitMetadataExpressions

namespace GroupWL.MachinePrograms.CircuitMetadataExpressions
open NatArrayLanguage NatArrayExpressions CircuitMetadataValues
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

theorem fstIf (p : Prop) [Decidable p] (a b : ℕ×ℕ) :
    (if p then a else b).1=if p then a.1 else b.1 := by split_ifs <;> rfl
theorem sndIf (p : Prop) [Decidable p] (a b : ℕ×ℕ) :
    (if p then a else b).2=if p then a.2 else b.2 := by split_ifs <;> rfl
theorem orIf (p q : Prop) [Decidable p] [Decidable q] (x y : ℕ) :
    (if (if p then 1 else 0)+(if q then 1 else 0)=0 then y else x)=
      if p∨q then x else y := by by_cases p <;> by_cases q <;> simp_all


theorem testIf (p : Prop) [Decidable p] (x y : ℕ) :
    (if (if p then 1 else 0)=0 then y else x)=if p then x else y := by
  by_cases p <;> simp_all

theorem entry_eval (f : Field) (S : Store Reg Input) :
    (entry f).eval S=value (readData S) f (S.scalar .index) := by
  cases f <;>
    simp only [entry,value,dimension,source,target,sourceForm,targetForm,domain,permutation,
      connectionSource,connectionTarget,connectionSourceForm,connectionTargetForm,
      connectionDomain,connectionPermutation,connectionCase,pairIf,sourceGate,gateOutput,
      schemaStride,requestStride,num,reg,rd,add,sub,mul,quo,rem,eq,lt,branch,
      Total.eval,Op.eval,BinaryOp.eval,readData,Data.dimension,Data.source,Data.target,
      Data.sourceForm,Data.targetForm,Data.domain,Data.permutation,Data.connectionSource,
      Data.connectionTarget,Data.connectionSourceForm,Data.connectionTargetForm,
      Data.connectionDomain,Data.connectionPermutation,Data.connectionCase,
      Data.sourceGate,Data.gateOutput,Data.schemaStride,Data.requestStride,fstIf,sndIf,orIf,testIf]


  all_goals rfl

end GroupWL.MachinePrograms.CircuitMetadataExpressions
