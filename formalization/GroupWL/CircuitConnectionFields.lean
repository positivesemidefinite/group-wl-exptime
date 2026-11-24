import GroupWL.CircuitConnectionEncoding

/-! All numeric connection record fields agree with the comparison gadget. -/
namespace GroupWL.CircuitMetadataValues
open CircuitComparisons CircuitComparisonCodes AddressedCircuit MachinePrograms.CircuitRecordParser
open MachinePrograms.NatArrayLowering (bitNat)
set_option maxHeartbeats 2000000
variable {T : Type} [FiniteCode T] {r : ℕ} (C : Circuit T r)

def unit2 (F : Type*) [Zero F] [One F] (n : ℕ) (k : Fin 2) : Fin n → F :=
  fun i=>if i.val=k.val then 1 else 0

variable (p : ℕ) [Fact p.Prime]

theorem proj_unit2 (n : ℕ) (j : Fin n) (k : Fin 2) :
    ((LinearMap.proj j : (Fin n → ZMod p) →ₗ[ZMod p] ZMod p) (unit2 (ZMod p) n k)).val=
      if k.val=j.val then 1 else 0 := by
  have hp : 1<p := (Fact.out : p.Prime).one_lt
  change (if j.val=k.val then (1:ZMod p) else 0).val=_
  by_cases h : j.val=k.val <;> simp [h,eq_comm,ZMod.val_one,Nat.mod_eq_of_lt hp]

theorem portCoordinate_value (t : T) (b : Bool) :
    (portCoordinate C t b).val=if C.kind t=.scalar then 0 else bitNat b := by
  unfold portCoordinate
  split_ifs <;> cases b <;> simp_all [bitNat]
  contradiction

theorem gateInput_unit (t : T) (b : Bool) (k : Fin 2) :
    (gateInput C (ZMod p) t b (unit2 (ZMod p) (gateDim C t) k)).val=
      if k.val=(kinds C)[(FiniteCode.equiv t).val]?.getD 0*bitNat b then 1 else 0 := by
  change ((LinearMap.proj (portCoordinate C t b) : (Fin (gateDim C t)→ZMod p)→ₗ[ZMod p] ZMod p)
    (unit2 (ZMod p) (gateDim C t) k)).val=_
  rw [proj_unit2,portCoordinate_value,kind_read]
  simp only [Equiv.symm_apply_apply]
  by_cases h : C.kind t=.scalar <;> simp [h]

theorem gateOutput_unit (t : T) (k : Fin 2) :
    (CircuitComparisons.gateOutput C (ZMod p) t (unit2 (ZMod p) (gateDim C t) k)).val=
      (ofCircuit C).gateOutput (FiniteCode.equiv t).val k.val := by
  have hp : 1<p := (Fact.out : p.Prime).one_lt
  change _=if k.val=0 then 1 else (kinds C)[(FiniteCode.equiv t).val]?.getD 0
  rw [kind_read]
  simp only [Equiv.symm_apply_apply]
  unfold CircuitComparisons.gateOutput
  by_cases h : C.kind t=.scalar
  · rw [if_pos h,gateInput_unit,kind_read]
    simp only [Equiv.symm_apply_apply,h,↓reduceIte,bitNat,zero_mul]
  · rw [if_neg h]
    change ((if (portCoordinate C t false).val=k.val then (1:ZMod p) else 0)+
      (if (portCoordinate C t true).val=k.val then 1 else 0)).val=_
    rw [portCoordinate_value,portCoordinate_value]
    simp only [h,↓reduceIte,bitNat]
    fin_cases k <;> simp [ZMod.val_one,Nat.mod_eq_of_lt hp]

theorem connection_sourceForm (e : Connection C) (k : Fin 2) :
    (ofCircuit C).connectionSourceForm (FiniteCode.equiv e).val k.val=
      (e.sourceForm C (ZMod p) (unit2 (ZMod p) (primaryDim C (e.source C)) k)).val := by
  rw [Data.connectionSourceForm,connection_case]
  cases e with
  | circuit i =>
    simp only [connectionKind,connectionIndex,show 0<2 by decide,↓reduceIte,Data.sourceGate,ofCircuit,Data.schemaStride]
    rw [schema_read_source]
    exact (gateOutput_unit C p (C.schema i).source k).symm
  | test i =>
    simp only [connectionKind,connectionIndex,show 1<2 by decide,show ¬(1=0) by decide,↓reduceIte,Data.sourceGate,ofCircuit,Data.requestStride]
    rw [testRecords,request_read_gate C.test i]
    exact (gateOutput_unit C p (C.test i).gate k).symm
  | identity t j =>
    simp only [connectionKind,connectionIndex,show ¬4<2 by decide,↓reduceIte,ofCircuit]
    simp only [packed_read,Option.getD_some]
    exact (proj_unit2 p _ j k).symm
  | flip i => exact (proj_unit2 p 1 0 k).symm
  | broadcast t j => exact (proj_unit2 p 1 0 k).symm
  | broadcastIdentity b => exact (proj_unit2 p 1 0 k).symm

theorem connection_targetForm (e : Connection C) (k : Fin 2) :
    (ofCircuit C).connectionTargetForm (FiniteCode.equiv e).val k.val=
      (e.targetForm C (ZMod p) (unit2 (ZMod p) (primaryDim C (e.target C)) k)).val := by
  rw [Data.connectionTargetForm,connection_case]
  cases e with
  | circuit i =>
    simp only [connectionKind,connectionIndex,↓reduceIte,ofCircuit,Data.schemaStride]
    simp only [schema_read_target,schema_read_port,Option.getD_some]
    exact (gateInput_unit C p (C.schema i).target (C.schema i).port k).symm
  | test i => exact (proj_unit2 p 1 0 k).symm
  | flip i => exact (proj_unit2 p 1 0 k).symm
  | broadcast t j =>
    simp only [connectionKind,connectionIndex,show ¬(3=0) by decide,show 3=3 ∨ 3=4 by decide,↓reduceIte,ofCircuit]
    simp only [packed_read,Option.getD_some]
    exact (proj_unit2 p _ j k).symm
  | identity t j =>
    simp only [connectionKind,connectionIndex,show ¬(4=0) by decide,show 4=3 ∨ 4=4 by decide,↓reduceIte,ofCircuit]
    simp only [packed_read,Option.getD_some]
    exact (proj_unit2 p _ j k).symm
  | broadcastIdentity b => exact (proj_unit2 p 1 0 k).symm

theorem connection_domain (e : Connection C) (i : Fin r) (a : Fin 2) :
    (ofCircuit C).connectionDomain (FiniteCode.equiv e).val i.val a.val=
      if finTwoEquiv a∈(e.domain C).coordinate i then 1 else 0 := by
  rw [Data.connectionDomain,connection_case]
  cases e with
  | circuit j =>
    simp only [connectionKind,connectionIndex,↓reduceIte,ofCircuit,Data.schemaStride]
    rw [schema_read_domain]
    simp [Connection.domain,bitNat]
  | test j =>
    simp only [connectionKind,connectionIndex,show ¬(1=0) by decide,↓reduceIte,ofCircuit,Data.requestStride]
    rw [testRecords,request_read_domain C.test j i a]
    simp [Connection.domain,bitNat]
  | flip j => simp [connectionKind,connectionIndex,Connection.domain,ProductDomain.full]
  | broadcast t j => simp [connectionKind,connectionIndex,Connection.domain,ProductDomain.full]
  | identity t j => simp [connectionKind,connectionIndex,Connection.domain,ProductDomain.full]
  | broadcastIdentity b => simp [connectionKind,connectionIndex,Connection.domain,ProductDomain.full]

theorem connection_permutation (e : Connection C) (i : Fin r) :
    (ofCircuit C).connectionPermutation (FiniteCode.equiv e).val i.val=
      bitNat (e.permutation C i false) := by
  rw [Data.connectionPermutation,connection_case]
  cases e with
  | circuit j =>
    simp only [connectionKind,connectionIndex,↓reduceIte,ofCircuit,Data.schemaStride]
    rw [schema_read_permutation]
    rfl
  | flip j =>
    by_cases h : i=j
    · subst j; simp [connectionKind,connectionIndex,Connection.permutation,bitNat]
    · have hv : i.val≠j.val := fun e=>h (Fin.ext e)
      simp [connectionKind,connectionIndex,Connection.permutation,bitNat,h,hv]
  | test j => rfl
  | broadcast t j => rfl
  | identity t j => rfl
  | broadcastIdentity b => rfl

end GroupWL.CircuitMetadataValues
