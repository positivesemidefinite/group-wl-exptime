import GroupWL.MachinePrograms.IncidencePipelineMiddle
import GroupWL.MachinePrograms.DescriptorPipelineBounds

/-! Polynomial trace and storage bounds for the circuit-to-operator computation. -/
namespace GroupWL.MachinePrograms.IncidencePipeline.Middle
open NatArrayLanguage CircuitGroupReduction CircuitComparisons ReductionResourceBounds
open ConstructiveIncidence
set_option quotPrecheck false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 1500000

variable {X : Type} [FiniteCode X] {n : ℕ} (C : AddressedCircuit.Circuit X (n+3)) (p : ℕ) [Fact p.Prime]
local notation "L₀" => wireLength n
local notation "q₀" => Parameters.frameWidth (n+3)
local notation "Cmp" => comparisons C (ZMod p)
local notation "A₀" => ComputableSource.affineSystem Cmp (L:=L₀)
local notation "R₀" => ConstructiveSourceTensor.radicalCoordinates Cmp L₀
local notation "b₀" => FiniteCode.size ((Cmp).Block L₀)
local notation "r₀" => FiniteCode.size ((Cmp).Readout L₀)
local notation "B₀" => scale C p
local notation "N₀" => FiniteCode.size (OldInputIndex A₀ R₀ q₀)

local instance : Fintype X := FiniteCode.fintype X
local instance : Fintype ((Cmp).Block L₀) := FiniteCode.fintype _
local instance : Fintype ((Cmp).Readout L₀) := FiniteCode.fintype _
local instance : DecidableEq ((Cmp).Block L₀) := (FiniteCode.equiv (α:=(Cmp).Block L₀)).decidableEq
local instance : DecidableEq ((Cmp).Readout L₀) := (FiniteCode.equiv (α:=(Cmp).Readout L₀)).decidableEq

theorem circuit_room (hq : 0<q₀) (M : ℕ) (space : B₀^128≤M) : Room p Cmp L₀ q₀ hq M := by
  have s := stage_room C p hq
  have low := (scale_lower C p).2.1
  have base : 1024≤B₀ := (Nat.le_mul_of_pos_right 1024 (Nat.zero_lt_succ p)).trans low
  have b : 1≤B₀ := (by decide : 1≤1024).trans base
  obtain ⟨_,hz,_,_,_,_⟩ := chart C p hq
  have h13 := (Nat.pow_le_pow_right b (by decide : 13≤128)).trans space
  have h26 := (Nat.pow_le_pow_right b (by decide : 26≤128)).trans space
  constructor
  · constructor
    · exact s.recordArithmetic.trans space
    · change b₀*r₀*2≤M
      rw [Nat.mul_comm (b₀*r₀) 2,←Nat.mul_assoc]
      exact s.recordCount.trans space
    · exact s.control.trans space
    · exact (Nat.add_le_add_left (Nat.le_mul_of_pos_left p (by decide : 0<2)) (p*p)).trans (s.field.trans space)
    · exact s.radicalSquare.trans space
    · exact s.radicalTable.trans space
    · exact s.extents.trans space
    · exact s.selectors.trans space
    · exact s.chosenSquare.trans space
  ·
    exact s.framePairs.trans space
  ·
    exact DescriptorPipeline.circuit_room C p M h26
  ·
    exact ⟨s.field.trans space,hz.trans h13,s.ambient.trans space,s.ambientSquare.trans space,
      s.chosenForms.trans space,s.wedgeTable.trans space⟩

private def overhead := Fintype.card SourceCoefficientTable.Reg+Fintype.card SourceCoefficientTable.Arr+
    Fintype.card SourceIncidenceTable.Reg+Fintype.card SourceIncidenceTable.Arr+
    Fintype.card IncidencePipeline.Reg+Fintype.card IncidencePipeline.Arr+
    Fintype.card Indices.Reg+Fintype.card Indices.Arr+
    2*(Fintype.card ArraySlice.Reg+Fintype.card ArraySlice.Arr)+
    Fintype.card DescriptorPipeline.Reg+Fintype.card DescriptorPipeline.Arr+
    Fintype.card ChargedWedgeStage.Reg+Fintype.card ChargedWedgeStage.Arr+
    Fintype.card MatrixArithmetic.Reg+Fintype.card MatrixArithmetic.Arr+
    Fintype.card WedgeKernel.Reg+Fintype.card WedgeKernel.Arr

private theorem overhead_bound : overhead ≤ 100000 := by decide

private theorem time_numeric (p b r n q f w x z desc P : ℕ)
    (coords : IncidencePipeline.time p b r n ≤ P)
    (cells : 2*b*r≤P) (pairs : q*q≤P) (d : desc≤P)
    (forms : f*w*(12*n+9)+7≤P)
    (wedge : w*x*z*(WedgeConstraints.expression.cost+4)+10+220*(w+x*z+p+1)^4≤P) :
    (Descriptors.idxTime p b r n q+(Fintype.card DescriptorPipeline.Reg+Fintype.card DescriptorPipeline.Arr+(1+desc)))+
    (Fintype.card ChargedWedgeStage.Reg+Fintype.card ChargedWedgeStage.Arr+
      ChargedWedgeStage.time p n f w x z) ≤ 1000000*P := by
  have caps := overhead_bound
  unfold overhead at caps
  unfold Descriptors.idxTime prefixTime Records.time Indices.time Indices.trimCost ChargedWedgeStage.time
  rw [show 2*b*r=2*(b*r) by ring] at cells
  omega

theorem circuit_time (hq : 0<q₀) : time p Cmp L₀ q₀ hq≤B₀^132 := by
  have s := stage_room C p hq
  have hl := (scale_lower C p).2.1
  have hb : 1024≤B₀ := by omega
  have h1 : 1≤B₀ := by omega
  let rs := SourceTableEncoding.radicalTable p Cmp L₀
  have length : rs.length=b₀*r₀*b₀ := SourceRadicalTables.collect_length _ _ _ _ _ _ _
  have desc := ((DescriptorPipeline.circuit_cost C p rs length).trans (DescriptorPipeline.circuit_time C p)).trans
    (Nat.pow_le_pow_right h1 (by decide : 27≤128))
  have h := time_numeric p b₀ r₀ N₀ q₀ _ _ _ _ _ _
    s.coordinateTime s.recordCount s.framePairs desc s.formTime s.wedgeTime
  calc
    time p Cmp L₀ q₀ hq ≤ 1000000*(B₀^128) := h
    _ ≤ B₀^4*B₀^128 := Nat.mul_le_mul_right _ ((by decide : 1000000≤1024^4).trans (Nat.pow_le_pow_left hb 4))
    _ = B₀^132 := (pow_add B₀ 4 128).symm

theorem circuit_runs (M : ℕ) (space : B₀^128≤M) (S : State) (bounded : S.Bounded M)
    (input : Records.Input p Cmp L₀ q₀ (readHeader S)) :
    ∃t≤B₀^132,∃U,Runs (storageBound Reg Arr M) (program p) S t U ∧ U.Bounded M ∧
      U.array (headerField .charge)=S.array (headerField .charge) ∧
      Output p Cmp L₀ q₀ (lt_of_lt_of_le (by decide : 0<2) (frameWidth_ge_two (n+3))) U := by
  have hq : 0<q₀ := lt_of_lt_of_le (by decide : 0<2) (frameWidth_ge_two (n+3))
  obtain ⟨t,ht,U,run,b,charge,out⟩ := program_runs p Cmp L₀ q₀ (dimension_le_two C) hq M
    (circuit_room C p hq M space) S bounded input
  exact ⟨t,ht.trans (circuit_time C p hq),U,run,b,charge,out⟩
end GroupWL.MachinePrograms.IncidencePipeline.Middle
