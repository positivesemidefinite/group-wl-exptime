import GroupWL.MachinePrograms.CircuitTensorPipeline
import GroupWL.MachinePrograms.CircuitFrontBounds
import GroupWL.MachinePrograms.IncidencePipelineMiddleBounds
import GroupWL.ReductionResourceBoundsGlobal

/-! A canonical circuit word in an otherwise empty store produces both original
dense tensors within a polynomial independent of the circuit and its gate type. -/
namespace GroupWL.MachinePrograms.CircuitTensorPipeline
open NatArrayLanguage NatArrayLowering CircuitRecordPipeline IncidencePipeline
open ReductionResourceBounds
set_option synthInstance.maxSize 65536
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000

private noncomputable def frontK := 2*Frontend.time 0 1 1 1
private noncomputable def portA := Fintype.card Middle.Reg+Fintype.card Middle.Arr
private noncomputable def portB := Fintype.card ChargedAssembly.Reg+Fintype.card ChargedAssembly.Arr
noncomputable def degree := globalDegree Frontend.frontExponent (globalExponent Frontend.frontExponent) 132
noncomputable def coefficient (p : ℕ) :=
  (frontK+portA+portB+Fintype.card ChargedAssembly.R₂+Fintype.card ChargedAssembly.A₂+2)*
    ((1024+WedgeConstraints.expression.cost)*(p+1))^degree

private theorem initial_bounded {U V : Type} [DecidableEq V] (a : V) (w : List Bool) (m : ℕ)
    (h : w.length+1≤m) : (inputStore (Reg:=U) a w).Bounded m := by
  refine ⟨by simp [inputStore],?_,?_⟩
  · intro b
    by_cases hb : b=a <;> simp [inputStore,hb] <;> omega
  · intro b x hx
    by_cases hb : b=a
    · subst b
      simp only [inputStore,Function.update_self,List.mem_map] at hx
      obtain ⟨bit,_,rfl⟩ := hx
      cases bit <;> simp [bitNat] <;> omega
    · simp [inputStore,hb] at hx

theorem canonical_run (p : ℕ) [Fact p.Prime] (v : Refinement.Version)
    {G : Type} [FiniteCode G] [Fintype G] {n : ℕ} (C : AddressedCircuit.Circuit G (n+3)) :
    ∃ m t S, (CircuitDescription.circuitWord C).length+1≤m ∧
      m≤coefficient p*((CircuitDescription.circuitWord C).length+1)^degree ∧
      t≤coefficient p*((CircuitDescription.circuitWord C).length+1)^degree ∧
      Runs (storageBound Reg Arr m) (program p v) (inputStore input (CircuitDescription.circuitWord C)) t S ∧
      S.Bounded m ∧ CircuitWriterReduction.Describes p (output.read S) (ComputableCircuitReduction.baseDescription p C)
        (ComputableCircuitReduction.mateDescription p C) (CircuitGroupReduction.dimension v (n+3)) := by
  let w := CircuitDescription.circuitWord C
  let x := scale C p
  let fe := Frontend.frontExponent
  let d := globalExponent fe
  let M := globalMemory C p fe
  let S : State := inputStore input w
  have hd : fe≤d := Nat.le_max_right _ _
  obtain ⟨_,h128,_,hN⟩ := workspace C p fe
  have bS : S.Bounded M := initial_bounded input w M hN
  have hx := (scale_lower C p).1
  have x1 : 1≤x := by dsimp only [x];omega
  have parseN : w.length+1≤x^4 :=
    (show w.length+1≤x by dsimp only [w,x];omega).trans (Nat.le_self_pow (by decide) _)
  have bSmall : S.Bounded (x^4) := initial_bounded input w _ parseN
  obtain ⟨sub,six,parse,sizes,expression,params,layout⟩ := Frontend.front_room C p d hd
  have raw : S.left.left.array Frontend.inputArray=w.map bitNat := by
    change (inputStore (Reg:=Reg) input w).array input=w.map bitNat
    simp [inputStore]
  let tFront := Frontend.time w.length (FiniteCode.size G) (x^4) M
  have scan := Frontend.program_runs v p C S.left.left (x^4) M bSmall.left.left sub six parse sizes expression params layout raw
  have hq : 0<Parameters.frameWidth (n+3) := lt_of_lt_of_le (by decide : 0<2) (CircuitGroupReduction.frameWidth_ge_two (n+3))
  obtain ⟨capacity,cells,storage,dense⟩ := assembly_room C p v hq fe
  obtain ⟨t,ht,U,run,bU,out⟩ := compose_runs C p v M (ChargedAssembly.writerBase (x^25)) tFront (x^132)
    S bS hq scan (by
      intro W bW read
      obtain ⟨u,hu,Y,rY,bY,_,data⟩ := Middle.circuit_runs C p M h128 W bW read
      exact ⟨u,hu,Y,rY,bY,data⟩) capacity cells storage dense
  have frontTime : tFront≤frontK*x^d := by
    have bound := Frontend.time_bounded C p d hd
    have hplus : x^d+1≤2*x^d := by have hpos : 1≤x^d := one_le_pow₀ x1; omega
    exact bound.trans ((Nat.mul_le_mul_left (Frontend.time 0 1 1 1) hplus).trans_eq (by unfold frontK;ring))
  obtain ⟨space,steps⟩ := full_cost C p hq fe d 132 frontK portA portB tFront (x^132) frontTime (le_refl _)
  exact ⟨M,t,U,hN,space,ht.trans steps,run,bU,out⟩

end GroupWL.MachinePrograms.CircuitTensorPipeline
