import GroupWL.ReductionResourceBounds
import GroupWL.MachinePrograms.ChargedWedgeStage
import GroupWL.MachinePrograms.ChargedBounds

/-! The global Gaussian and both tensor assemblers fit the same circuit workspace. -/
namespace GroupWL.ReductionResourceBounds
open CircuitComparisons CircuitGroupReduction ConstructiveIncidence ConstructiveCoordinates MachinePrograms
set_option synthInstance.maxSize 8192
set_option maxRecDepth 8192
set_option quotPrecheck false
set_option linter.unusedSectionVars false

private theorem chargedInputBounds {s X Z q c p k b : ℕ}
    (hs : 1024≤s) (hx : X≤s^12) (hz : Z≤s^13) (hq : q≤s) (hc : c≤q*q)
    (hp : p≤s) (hk : k≤s^3) (hb : b≤s^3) :
    2+X+Z+q*2+c*2+p+k+b+X*X+X*X*Z≤s^40 := by
  have q1 := constPow hq
  have p1 := constPow hp
  have c2 : c≤s^(1+1) := hc.trans (mulPow q1 q1)
  poly_room

private theorem sharpBudget (s : ℕ) (hs : 2≤s) : s^40*s^40+2≤s^128 :=
  exponentUp hs (addPow hs (mulPow (le_refl (s^40)) (le_refl (s^40))) (constPow hs)) (by decide)

variable {T : Type} [FiniteCode T] {n : ℕ} (C : AddressedCircuit.Circuit T (n+3)) (p : ℕ) [Fact p.Prime]
local notation "q₀" => Parameters.frameWidth (n+3)
local notation "L₀" => wireLength n
local notation "Cmp" => comparisons C (ZMod p)
local notation "A₀" => ComputableSource.affineSystem Cmp (L:=L₀)
local notation "R₀" => ConstructiveSourceTensor.radicalCoordinates Cmp L₀
local notation "S₀" => scale C p
local instance chargedCircuitGateFintype : Fintype T := FiniteCode.fintype T
local instance chargedCircuitBlockFintype : Fintype ((Cmp).Block L₀) := FiniteCode.fintype _
local instance chargedCircuitReadoutFintype : Fintype ((Cmp).Readout L₀) := FiniteCode.fintype _
local instance chargedCircuitBlockDecidableEq : DecidableEq ((Cmp).Block L₀) := (FiniteCode.equiv (α:=(Cmp).Block L₀)).decidableEq
local instance chargedCircuitReadoutDecidableEq : DecidableEq ((Cmp).Readout L₀) := (FiniteCode.equiv (α:=(Cmp).Readout L₀)).decidableEq
local instance chargedCircuitIncidenceCode : FiniteCode (IncidenceTensor.Incidence A₀) := inferInstance
local notation "X₀" => FiniteCode.size (InputIndex A₀ R₀ q₀)
local notation "Z₀" => FiniteCode.size (OutputIndex A₀ R₀ q₀)
local notation "Y₀" => ConstructiveTensor.operatorCoordinates A₀ R₀ q₀
local notation "b₀" => FiniteCode.size ((Cmp).Block L₀)
local notation "pairs₀" => FiniteCode.size (IncidenceTensor.Pair q₀)

theorem charged_assembly_room (v : Refinement.Version) (hq : 0<q₀) :
    let B := S₀^40
    let M := S₀^128
    let w := (Y₀ hq).dimension
    2+X₀+Z₀+q₀*2+pairs₀*2+p+dimension v (n+3)+b₀+X₀*X₀+X₀*X₀*Z₀≤B ∧
      B*B+2≤M ∧ B≤M ∧ X₀+w+(X₀+w)*(X₀+w)+(X₀+w)*(X₀+w)*Z₀≤M := by
  obtain ⟨x,z,_,_,_,_⟩ := chart C p hq
  obtain ⟨_,_,_,q,_,s⟩ := schema C p
  obtain ⟨hl,hp,_⟩ := scale_lower C p
  have base : 1024≤S₀ := by omega
  have h40 : S₀^40≤S₀^40 := le_rfl
  refine ⟨chargedInputBounds base x z q (ChargedAssembly.pairCount_le _) (by omega)
    (dimension_bound C p v) ((source_counts C p).1.trans s),?_,?_,(stage_room C p hq).coefficients⟩
  · exact sharpBudget S₀ (by omega)
  · exact exponentUp (by omega) h40 (by decide)

theorem charged_wedge_room (hq : 0<q₀) : ChargedWedgeStage.Room p A₀ R₀ q₀ hq (S₀^128) := by
  have h := stage_room C p hq
  obtain ⟨_,z,_,_,_,_⟩ := chart C p hq
  have base := (scale_lower C p).1
  exact ⟨h.field,exponentUp (by omega) z (by decide),h.ambient,h.ambientSquare,h.chosenForms,h.wedgeTable⟩

end GroupWL.ReductionResourceBounds
