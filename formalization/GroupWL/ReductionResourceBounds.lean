import GroupWL.CircuitOutputSize
import GroupWL.CircuitDescription
import GroupWL.MachinePrograms.IncidencePipeline
import GroupWL.WedgeOperatorClient

/-! Uniform resource bounds in the length of the compact addressed-circuit word. -/
namespace GroupWL.ReductionResourceBounds
open CircuitOutputSize CircuitGroupReduction CircuitComparisons
open ConstructiveIncidence ConstructiveCoordinates MachinePrograms
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 8192
set_option quotPrecheck false
theorem mulPow {b x y i j : ℕ} (hx : x ≤ b^i) (hy : y ≤ b^j) :
    x*y ≤ b^(i+j) := (Nat.mul_le_mul hx hy).trans_eq (pow_add b i j).symm

theorem addPow {b x y i j : ℕ} (hb : 2≤b) (hx : x≤b^i) (hy : y≤b^j) :
    x+y ≤ b^(max i j+1) := by
  have h1 : x≤b^(max i j) := hx.trans (pow_le_pow_right' (by omega) (le_max_left _ _))
  have h2 : y≤b^(max i j) := hy.trans (pow_le_pow_right' (by omega) (le_max_right _ _))
  rw [pow_succ]
  have h := Nat.mul_le_mul_left (b^(max i j)) hb
  omega

theorem constPow {b x : ℕ} (hx : x≤b) : x≤b^1 := by simpa
theorem exponentUp {b x i j : ℕ} (hb : 2≤b) (hx : x≤b^i) (he : i≤j) : x≤b^j :=
  hx.trans (pow_le_pow_right' (by omega) he)
theorem natPower {b x i : ℕ} (k : ℕ) (hx : x≤b^i) : x^k ≤ b^(i*k) :=
  (Nat.pow_le_pow_left hx k).trans_eq (pow_mul b i k).symm
open Lean Elab Tactic in
elab "resource_head " n:ident : tactic => do
  let goal ← instantiateMVars (← getMainTarget)
  let lhs := goal.getAppArgs[goal.getAppNumArgs-2]!
  unless lhs.getAppFn.constName? == some n.getId.eraseMacroScopes do
    throwError "unexpected arithmetic operation"

syntax "poly_leaf" : tactic
macro_rules | `(tactic| poly_leaf) => `(tactic| first
  | assumption
  | (resource_head HPow.hPow; apply natPower <;> poly_leaf)
  | (resource_head HMul.hMul; apply mulPow <;> poly_leaf)
  | (resource_head HAdd.hAdd; apply addPow (by omega) <;> poly_leaf)
  | exact constPow (by omega))
macro "poly_room" : tactic => `(tactic|
  exact exponentUp (by omega) (by poly_leaf) (by decide))

variable {T : Type} [FiniteCode T] {n : ℕ} (C : AddressedCircuit.Circuit T (n+3))
def scale (p : ℕ) : ℕ :=
  (1024 + WedgeConstraints.expression.cost)*(p+1)*((CircuitDescription.circuitWord C).length+1)

theorem scale_lower (p : ℕ) :
    1024*((CircuitDescription.circuitWord C).length+1) ≤ scale C p ∧
    1024*(p+1) ≤ scale C p ∧ WedgeConstraints.expression.cost ≤ scale C p := by
  let a := 1024+WedgeConstraints.expression.cost
  let N := (CircuitDescription.circuitWord C).length
  change 1024*(N+1)≤a*(p+1)*(N+1) ∧ 1024*(p+1)≤a*(p+1)*(N+1) ∧ _≤a*(p+1)*(N+1)
  have ha : 1024 ≤ a := by dsimp [a]; omega
  have hm : a ≤ a*(p+1) := by nlinarith
  have hw : a*(p+1) ≤ a*(p+1)*(N+1) := Nat.le_mul_of_pos_right _ (by omega)
  exact ⟨Nat.mul_le_mul_right _ (ha.trans hm),(Nat.mul_le_mul_right _ ha).trans hw,
    (Nat.le_add_left _ _).trans (hm.trans hw)⟩

theorem header :
    FiniteCode.size T + (n+3) + C.edges + C.seedCount + C.testCount + 5 ≤
      (CircuitDescription.circuitWord C).length := by
  simp only [CircuitDescription.circuitWord,List.length_append,CircuitDescription.length_natWord]
  omega

local notation "q₀" => Parameters.frameWidth (n+3)
local notation "L₀" => wireLength n
local notation "s₀" => sourceBound C L₀

theorem schema (p : ℕ) :
    connectionBound C ≤ scale C p ∧ realBound C ≤ scale C p ∧ comparisonBound C ≤ scale C p ∧
    q₀ ≤ scale C p ∧ L₀+2 ≤ scale C p ∧ s₀ ≤ (scale C p)^3 := by
  have h := header C
  have hs := (scale_lower C p).1
  let B := scale C p
  let u := realBound C
  let v := comparisonBound C
  have h4 : 4*(n+3) ≤ B := by dsimp [B]; omega
  have hu : u+2*v ≤ B := by dsimp [u,v,realBound,comparisonBound,connectionBound,B]; omega
  have hL : L₀+2 ≤ B := by dsimp [wireLength,B]; omega
  have hq : q₀ ≤ B := by dsimp [Parameters.frameWidth,B]; omega
  refine ⟨?_,?_,?_,hq,hL,?_⟩
  · dsimp [connectionBound]; omega
  · change u ≤ B; omega
  · change v ≤ B; omega
  · calc
      s₀ ≤ (4*(n+3))*((u+2*v)*(L₀+2)) := by
        change 4*(n+3)*(u+v*(L₀+1))+4*(n+3)*v*(L₀+2) ≤ _
        rw [Nat.mul_assoc (4*(n+3)) v,←Nat.mul_add]
        exact Nat.mul_le_mul_left _ (by nlinarith)
      _ ≤ B*(B*B) := Nat.mul_le_mul h4 (Nat.mul_le_mul hu hL)
      _ = _ := by ring

private theorem coordinateBudgets {B s q : ℕ} (base : 1024 ≤ B) (hs : s≤B^3) (hq : q≤B) :
    coordinateInputBound s q ≤ B^12 ∧ coordinateOutputBound s q ≤ B^13 ∧
      tensorInputBound s q ≤ B^26 := by
  have q1 := constPow hq
  have hi : coordinateInputBound s q ≤ B^12 := by unfold coordinateInputBound; poly_room
  have ho : coordinateOutputBound s q ≤ B^13 := by unfold coordinateOutputBound; poly_room
  exact ⟨hi,ho,by unfold tensorInputBound; poly_room⟩

theorem coordinate_budgets (p : ℕ) :
    coordinateInputBound s₀ q₀ ≤ (scale C p)^12 ∧
    coordinateOutputBound s₀ q₀ ≤ (scale C p)^13 ∧
    tensorInputBound s₀ q₀ ≤ (scale C p)^26 := by
  obtain ⟨_,_,_,hq,_,hs⟩ := schema C p
  have hl := (scale_lower C p).1
  exact coordinateBudgets (by omega) hs hq

variable (p : ℕ) [Fact p.Prime]
local notation "Cmp" => comparisons C (ZMod p)
local notation "A₀" => ComputableSource.affineSystem Cmp (L:=L₀)
local notation "R₀" => ConstructiveSourceTensor.radicalCoordinates Cmp L₀
local notation "X₀" => FiniteCode.size (InputIndex A₀ R₀ q₀)
local notation "Z₀" => FiniteCode.size (OutputIndex A₀ R₀ q₀)
local notation "N₀" => FiniteCode.size (OldInputIndex A₀ R₀ q₀)
local notation "F₀" => FiniteCode.size (FormIndex A₀ R₀ q₀)
local notation "b₀" => FiniteCode.size ((Cmp).Block L₀)
local notation "r₀" => FiniteCode.size ((Cmp).Readout L₀)
local notation "B₀" => scale C p

local instance : Fintype T := FiniteCode.fintype T
local instance : Fintype ((Cmp).Block L₀) := FiniteCode.fintype _
local instance : Fintype ((Cmp).Readout L₀) := FiniteCode.fintype _
local instance : DecidableEq ((Cmp).Block L₀) := (FiniteCode.equiv (α:=(Cmp).Block L₀)).decidableEq
local instance : DecidableEq ((Cmp).Readout L₀) := (FiniteCode.equiv (α:=(Cmp).Readout L₀)).decidableEq

local instance : FiniteCode (IncidenceTensor.Incidence A₀) := inferInstance

theorem source_counts : b₀ ≤ s₀ ∧ r₀ ≤ s₀ := by
  rw [←FiniteCode.card_eq_size,←FiniteCode.card_eq_size]
  constructor
  · simpa only [←Nat.card_eq_fintype_card] using block_card_le C (ZMod p) L₀
  · simpa only [←Nat.card_eq_fintype_card] using readout_card_le C (ZMod p) L₀

private theorem form_budget {B old edges q : ℕ} (hb : 1024≤B) (ho : old≤B^12) (he : edges≤B^6) (hq : q≤B) :
    old + edges*(q*2) ≤ B^14 := by
  have hq1 := constPow hq
  poly_room

private theorem chartGeneral {I J F : Type} [Field F] [DecidableEq F] [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [FiniteCode I] [FiniteCode J]
    {V : J → Type} [∀j, AddCommGroup (V j)] [∀j, Module F (V j)]
    (A : AffineSystem F I J V) (R : ∀j, Coordinates F (IncidenceTensor.ReadoutRadical A j))
    (q B s : ℕ) (hq : 0<q) (base : 1024≤B) (hs : s≤B^3) (hq' : q≤B)
    (bi : Fintype.card I≤s) (ri : Fintype.card J≤s)
    (ci : coordinateInputBound s q≤B^12) (co : coordinateOutputBound s q≤B^13) :
    FiniteCode.size (InputIndex A R q)≤B^12 ∧ FiniteCode.size (OutputIndex A R q)≤B^13 ∧
    FiniteCode.size (OldInputIndex A R q)≤B^12 ∧ (chosenCoordinates A R q hq).dimension≤B^12 ∧
    (ConstructiveTensor.operatorCoordinates A R q hq).dimension≤B^25 ∧ FiniteCode.size (FormIndex A R q)≤B^14 := by
  have xi := (coordinateInputBound_le (q:=q) A bi ri).trans ci
  have zi := (coordinateOutputBound_le (q:=q) A bi ri).trans co
  have x : (FiniteCode.size (InputIndex A R q)) ≤ B^12 :=
    (FiniteCode.card_eq_size (InputIndex A R q)).ge.trans ((ConstructiveTensorSize.input_card_le A R q).trans xi)
  have z : (FiniteCode.size (OutputIndex A R q)) ≤ B^13 :=
    (FiniteCode.card_eq_size (OutputIndex A R q)).ge.trans ((ConstructiveTensorSize.output_card_le A R q).trans zi)
  have old : (FiniteCode.size (OldInputIndex A R q)) ≤ B^12 := (Nat.le_add_right (FiniteCode.size (OldInputIndex A R q)) (FiniteCode.size (OldOutputIndex A R q))).trans x
  have small : (chosenCoordinates A R q hq).dimension ≤ (FiniteCode.size (OldInputIndex A R q)) :=
    Coordinates.kernel_dimension_le (oldInputCoordinates A R q) (Coordinates.pi _) (scalarTests A q hq)
  refine ⟨x,z,old,small.trans old,(ConstructiveTensorSize.operator_dimension_le A R q hq).trans (mulPow xi zi),?_⟩
  have inc : FiniteCode.size (IncidenceTensor.Incidence A) ≤ B^6 := by
    rw [←FiniteCode.card_eq_size]
    exact (IncidenceSize.card_incidence_le A).trans (mulPow (bi.trans hs) (ri.trans hs))
  have q1 := constPow hq'
  change (FiniteCode.size (OldInputIndex A R q)) + FiniteCode.size (IncidenceTensor.Incidence A)*(q*2) ≤ _
  exact form_budget base old inc hq'

theorem chart (hq : 0<q₀) :
    X₀ ≤ B₀^12 ∧ Z₀ ≤ B₀^13 ∧ N₀ ≤ B₀^12 ∧
    (chosenCoordinates A₀ R₀ q₀ hq).dimension ≤ B₀^12 ∧
    (ConstructiveTensor.operatorCoordinates A₀ R₀ q₀ hq).dimension ≤ B₀^25 ∧ F₀ ≤ B₀^14 := by
  obtain ⟨hb,hr⟩ := source_counts C p
  have bi : Fintype.card ((Cmp).Block L₀) ≤ s₀ := (FiniteCode.card_eq_size ((Cmp).Block L₀)).le.trans hb
  have ri : Fintype.card ((Cmp).Readout L₀) ≤ s₀ := (FiniteCode.card_eq_size ((Cmp).Readout L₀)).le.trans hr
  obtain ⟨ci,co,_⟩ := coordinate_budgets C p
  obtain ⟨_,_,_,q,_,s⟩ := schema C p
  have hl := (scale_lower C p).1
  exact chartGeneral A₀ R₀ q₀ B₀ s₀ hq (by omega) s q bi ri ci co

private theorem wordBudget {p s q B n : ℕ} (base : 1024≤B) (hp : p≤B) (hn : n+4≤B)
    (hx : tensorInputBound s q ≤ B^26) (hz : coordinateOutputBound s q ≤ B^13) :
    tensorWordBound p s q ≤ B^68 ∧ tensorWordBound p s q+146*(n+4)^2 ≤ B^72 ∧
    2*tensorWordBound p s q+146*(n+4)^2 ≤ B^72 := by
  have hp1 := constPow hp
  have hn1 := constPow hn
  have h : tensorWordBound p s q ≤ B^68 := by unfold tensorWordBound; poly_room
  exact ⟨h,by poly_room,by poly_room⟩

theorem output_lengths (v : Refinement.Version) (e : Statement.DimensionEncoding) :
    ((ComputableCircuitReduction.baseDescription p C).denseWord p).length ≤ B₀^68 ∧
    ((ComputableCircuitReduction.mateDescription p C).denseWord p).length ≤ B₀^68 ∧
    (ComputableCircuitReduction.identificationOutput p C v e).length ≤ B₀^72 ∧
    (ComputableCircuitReduction.equivalenceOutput p C v e).length ≤ B₀^72 := by
  obtain ⟨_,ho,hi⟩ := coordinate_budgets C p
  obtain ⟨hL,hp,_⟩ := scale_lower C p
  have hN := header C
  obtain ⟨tensor,one,two⟩ := wordBudget (n:=n) (p:=p) (by omega) (by omega) (by omega) hi ho
  exact ⟨(base_word_length_le p C).trans tensor,(mate_word_length_le p C).trans tensor,
    (identification_length_le p C v e).trans one,(equivalence_length_le p C v e).trans two⟩


/-- Numerical contract shared by the incidence table, Gaussian kernel and coefficient writers. -/
structure StageRoom (p b r q n x z chosen y f : ℕ) (M : ℕ) : Prop where
  field : p*p+2*p≤M
  control : 2*b+2≤M
  radicalSquare : b*b≤M
  radicalTable : b*r*b≤M
  extents : (b+r)*(b+2)*q≤M
  selectors : (b+r)*n≤M
  chosenSquare : n*n≤M
  chosenForms : f*chosen≤M
  framePairs : q*q≤M
  recordArithmetic : 6*p+4≤M
  recordCount : 2*b*r≤M
  ambient : x*z≤M
  ambientSquare : (x*z)^2≤M
  wedgeTable : chosen*x*z≤M
  coefficients : (x+y)+(x+y)*(x+y)+(x+y)*(x+y)*z≤M
  zeroTensor : x*x*z≤M
  coordinateTime : IncidencePipeline.time p b r n≤M
  formTime : f*chosen*(12*n+9)+7≤M
  wedgeTime : (chosen*x*z)*(WedgeConstraints.expression.cost+4)+10+220*(chosen+x*z+p+1)^4≤M

private theorem stageRoomOfBounds {B p b r q n x z chosen y f : ℕ} (base : 1024≤B)
    (he : WedgeConstraints.expression.cost≤B) (hp : p≤B) (hb : b≤B^3) (hr : r≤B^3)
    (hq : q≤B) (hn : n≤B^12) (hx : x≤B^12) (hz : z≤B^13) (hc : chosen≤B^12)
    (hy : y≤B^25) (hf : f≤B^14) : StageRoom p b r q n x z chosen y f (B^128) := by
  have hp1 := constPow hp
  have hq1 := constPow hq
  have he1 := constPow he
  constructor <;> first | (unfold IncidencePipeline.time; poly_room) | poly_room

theorem stage_room (hq : 0<q₀) :
    StageRoom p b₀ r₀ q₀ N₀ X₀ Z₀ (chosenCoordinates A₀ R₀ q₀ hq).dimension
      (ConstructiveTensor.operatorCoordinates A₀ R₀ q₀ hq).dimension F₀ (B₀^128) := by
  obtain ⟨x,z,old,chosen,y,f⟩ := chart C p hq
  obtain ⟨b,r⟩ := source_counts C p
  obtain ⟨_,_,_,q,_,s⟩ := schema C p
  obtain ⟨base,field,expr⟩ := scale_lower C p
  exact stageRoomOfBounds (by omega) expr (by omega) (b.trans s) (r.trans s) q old x z chosen y f

theorem dimension_bound (v : Refinement.Version) : dimension v (n+3) ≤ B₀^3 := by
  have hN := header C
  have hl := (scale_lower C p).1
  have hh := constPow (show 146≤B₀ by omega)
  have hr := constPow (show n+3+1≤B₀ by omega)
  exact (dimension_le_quadratic v (n+3)).trans (mulPow hh (natPower 2 hr))

theorem scale_polynomial (d : ℕ) : B₀^d =
    ((1024+WedgeConstraints.expression.cost)*(p+1))^d*((CircuitDescription.circuitWord C).length+1)^d :=
  mul_pow _ _ _

end GroupWL.ReductionResourceBounds
