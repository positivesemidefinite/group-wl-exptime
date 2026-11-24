import GroupWL.ReductionResourceBounds
import GroupWL.MachinePrograms.ChargedBounds

/-! A single workspace for the raw circuit frontend, middle and charged tensor writer. -/
namespace GroupWL.ReductionResourceBounds
open CircuitComparisons CircuitGroupReduction ConstructiveIncidence ConstructiveCoordinates MachinePrograms
set_option synthInstance.maxSize 8192
set_option maxRecDepth 8192
set_option maxHeartbeats 750000
set_option quotPrecheck false
set_option linter.unusedSectionVars false

/-- The charged entry evaluator uses a fixed expression with cost 132. -/
def globalExponent (frontend : ℕ) := max 22000 frontend

def globalDegree (frontend frontTime middleTime : ℕ) :=
  max (globalExponent frontend) (max frontTime middleTime)

private theorem chargedSpace {B : ℕ} (hb : 1024≤B) :
    ChargedAssembly.writerMemory (B^25) ≤ B^22000 := by
  have one : 1≤B^1 := constPow (by omega)
  have two : 2≤B^1 := constPow (by omega)
  have sixteen : 16≤B^1 := constPow (by omega)
  have s : B^25+1 ≤ B^26 := addPow (by omega) (le_refl (B^25)) one
  have base : ChargedAssembly.writerBase (B^25) ≤ B^79 := mulPow sixteen (natPower 3 s)
  have expanded : ChargedAssembly.writerBase (B^25)+2 ≤ B^80 := addPow (by omega) base two
  exact exponentUp (by omega) (natPower 264 expanded) (by decide)

private theorem chargedTime {B : ℕ} (hb : 1024≤B) :
    322*(B^25+1)^3 ≤ B^79 := by
  have one : 1≤B^1 := constPow (by omega)
  have s : B^25+1 ≤ B^26 := addPow (by omega) (le_refl (B^25)) one
  exact mulPow (constPow (show 322≤B by omega)) (natPower 3 s)

variable {T : Type} [FiniteCode T] {n : ℕ} (C : AddressedCircuit.Circuit T (n+3)) (p : ℕ) [Fact p.Prime]
local notation "B₀" => scale C p
local notation "L₀" => wireLength n
local notation "q₀" => Parameters.frameWidth (n+3)
local notation "Cmp" => comparisons C (ZMod p)
local notation "A₀" => ComputableSource.affineSystem Cmp (L:=L₀)
local notation "R₀" => ConstructiveSourceTensor.radicalCoordinates Cmp L₀
local instance : Fintype T := FiniteCode.fintype T
local instance : Fintype ((Cmp).Block L₀) := FiniteCode.fintype _
local instance : Fintype ((Cmp).Readout L₀) := FiniteCode.fintype _
local instance : DecidableEq ((Cmp).Block L₀) := (FiniteCode.equiv (α:=(Cmp).Block L₀)).decidableEq
local instance : DecidableEq ((Cmp).Readout L₀) := (FiniteCode.equiv (α:=(Cmp).Readout L₀)).decidableEq
local instance : FiniteCode (IncidenceTensor.Incidence A₀) := inferInstance

local notation "X₀" => FiniteCode.size (InputIndex A₀ R₀ q₀)
local notation "Z₀" => FiniteCode.size (OutputIndex A₀ R₀ q₀)
local notation "Y₀" => ConstructiveTensor.operatorCoordinates A₀ R₀ q₀
local notation "b₀" => FiniteCode.size ((Cmp).Block L₀)
local notation "pairs₀" => FiniteCode.size (IncidenceTensor.Pair q₀)

def globalMemory (frontend : ℕ) := B₀^(globalExponent frontend)

theorem workspace (frontend : ℕ) :
    B₀^frontend ≤ globalMemory C p frontend ∧ B₀^128 ≤ globalMemory C p frontend ∧
    ChargedAssembly.writerMemory (B₀^25) ≤ globalMemory C p frontend ∧
    (CircuitDescription.circuitWord C).length+1 ≤ globalMemory C p frontend := by
  have hl := (scale_lower C p).1
  have hb : 1024≤B₀ := by omega
  have mono (d : ℕ) (h : d≤globalExponent frontend) : B₀^d ≤ globalMemory C p frontend :=
    pow_le_pow_right' (by omega) h
  have h : 22000 ≤ globalExponent frontend := Nat.le_max_left _ _
  exact ⟨mono _ (Nat.le_max_right _ _),mono _ (by omega),(chargedSpace hb).trans (mono _ h),
    (constPow (by omega)).trans (mono 1 (by omega))⟩

theorem assembly_room (v : Refinement.Version) (hq : 0<q₀) (frontend : ℕ) :
    let k := dimension v (n+3)
    let y := (Y₀ hq).dimension
    let B := ChargedAssembly.writerBase (B₀^25)
    let M := globalMemory C p frontend
    2+X₀+Z₀+q₀*2+pairs₀*2+p+k+b₀+X₀*X₀+X₀*X₀*Z₀≤B ∧
    (B+2)^(2*(ChargedWriter.term.expression ChargedWriter.sizeReg).cost)≤M ∧ B≤M ∧
    (X₀+y)+(X₀+y)*(X₀+y)+(X₀+y)*(X₀+y)*Z₀≤M := by
  obtain ⟨x,z,_,_,y,_⟩ := chart C p hq
  obtain ⟨_,_,_,q,_,s⟩ := schema C p
  obtain ⟨hl,hp,_⟩ := scale_lower C p
  have hb : 1024≤B₀ := by omega
  have up {u d : ℕ} (h : u≤B₀^d) (hd : d≤25) : u≤B₀^25 := exponentUp (by omega) h hd
  have blocks := (source_counts C p).1.trans s
  obtain ⟨args,expr,base,coeff⟩ := ChargedAssembly.room (up x (by decide)) (up z (by decide))
    (up (constPow q) (by decide)) (ChargedAssembly.pairCount_le q₀)
    (up (constPow (show p≤B₀ by omega)) (by decide)) (up (dimension_bound C p v) (by decide))
    (up blocks (by decide)) y
  have hM := (workspace C p frontend).2.2.1
  exact ⟨args,expr.trans hM,base.trans hM,coeff.trans hM⟩

private theorem sumClock {f m c K a b r v z : ℕ} (one : 1≤z) (hf : f≤K*z) (hm : m≤z)
    (hc : c≤r+v+z) : (f+(a+m))+(b+c)≤(K+a+b+r+v+2)*z := by
  have fixed := Nat.le_mul_of_pos_right (a+b+r+v) one
  rw [show K+a+b+r+v+2=K+(a+b+r+v)+2 by omega, Nat.add_mul, Nat.add_mul]
  omega

/-- Composition with arbitrary fixed port counts and a polynomial frontend time. -/
theorem full_cost (hq : 0<q₀) (frontend frontDegree middleDegree frontK portA portB ft mt : ℕ)
    (front : ft≤frontK*B₀^frontDegree) (middle : mt≤B₀^middleDegree) :
    let e := globalDegree frontend frontDegree middleDegree
    let K := frontK+portA+portB+Fintype.card ChargedAssembly.R₂+Fintype.card ChargedAssembly.A₂+2
    let length := (CircuitDescription.circuitWord C).length
    let coeff := K*((1024+WedgeConstraints.expression.cost)*(p+1))^e
    globalMemory C p frontend ≤ coeff*(length+1)^e ∧
    (ft+(portA+mt))+(portB+ChargedAssembly.cost (X₀*X₀*Z₀) ((X₀+(Y₀ hq).dimension)*(X₀+(Y₀ hq).dimension)*Z₀))
      ≤ coeff*(length+1)^e := by
  let e := globalDegree frontend frontDegree middleDegree
  let K := frontK+portA+portB+Fintype.card ChargedAssembly.R₂+Fintype.card ChargedAssembly.A₂+2
  have hl := (scale_lower C p).1
  have hb : 1024 ≤ B₀ := by omega
  have one : 1≤B₀^e := one_le_pow₀ (by omega)
  have mono {i : ℕ} (h : i≤e) : B₀^i≤B₀^e := pow_le_pow_right' (by omega) h
  have he : globalExponent frontend≤e := Nat.le_max_left _ _
  have hf : frontDegree≤e := (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hm : middleDegree≤e := (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have e79 : 79≤e := (show 79≤globalExponent frontend from (by unfold globalExponent; omega)).trans he
  have mem : globalMemory C p frontend ≤ K*B₀^e :=
    (mono he).trans (Nat.le_mul_of_pos_left _ (by dsimp [K]; omega))
  have ft' := front.trans (Nat.mul_le_mul_left _ (mono hf))
  have mt' := middle.trans (mono hm)
  obtain ⟨x,z,_,_,y,_⟩ := chart C p hq
  have cost := ChargedAssembly.time_bound (exponentUp (by omega) x (by decide : 12≤25))
    (exponentUp (by omega) z (by decide : 13≤25)) y
  have ct := (chargedTime hb).trans (mono e79)
  have total : (ft+(portA+mt))+(portB+ChargedAssembly.cost (X₀*X₀*Z₀)
      ((X₀+(Y₀ hq).dimension)*(X₀+(Y₀ hq).dimension)*Z₀)) ≤ K*B₀^e :=
    sumClock one ft' mt' (cost.trans (Nat.add_le_add_left ct _))
  have expand : K*B₀^e = (K*((1024+WedgeConstraints.expression.cost)*(p+1))^e)*
      ((CircuitDescription.circuitWord C).length+1)^e := by
    rw [scale_polynomial C p e, Nat.mul_assoc]
  exact ⟨mem.trans_eq expand,total.trans_eq expand⟩

end GroupWL.ReductionResourceBounds
