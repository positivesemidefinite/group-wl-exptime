import GroupWL.MachinePrograms.DescriptorPipeline
import GroupWL.ReductionResourceBounds
import GroupWL.SourceInputMetadata

/-! Polynomial workspace for all descriptor and form-matrix passes on circuits. -/
namespace GroupWL.MachinePrograms.DescriptorPipeline
open CircuitGroupReduction CircuitComparisons ReductionResourceBounds
open ConstructiveCoordinates ConstructiveIncidence IncidenceTensor
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 1500000

variable {T : Type} [FiniteCode T] {n : ℕ} (C : AddressedCircuit.Circuit T (n+3)) (p : ℕ) [Fact p.Prime]
local notation "L₀" => wireLength n
local notation "q₀" => Parameters.frameWidth (n+3)
local notation "Cmp" => comparisons C (ZMod p)
local notation "A₀" => ComputableSource.affineSystem Cmp (L:=L₀)
local notation "R₀" => ConstructiveSourceTensor.radicalCoordinates Cmp L₀
local notation "b₀" => FiniteCode.size ((Cmp).Block L₀)
local notation "r₀" => FiniteCode.size ((Cmp).Readout L₀)
local notation "B₀" => scale C p
local notation "N₀" => FiniteCode.size (OldInputIndex A₀ R₀ q₀)
local notation "O₀" => FiniteCode.size (OldOutputIndex A₀ R₀ q₀)
local notation "F₀" => FiniteCode.size (FormIndex A₀ R₀ q₀)

local instance : Fintype T := FiniteCode.fintype T
local instance : Fintype ((Cmp).Block L₀) := FiniteCode.fintype _
local instance : Fintype ((Cmp).Readout L₀) := FiniteCode.fintype _
local instance : DecidableEq ((Cmp).Block L₀) := (FiniteCode.equiv (α:=(Cmp).Block L₀)).decidableEq
local instance : DecidableEq ((Cmp).Readout L₀) := (FiniteCode.equiv (α:=(Cmp).Readout L₀)).decidableEq

private theorem arithmetic {B b r q pairs ni out forms : ℕ}
    (big : 2≤B) (hb : b≤B^3) (hr : r≤B^3) (hq : q≤B^1)
    (hp : pairs≤B^2) (hn : ni≤B^12) (ho : out≤B^12) (hf : forms≤B^14) :
    2 ≤ B^26 ∧ ni+(q+1)*(b+2) ≤ B^26 ∧ ni+q*2+1 ≤ B^26 ∧ forms ≤ B^26 ∧
    (b+r)*pairs*(b+2) ≤ B^26 ∧ out ≤ B^26 ∧ forms*ni ≤ B^26 := by
  exact ⟨by poly_room,by poly_room,by poly_room,by poly_room,by poly_room,by poly_room,mulPow hf hn⟩

theorem circuit_room (M : ℕ) (space : B₀^26 ≤ M) : Room p A₀ R₀ q₀ (b₀+2) M := by
  let horizontal : (Cmp).Horizontal L₀ := ⟨.inl (.inl .broadcast),⟨0,by omega⟩,
    ⟨false,Finset.mem_univ _⟩,⟨false,Finset.mem_univ _⟩⟩
  let block : (Cmp).Block L₀ := .inl horizontal
  let readout : (Cmp).Readout L₀ := .inl horizontal
  have rb : 0 < b₀ := Nat.zero_lt_of_lt (FiniteCode.equiv block).isLt
  have rr : 0 < r₀ := Nat.zero_lt_of_lt (FiniteCode.equiv readout).isLt
  have q2 := frameWidth_ge_two (n+3)
  have qp : 0 < q₀ := by omega
  let ix : OldInputIndex A₀ R₀ q₀ := ⟨.inl block,⟨0,qp⟩,none⟩
  have rn : 0 < N₀ := Nat.zero_lt_of_lt (FiniteCode.equiv ix).isLt
  have dims : ∀v,ringDimension A₀ R₀ v ≤ b₀+1 := by
    intro v
    cases v with
    | inl i => rw [ringDimension_block];omega
    | inr j =>
      rw [ringDimension_readout]
      have dim := SourceTableEncoding.radicalWidth_canonical p Cmp L₀ (dimension_le_two C) j
      have mem : (R₀ j).dimension ∈ SourceTableEncoding.radicalWidths p Cmp L₀ := by
        rw [←dim]; apply List.mem_ofFn.mpr; exact ⟨FiniteCode.equiv j,rfl⟩
      exact Nat.add_le_add_right (SourceTableEncoding.radicalWidths_le p Cmp L₀ _ mem) _
  obtain ⟨_,_,_,hq,_,hs⟩ := schema C p
  obtain ⟨hb,hr⟩ := source_counts C p
  have b := hb.trans hs
  have r := hr.trans hs
  have q1 := constPow hq
  have big := (scale_lower C p).1
  obtain ⟨hx,_,hn,_,_,hf⟩ := chart C p qp
  have ho : O₀ ≤ B₀^12 := (Nat.le_add_left O₀ N₀).trans hx
  have pairN : FiniteCode.size (Pair q₀) ≤ B₀^(1+1) := by
    rw [←FiniteCode.card_eq_size]
    exact (IncidenceSize.card_pair_le q₀).trans (mulPow q1 q1)
  obtain ⟨two,offsets,edgeOffsets,forms,candidates,outputs,matrix⟩ :=
    arithmetic (by omega : 2≤B₀) b r q1 pairN hn ho hf
  refine ⟨q2,by omega,rr,rn,fun v => (dims v).trans (by omega),dims,two.trans space,?_,?_,?_,?_,?_,?_⟩
  · rw [inputTotal_eq];exact offsets.trans space
  · rw [inputTotal_eq];exact edgeOffsets.trans space
  · change N₀ + FiniteCode.size (Incidence A₀)*q₀*2 ≤ M
    have raw : N₀ + FiniteCode.size (Incidence A₀)*(q₀*2) ≤ B₀^26 := forms
    simpa only [Nat.mul_assoc] using raw.trans space
  · exact candidates.trans space
  · exact outputs.trans space
  · exact matrix.trans space

theorem circuit_cost (radicals : List ℕ) (length : radicals.length = b₀*r₀*b₀) :
    cost (layout p A₀ R₀ q₀ (b₀+2) radicals) ≤ coefficient*(B₀^26+1) := by
  exact cost_le _ _ (layout_valid p A₀ R₀ q₀ (b₀+2) radicals _ (circuit_room C p _ le_rfl) length)

theorem circuit_time : coefficient*(B₀^26+1) ≤ B₀^27 := by
  have small : coefficient = 1036 := by decide
  have h := (scale_lower C p).2.1
  have prime := (Fact.out : p.Prime).two_le
  have c : coefficient*2 ≤ B₀ := by rw [small];omega
  have hb : 0 < B₀ := by omega
  have pos : 0 < B₀^26 := pow_pos hb _
  calc
    _ ≤ coefficient*(2*B₀^26) := Nat.mul_le_mul_left _ (by omega)
    _ = (coefficient*2)*B₀^26 := (Nat.mul_assoc _ _ _).symm
    _ ≤ B₀*B₀^26 := Nat.mul_le_mul_right _ c
    _ = _ := (Nat.mul_comm _ _).trans (pow_succ B₀ 26).symm

def circuitLayout := layout p A₀ R₀ q₀ (b₀+2) (SourceTableEncoding.radicalTable p Cmp L₀)

theorem circuit_runs (M : ℕ) (space : B₀^26 ≤ M) (S : State) (bounded : S.Bounded M)
    (input : Input (circuitLayout C p) (inputState S)) :
    ∃t≤B₀^27,∃T,
      NatArrayLanguage.Runs (NatArrayLanguage.storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧
      Input (circuitLayout C p) (inputState T) ∧ CanonicalOutput p A₀ R₀ q₀ T := by
  let rs := SourceTableEncoding.radicalTable p Cmp L₀
  have length : rs.length=b₀*r₀*b₀ := SourceRadicalTables.collect_length _ _ _ _ _ _ _
  have spec := SourceTableEncoding.radicalTable_spec p Cmp L₀ (dimension_le_two C)
  have values : ∀x∈rs,x<p := SourceRadicalTables.collect_values _ _ _ _ _ _ _ (Fact.out : p.Prime).one_lt
  obtain ⟨t,ht,T,run,hT,hI,out⟩ :=
    program_runs p A₀ R₀ q₀ (b₀+2) rs M (circuit_room C p M space) length spec values S bounded input
  exact ⟨t,ht.trans ((circuit_cost C p rs length).trans (circuit_time C p)),T,run,hT,hI,out⟩

end GroupWL.MachinePrograms.DescriptorPipeline
