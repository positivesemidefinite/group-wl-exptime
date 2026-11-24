import GroupWL.MachinePrograms.LayoutIncidencePrograms

/-! A uniform cubic bound for the whole incidence preprocessing program. -/
namespace GroupWL.MachinePrograms.LayoutIncidencePrograms
open NatArrayLanguage LayoutMetadata
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 16384
set_option maxRecDepth 8192

def magnitude (C : ComparisonMetadata.Table) (L : ℕ) : ℕ :=
  C.types+C.comparisons+L+C.coordinates+1
def budget (C : ComparisonMetadata.Table) (L : ℕ) : ℕ := 20*(magnitude C L)^3

theorem magnitude_bounds (C : ComparisonMetadata.Table) (L : ℕ) :
    1≤magnitude C L ∧ L+1≤magnitude C L ∧
    nodeCount C L≤2*(magnitude C L)^2 ∧ linkCount C L≤3*(magnitude C L)^2 ∧
    nodeCount C L*C.coordinates≤2*(magnitude C L)^3 ∧
    linkCount C L*C.coordinates≤3*(magnitude C L)^3 := by
  let B := magnitude C L
  have h1 : 1≤B := by unfold B magnitude;omega
  have ht : C.types≤B := by unfold B magnitude;omega
  have he : C.comparisons≤B := by unfold B magnitude;omega
  have hl : L+1≤B := by unfold B magnitude;omega
  have hr : C.coordinates≤B := by unfold B magnitude;omega
  have h12 : B≤B^2 := by simpa using Nat.pow_le_pow_right h1 (by decide : 1≤2)
  have hm := Nat.mul_le_mul he hl
  have hn : nodeCount C L≤2*B^2 := by unfold nodeCount;nlinarith
  have hlinks : linkCount C L≤3*B^2 := by unfold linkCount;nlinarith
  have hnr := Nat.mul_le_mul hn hr
  have hlr := Nat.mul_le_mul hlinks hr
  exact ⟨h1,hl,hn,hlinks,by nlinarith,by nlinarith⟩

theorem room_budget (C : ComparisonMetadata.Table) (L : ℕ) (valid : Valid C) :
    Room C L (budget C L) := by
  obtain ⟨h1,hl,hn,hlinks,hnr,hlr⟩ := magnitude_bounds C L
  have h13 : magnitude C L≤(magnitude C L)^3 := by
    simpa using Nat.pow_le_pow_right h1 (by decide : 1≤3)
  have h23 : (magnitude C L)^2≤(magnitude C L)^3 := Nat.pow_le_pow_right h1 (by decide)
  have hh := FilterRanks.count_le (LayoutFlagPrograms.horizontal_binary C L valid.domainBinary)
    (horizontalFlags C L).length
  have hv := FilterRanks.count_le (LayoutFlagPrograms.link_binary C L valid.domainBinary)
    (linkLabels C L).length
  change horizontalCount C L≤(horizontalFlags C L).length at hh
  change verticalCount C L≤(linkLabels C L).length at hv
  simp only [horizontalFlags,linkLabels,List.length_ofFn] at hh hv
  constructor <;> unfold budget <;> omega

theorem program_runs_polynomial (C : ComparisonMetadata.Table) (L : ℕ) (S : State)
    (bounded : S.Bounded (budget C L)) (input : Input C L S) (valid : Valid C) (positive : 0<L) :
    ∃t≤4000*(magnitude C L)^3,∃T,
      Runs (storageBound Reg Arr (budget C L)) program S t T ∧
      T.Bounded (budget C L) ∧ Output C L T := by
  obtain ⟨t,ht,T,run,hT,hout⟩ := program_runs C L (budget C L) S bounded input valid
    (room_budget C L valid) positive
  obtain ⟨h1,_,_,hl,hnr,hlr⟩ := magnitude_bounds C L
  have h13 : magnitude C L≤(magnitude C L)^3 := by
    simpa using Nat.pow_le_pow_right h1 (by decide : 1≤3)
  have h23 : (magnitude C L)^2≤(magnitude C L)^3 := Nat.pow_le_pow_right h1 (by decide)
  exact ⟨t,by omega,T,run,hT,hout⟩

end GroupWL.MachinePrograms.LayoutIncidencePrograms
