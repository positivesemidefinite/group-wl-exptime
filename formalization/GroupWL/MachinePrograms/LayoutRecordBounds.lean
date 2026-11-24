import GroupWL.MachinePrograms.LayoutRecordPrograms
import GroupWL.MachinePrograms.LayoutIncidenceBounds

/-! Uniform polynomial bounds for every source-record construction stage. -/
namespace GroupWL.MachinePrograms.LayoutRecordPrograms
open NatArrayLanguage LayoutMetadata
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 65536
set_option maxRecDepth 32768
def budget (C : ComparisonMetadata.Table) (L : ℕ) := 40*(LayoutIncidencePrograms.magnitude C L)^3

theorem budget_room (C : ComparisonMetadata.Table) (L : ℕ) (valid : LayoutIncidencePrograms.Valid C) :
    LayoutIncidencePrograms.Room C L (budget C L) ∧ 4*C.coordinates≤budget C L ∧
    2*(squareFlags C L).length≤budget C L ∧ 2*linkCount C L≤budget C L ∧
    horizontalCount C L+squareCount C L≤budget C L := by
  have old := LayoutIncidencePrograms.room_budget C L valid
  obtain ⟨h1,_,_,hl,hnr,hlr⟩ := LayoutIncidencePrograms.magnitude_bounds C L
  have h13 : LayoutIncidencePrograms.magnitude C L≤(LayoutIncidencePrograms.magnitude C L)^3 := by
    simpa using Nat.pow_le_pow_right h1 (by decide : 1≤3)
  have h23 : (LayoutIncidencePrograms.magnitude C L)^2≤(LayoutIncidencePrograms.magnitude C L)^3 :=
    Nat.pow_le_pow_right h1 (by decide)
  have hr : C.coordinates≤LayoutIncidencePrograms.magnitude C L := by unfold LayoutIncidencePrograms.magnitude;omega
  have hh := FilterRanks.count_le (LayoutFlagPrograms.horizontal_binary C L valid.domainBinary) (horizontalFlags C L).length
  have hs := FilterRanks.count_le (LayoutFlagPrograms.square_binary C L valid.domainBinary) (squareFlags C L).length
  change horizontalCount C L≤(horizontalFlags C L).length at hh
  change squareCount C L≤(squareFlags C L).length at hs
  simp only [horizontalFlags,squareFlags,List.length_ofFn] at hh hs ⊢
  rcases old with ⟨a,b,c,d,e,f,g⟩
  unfold LayoutIncidencePrograms.budget at a b c d e f g
  unfold budget
  exact ⟨⟨by omega,by omega,by omega,by omega,by omega,by omega,by omega⟩,
    by omega,by omega,by omega,by omega⟩

theorem program_runs_polynomial (C : ComparisonMetadata.Table) (L q : ℕ) (S : State)
    (bounded : S.Bounded (budget C L)) (input : LayoutIncidencePrograms.Input C L S.left.left)
    (source : S.left.right.right.left.left.array .forms=C.sourceForm)
    (target : S.left.right.right.right.left.array .forms=C.targetForm)
    (dimensions : S.right.left.left.left.array .input=C.dimensions)
    (special : S.right.right.left.scalar .special=q) (qbound : q≤C.comparisons)
    (valid : LayoutIncidencePrograms.Valid C) (positive : 0<L) (width : 0<C.coordinates)
    (sourceLength : C.sourceForm.length=2*C.comparisons) (targetLength : C.targetForm.length=2*C.comparisons) :
    ∃t≤80500*(LayoutIncidencePrograms.magnitude C L)^3,∃T,
      Runs (storageBound Reg Arr (budget C L)) program S t T ∧ T.Bounded (budget C L) ∧ Output C L q T := by
  obtain ⟨room,copies,size,links,blocks⟩ := budget_room C L valid
  obtain ⟨t,ht,T,run,hT,hout⟩ := program_runs C L q (budget C L) S bounded input source target dimensions special
    qbound valid room positive copies size links blocks width sourceLength targetLength
  have h1 := (LayoutIncidencePrograms.magnitude_bounds C L).1
  have h13 : LayoutIncidencePrograms.magnitude C L≤(LayoutIncidencePrograms.magnitude C L)^3 := by
    simpa using Nat.pow_le_pow_right h1 (by decide : 1≤3)
  unfold budget at ht
  exact ⟨t,by omega,T,run,hT,hout⟩

end GroupWL.MachinePrograms.LayoutRecordPrograms
