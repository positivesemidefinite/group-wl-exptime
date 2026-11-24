import GroupWL.FiniteCodeEnumeration
import GroupWL.MachinePrograms.FilterRanksSemantics

/-! Canonical filtered Boolean codes coincide with dense prefix ranks. -/
namespace GroupWL.FiniteCode
open MachinePrograms
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def boolFlag (s : Finset Bool) (a : Bool) : ℕ := if a∈s then 1 else 0
def boolFlags (s : Finset Bool) : List ℕ := [boolFlag s false,boolFlag s true]
def boolPairFlags (s t : Finset Bool) : List ℕ :=
  [boolFlag s false*boolFlag t false,boolFlag s false*boolFlag t true,
    boolFlag s true*boolFlag t false,boolFlag s true*boolFlag t true]

theorem bool_subtype_size (s : Finset Bool) :
    size {a : Bool // a∈s}=FilterRanks.count (boolFlags s) 2 := by decide +revert

theorem bool_subtype_rank (s : Finset Bool) (a : {a : Bool // a∈s}) :
    (equiv a).val=FilterRanks.count (boolFlags s) (equiv a.val).val := by
  change (((subtypeSet (fun x : Bool => x∈s)).orderIsoOfFin rfl).symm
    (subtypeEquiv (fun x : Bool => x∈s) a)).val=_
  rw [Finset.orderIsoOfFin_symm_apply]
  change (subtypeSet (fun x : Bool => x∈s)).sort.idxOf (equiv a.val)=_
  have hs : (subtypeSet (fun x : Bool => x∈s)).sort=
      (List.finRange 2).filter (fun i => decide (finTwoEquiv i∈s)) := by
    apply (Finset.sortedLT_sort _).eq_of_mem_iff
    · exact ((List.sortedLT_finRange _).pairwise.filter _).sortedLT
    · intro i
      simp [subtypeSet]
      rfl
  rw [hs]
  clear hs
  decide +revert

theorem bool_pair_size (s t : Finset Bool) :
    size ({a : Bool // a∈s}×{b : Bool // b∈t})=FilterRanks.count (boolPairFlags s t) 4 := by decide +revert

theorem bool_pair_rank (s t : Finset Bool) (a : {a : Bool // a∈s}) (b : {b : Bool // b∈t}) :
    (equiv (a,b)).val=FilterRanks.count (boolPairFlags s t) (2*(equiv a.val).val+(equiv b.val).val) := by
  change (equiv b).val+size {b : Bool // b∈t}*(equiv a).val=_
  rw [bool_subtype_rank,bool_subtype_rank,bool_subtype_size]
  decide +revert

end GroupWL.FiniteCode
