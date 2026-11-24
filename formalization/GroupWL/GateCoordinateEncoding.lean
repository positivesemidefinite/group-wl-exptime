import GroupWL.CircuitComparisonCodes
import GroupWL.MachinePrograms.GateCandidates
import GroupWL.MachinePrograms.SelectArraySemantics

/-! The packed gate-coordinate arrays use the canonical dependent finite code. -/
namespace GroupWL.CircuitComparisonCodes
open CircuitComparisons AddressedCircuit CircuitDescription MachinePrograms
open NatArrayLowering (bitNat)
open scoped BigOperators
set_option maxHeartbeats 2000000
variable {T : Type} [FiniteCode T] {r : ℕ} (C : Circuit T r)

def kinds : List ℕ := (kindWord C).map bitNat
def dimensions : List ℕ := List.ofFn (fun i : Fin (FiniteCode.size T) =>
  gateDim C (FiniteCode.equiv.symm i))
def candidates (f : GateCandidates.Field) : List ℕ :=
  List.ofFn (fun i : Fin (2*FiniteCode.size T) => GateCandidates.value (kinds C) i f)
def packed (f : GateCandidates.Field) : List ℕ :=
  SelectArray.selectedPrefix (candidates C .flag) (candidates C f) (2*FiniteCode.size T)

@[simp] theorem kinds_length : (kinds C).length=FiniteCode.size T := by simp [kinds,kindWord]
@[simp] theorem candidates_length (f : GateCandidates.Field) : (candidates C f).length=2*FiniteCode.size T := by simp [candidates]

theorem kinds_binary : ∀x∈kinds C,x≤1 := by
  intro x hx
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx
  cases b <;> simp [bitNat]

theorem kind_read (i : Fin (FiniteCode.size T)) :
    (kinds C)[i.val]?.getD 0 = if C.kind (FiniteCode.equiv.symm i)=.scalar then 0 else 1 := by
  simp only [kinds,kindWord,List.map_ofFn,Function.comp_def,List.getElem?_ofFn,dif_pos i.isLt,Option.getD_some]
  cases C.kind (FiniteCode.equiv.symm i) <;> simp [bitNat]

theorem dimension_eq_kind (i : Fin (FiniteCode.size T)) :
    gateDim C (FiniteCode.equiv.symm i)=1+(kinds C)[i.val]?.getD 0 := by
  rw [kind_read]
  unfold gateDim
  split_ifs <;> rfl

theorem candidate_read (f : GateCandidates.Field) (i : Fin (FiniteCode.size T)) (k : Fin 2) :
    (candidates C f)[2*i.val+k.val]?.getD 0=
      match f with
      | .flag => 1-k.val+k.val*(kinds C)[i.val]?.getD 0
      | .owner => i.val
      | .port => k.val := by
  have hi : 2*i.val+k.val<2*FiniteCode.size T := by omega
  have hd : (2*i.val+k.val)/2=i.val := by omega
  have hm : (2*i.val+k.val)%2=k.val := by omega
  cases f <;> simp [candidates,List.getElem?_ofFn,hi,GateCandidates.value,hd,hm]

theorem flags_binary : ∀x∈candidates C .flag,x≤1 := by
  intro x hx
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  have hi : i.val/2<FiniteCode.size T := by omega
  have hk : i.val%2<2 := Nat.mod_lt _ (by decide)
  have hv := candidate_read C .flag ⟨i.val/2,hi⟩ ⟨i.val%2,hk⟩
  have hp : 2*(i.val/2)+i.val%2=i.val := by omega
  rw [hp] at hv
  have he : (candidates C .flag)[i.val]?.getD 0=GateCandidates.value (kinds C) i .flag := by
    simp [candidates,List.getElem?_ofFn,i.isLt]
  rw [he] at hv
  have hb := FilterRanks.read_le_one (kinds_binary C) (i.val/2)
  have hcase : i.val%2=0 ∨ i.val%2=1 := by omega
  rcases hcase with h | h <;> rw [hv] <;> simp [h] <;> omega

theorem count_pairs (i : ℕ) (hi : i≤FiniteCode.size T) :
    FilterRanks.count (candidates C .flag) (2*i)=FilterRanks.count (dimensions C) i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have lt : i<FiniteCode.size T := by omega
    have a := candidate_read C .flag ⟨i,lt⟩ 0
    have b := candidate_read C .flag ⟨i,lt⟩ 1
    simp only [Fin.val_zero,Nat.add_zero,Nat.sub_zero,Nat.zero_mul,Fin.val_one,Nat.sub_self,Nat.one_mul,Nat.zero_add] at a b
    have hd : (dimensions C)[i]?.getD 0=gateDim C (FiniteCode.equiv.symm ⟨i,lt⟩) := by
      simp [dimensions,List.getElem?_ofFn,lt]
    calc
      _ = FilterRanks.count (candidates C .flag) (2*i)+1+(kinds C)[i]?.getD 0 := by
        rw [show 2*(i+1)=2*i+1+1 by omega,FilterRanks.count,FilterRanks.count,a,b]
      _ = FilterRanks.count (dimensions C) i+gateDim C (FiniteCode.equiv.symm ⟨i,lt⟩) := by
        rw [ih (by omega),dimension_eq_kind]
        simp only [Fin.val_mk,Nat.add_assoc]
      _ = FilterRanks.count (dimensions C) (i+1) := by rw [FilterRanks.count,hd]

theorem portCount_eq_count : portCount C=FilterRanks.count (dimensions C) (FiniteCode.size T) := by
  unfold dimensions
  rw [FilterRanks.count_ofFn _ _ le_rfl]
  rfl

theorem selected_count : FilterRanks.count (candidates C .flag) (2*FiniteCode.size T)=portCount C := by
  rw [count_pairs C _ le_rfl,portCount_eq_count]

theorem port_code (t : T) (k : Fin (gateDim C t)) :
    (FiniteCode.equiv (⟨t,k⟩ : gatePorts C)).val=
      FilterRanks.count (dimensions C) (FiniteCode.equiv t).val+k.val := by
  unfold dimensions
  rw [FilterRanks.count_ofFn _ _ (Nat.le_of_lt (FiniteCode.equiv t).isLt)]
  let e := FiniteCode.equiv (α:=T)
  have hs : ((Equiv.sigmaCongrLeft (β:=fun t => Fin (gateDim C t)) e.symm).symm ⟨t,k⟩).snd.val=k.val := by
    have castval {a b : T} (h : a=b) (x : Fin (gateDim C a)) :
        ((h ▸ x) : Fin (gateDim C b)).val=x.val := by cases h; rfl
    change (((e.symm_apply_apply t).symm ▸ k) : Fin (gateDim C (e.symm (e t)))).val=k.val
    exact castval _ _
  simp only [FiniteCode.equiv,Equiv.trans_apply,Equiv.sigmaCongrRight_apply,finSigmaFinEquiv_apply]
  change (∑ x : Fin (e t).val,gateDim C (e.symm (Fin.castLE _ x)))+
    ((Equiv.sigmaCongrLeft (β:=fun t => Fin (gateDim C t)) e.symm).symm ⟨t,k⟩).snd.val=_
  rw [hs]
  rfl

theorem packed_length (f : GateCandidates.Field) : (packed C f).length=portCount C := by
  rw [packed,SelectArray.selectedPrefix_length _ _ (flags_binary C),selected_count]

theorem packed_read (t : T) (k : Fin (gateDim C t)) (f : GateCandidates.Field) :
    (packed C f)[(FiniteCode.equiv (⟨t,k⟩ : gatePorts C)).val]?=
      some (match f with | .flag=>1 | .owner=>(FiniteCode.equiv t).val | .port=>k.val) := by
  let i := FiniteCode.equiv t
  have hi : i.val<FiniteCode.size T := i.isLt
  have dim : gateDim C t≤2 := by unfold gateDim; split_ifs <;> omega
  have hk : k.val<2 := lt_of_lt_of_le k.isLt dim
  have kcase : k.val=0 ∨ k.val=1 := by omega
  have hd := dimension_eq_kind C i
  simp only [i,Equiv.symm_apply_apply] at hd
  have hf := candidate_read C .flag i ⟨k.val,hk⟩
  have chosen : (candidates C .flag)[2*i.val+k.val]?.getD 0=1 := by
    rw [hf]
    change 1-k.val+k.val*(kinds C)[i.val]?.getD 0=1
    rcases kcase with h | h
    · simp only [h,Nat.sub_zero,Nat.zero_mul,Nat.add_zero]
    · simp only [h,Nat.sub_self,Nat.one_mul,Nat.zero_add]
      have kl := k.isLt
      have hb := FilterRanks.read_le_one (kinds_binary C) i.val
      change gateDim C t=1+(kinds C)[i.val]?.getD 0 at hd
      omega
  have hc : FilterRanks.count (candidates C .flag) (2*i.val+k.val)=
      FilterRanks.count (dimensions C) i.val+k.val := by
    rcases kcase with h | h
    · simp only [h,Nat.add_zero]; exact count_pairs C i.val (Nat.le_of_lt hi)
    · rw [h,FilterRanks.count,count_pairs C i.val (Nat.le_of_lt hi)]
      have hz := candidate_read C .flag i 0
      simpa using congrArg (fun x => FilterRanks.count (dimensions C) i.val+x) hz
  have read := SelectArray.selectedPrefix_read (candidates C .flag) (candidates C f)
    (flags_binary C) (2*FiniteCode.size T) (2*i.val+k.val) (by omega) chosen
  rw [hc,←port_code C t k] at read
  rw [candidate_read C f i ⟨k.val,hk⟩] at read
  cases f with
  | flag =>
    have hh : 1-k.val+k.val*(kinds C)[i.val]?.getD 0=1 := hf.symm.trans chosen
    simpa only [packed,Fin.val_mk,hh] using read
  | owner => exact read
  | port => exact read

end GroupWL.CircuitComparisonCodes
