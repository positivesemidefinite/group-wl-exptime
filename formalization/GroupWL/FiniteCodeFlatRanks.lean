import GroupWL.FiniteCodeRanks
import GroupWL.MachinePrograms.FilterRanksSemantics

/-! Dense ranks of fixed-width candidate blocks agree with the canonical
sigma code whenever each filtered fibre uses its own dense rank. -/
namespace GroupWL.FiniteCode
open MachinePrograms
open scoped BigOperators
variable {α : Type*} {β : α → Type*} [FiniteCode α] [∀a,FiniteCode (β a)]

theorem sigma_flat_rank (width : ℕ) (flags : List ℕ) (localFlags : α → List ℕ)
    (key : ∀a,β a → ℕ)
    (hread : ∀a j,j<width → flags[(equiv a).val*width+j]?.getD 0=(localFlags a)[j]?.getD 0)
    (hsize : ∀a,size (β a)=FilterRanks.count (localFlags a) width)
    (hrank : ∀a b,(equiv b).val=FilterRanks.count (localFlags a) (key a b))
    (hkey : ∀a b,key a b≤width) (a : α) (b : β a) :
    (equiv (α:=Σa,β a) ⟨a,b⟩).val=FilterRanks.count flags ((equiv a).val*width+key a b) := by
  rw [sigma_val,FilterRanks.count_blocks]
  congr 1
  · calc
      (∑ i : Fin (equiv a).val,size (β ((equiv (α:=α)).symm ⟨i.val,i.isLt.trans (equiv a).isLt⟩)))=
          ∑i : Fin (equiv a).val,∑j∈Finset.range width,flags[i.val*width+j]?.getD 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hsize,FilterRanks.count_eq_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have h := hread ((equiv (α:=α)).symm ⟨i.val,i.isLt.trans (equiv a).isLt⟩) j (Finset.mem_range.mp hj)
        simpa only [Equiv.apply_symm_apply] using h.symm
      _=∑i∈Finset.range (equiv a).val,∑j∈Finset.range width,flags[i*width+j]?.getD 0 :=
        Fin.sum_univ_eq_sum_range (fun i => ∑j∈Finset.range width,flags[i*width+j]?.getD 0) (equiv a).val
  · rw [hrank,FilterRanks.count_eq_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact (hread a j ((Finset.mem_range.mp hj).trans_le (hkey a b))).symm

theorem sigma_flat_size (width : ℕ) (flags : List ℕ) (localFlags : α → List ℕ)
    (hread : ∀a j,j<width → flags[(equiv a).val*width+j]?.getD 0=(localFlags a)[j]?.getD 0)
    (hsize : ∀a,size (β a)=FilterRanks.count (localFlags a) width) :
    size (Σa,β a)=FilterRanks.count flags (size α*width) := by
  change (∑i : Fin (size α),size (β ((equiv (α:=α)).symm i)))=_
  rw [FilterRanks.count_eq_sum,FilterRanks.sum_range_blocks]
  rw [←Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hsize,FilterRanks.count_eq_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have h := hread ((equiv (α:=α)).symm i) j (Finset.mem_range.mp hj)
  simpa only [Equiv.apply_symm_apply] using h.symm

section Nested
variable {r : ℕ} {γ : α → Fin r → Type*} [∀a i,FiniteCode (γ a i)]

def blockFlags (flags : List ℕ) (width offset : ℕ) : List ℕ :=
  List.ofFn (fun j : Fin width => flags[offset+j.val]?.getD 0)

theorem blockFlags_read (flags : List ℕ) (width offset j : ℕ) (hj : j<width) :
    (blockFlags flags width offset)[j]?.getD 0=flags[offset+j]?.getD 0 := by
  simp only [blockFlags,List.getElem?_ofFn,dif_pos hj,Option.getD_some]

theorem nested_flat_rank (width : ℕ) (flags : List ℕ) (localFlags : ∀a,Fin r → List ℕ)
    (key : ∀a i,γ a i → ℕ)
    (hread : ∀a i j,j<width → flags[((equiv a).val*r+i.val)*width+j]?.getD 0=(localFlags a i)[j]?.getD 0)
    (hsize : ∀a i,size (γ a i)=FilterRanks.count (localFlags a i) width)
    (hrank : ∀a i b,(equiv b).val=FilterRanks.count (localFlags a i) (key a i b))
    (hkey : ∀a i b,key a i b≤width) (a : α) (i : Fin r) (b : γ a i) :
    (equiv (α:=Σa,Σi,γ a i) ⟨a,i,b⟩).val=
      FilterRanks.count flags (((equiv a).val*r+i.val)*width+key a i b) := by
  let blocks := fun (a : α) => blockFlags flags (r*width) ((equiv a).val*(r*width))
  have reads (a : α) (i : Fin r) (j : ℕ) (hj : j<width) :
      (blocks a)[(equiv i).val*width+j]?.getD 0=(localFlags a i)[j]?.getD 0 := by
    have hi : i.val*width+j<r*width := by
      have h := Nat.mul_le_mul_right width (Nat.succ_le_of_lt i.isLt)
      nlinarith
    dsimp only [blocks]
    rw [show (equiv i).val=i.val from rfl,blockFlags_read _ _ _ _ hi]
    have he : (equiv a).val*(r*width)+(i.val*width+j)=((equiv a).val*r+i.val)*width+j := by ring
    rw [he]
    exact hread a i j hj
  have sizes (a : α) : size (Σi,γ a i)=FilterRanks.count (blocks a) (r*width) :=
    sigma_flat_size width (blocks a) (localFlags a) (reads a) (hsize a)
  have ranks (a : α) (z : Σi,γ a i) :
      (equiv z).val=FilterRanks.count (blocks a) (z.1.val*width+key a z.1 z.2) :=
    sigma_flat_rank width (blocks a) (localFlags a) (key a) (reads a) (hsize a) (hrank a) (hkey a) z.1 z.2
  have bounds (a : α) (z : Σi,γ a i) : z.1.val*width+key a z.1 z.2≤r*width := by
    have h := Nat.mul_le_mul_right width (Nat.succ_le_of_lt z.1.isLt)
    have := hkey a z.1 z.2
    nlinarith
  have h := sigma_flat_rank (r*width) flags blocks (fun a z => z.1.val*width+key a z.1 z.2)
    (fun a j hj => (blockFlags_read flags _ _ j hj).symm) sizes ranks bounds a ⟨i,b⟩
  convert h using 1 <;> congr 1 <;> ring

theorem nested_flat_size (width : ℕ) (flags : List ℕ) (localFlags : ∀a,Fin r → List ℕ)
    (hread : ∀a i j,j<width → flags[((equiv a).val*r+i.val)*width+j]?.getD 0=(localFlags a i)[j]?.getD 0)
    (hsize : ∀a i,size (γ a i)=FilterRanks.count (localFlags a i) width) :
    size (Σa,Σi,γ a i)=FilterRanks.count flags (size α*r*width) := by
  let blocks := fun (a : α) => blockFlags flags (r*width) ((equiv a).val*(r*width))
  have reads (a : α) (i : Fin r) (j : ℕ) (hj : j<width) :
      (blocks a)[(equiv i).val*width+j]?.getD 0=(localFlags a i)[j]?.getD 0 := by
    have hi : i.val*width+j<r*width := by
      have h := Nat.mul_le_mul_right width (Nat.succ_le_of_lt i.isLt)
      nlinarith
    dsimp only [blocks]
    rw [show (equiv i).val=i.val from rfl,blockFlags_read _ _ _ _ hi]
    have he : (equiv a).val*(r*width)+(i.val*width+j)=((equiv a).val*r+i.val)*width+j := by ring
    rw [he]
    exact hread a i j hj
  have sizes (a : α) : size (Σi,γ a i)=FilterRanks.count (blocks a) (r*width) :=
    sigma_flat_size width (blocks a) (localFlags a) (reads a) (hsize a)
  have h := sigma_flat_size (r*width) flags blocks
    (fun a j hj => (blockFlags_read flags _ _ j hj).symm) sizes
  simpa only [Nat.mul_assoc] using h
end Nested

end GroupWL.FiniteCode
