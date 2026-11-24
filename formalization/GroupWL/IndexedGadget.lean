import GroupWL.FiniteGraphWL
import GroupWL.MachinePrograms.GroupInitial

/-! Numeric encoding of the multiplication graph and its adjacency test. -/
namespace GroupWL.IndexedGadget
open Refinement IndexedRefinement
abbrev Vertex (n : ℕ) := Fin n ⊕ (Fin n × Fin n × Fin 4)
def size (n : ℕ) := n+n*(n*4)

def enumeration (n : ℕ) : Vertex n ≃ Fin (size n) :=
  (Equiv.sumCongr (Equiv.refl (Fin n))
    ((Equiv.prodCongr (Equiv.refl (Fin n)) finProdFinEquiv).trans finProdFinEquiv)).trans finSumFinEquiv

@[simp] theorem enumeration_group {n : ℕ} (v : Fin n) : (enumeration n (.inl v)).val=v.val := rfl

theorem enumeration_aux {n : ℕ} (g h : Fin n) (j : Fin 4) :
    (enumeration n (.inr (g,h,j))).val=n+(j.val+4*(h.val+n*g.val)) := by
  change n+(j.val+4*h.val+(n*4)*g.val)=_
  ring

def pairIndex (n v : ℕ) := (v-n)/4
def tag (n v : ℕ) := (v-n)%4

@[simp] theorem pairIndex_aux {n : ℕ} (g h : Fin n) (j : Fin 4) :
    pairIndex n (enumeration n (.inr (g,h,j))).val=h.val+n*g.val := by
  rw [pairIndex,enumeration_aux,Nat.add_sub_cancel_left,Nat.add_mul_div_left _ _ (by decide),Nat.div_eq_of_lt j.isLt,zero_add]

@[simp] theorem tag_aux {n : ℕ} (g h : Fin n) (j : Fin 4) :
    tag n (enumeration n (.inr (g,h,j))).val=j.val := by
  rw [tag,enumeration_aux,Nat.add_sub_cancel_left,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt j.isLt]

theorem pairIndex_lt {n : ℕ} (hn : 0<n) (v : Fin (size n)) : pairIndex n v.val<n*n := by
  have hn2 : 0<n*n := Nat.mul_pos hn hn
  have hv := v.isLt
  unfold size at hv
  unfold pairIndex
  apply (Nat.div_lt_iff_lt_mul (by decide : 0<4)).mpr
  by_cases h : n≤v.val
  · nlinarith [Nat.sub_add_cancel h]
  · simp [Nat.sub_eq_zero_of_le (by omega : v.val≤n),hn2]

def attachment (v g h j product : ℕ) : Bool :=
  decide ((j=0 ∧ v=g) ∨ (j=1 ∧ v=h) ∨ (j=3 ∧ v=product))

def test (n : ℕ) (table : List ℕ) (x y : ℕ) : Bool :=
  if x<n then
    if y<n then false else
      attachment x (pairIndex n y/n) (pairIndex n y%n) (tag n y) (read table (pairIndex n y))
  else if y<n then
    attachment y (pairIndex n x/n) (pairIndex n x%n) (tag n x) (read table (pairIndex n x))
  else decide (pairIndex n x=pairIndex n y ∧ (tag n x+1=tag n y ∨ tag n y+1=tag n x))

def adj {n : ℕ} (f : Fin n → Fin n → Fin n) : Vertex n → Vertex n → Bool
  | .inl _,.inl _ => false
  | .inl v,.inr (g,h,j) => decide ((j=0 ∧ v=g) ∨ (j=1 ∧ v=h) ∨ (j=3 ∧ v=f g h))
  | .inr (g,h,j),.inl v => decide ((j=0 ∧ v=g) ∨ (j=1 ∧ v=h) ∨ (j=3 ∧ v=f g h))
  | .inr (g,h,i),.inr (g',h',j) => decide (g=g' ∧ h=h' ∧ (i.val+1=j.val ∨ j.val+1=i.val))

theorem test_correct {n : ℕ} (f : Fin n → Fin n → Fin n) (a b : Vertex n) :
    test n (MachinePrograms.GroupInitial.tableWord f) (enumeration n a).val (enumeration n b).val=adj f a b := by
  have hg (v : Fin n) : (enumeration n (.inl v)).val<n := v.isLt
  have ha (g h : Fin n) (j : Fin 4) : ¬(enumeration n (.inr (g,h,j))).val<n := by rw [enumeration_aux];omega
  have div (g h : Fin n) : (h.val+n*g.val)/n=g.val := by
    have hn : 0<n := by have := g.isLt;omega
    rw [Nat.add_mul_div_left _ _ hn,Nat.div_eq_of_lt h.isLt,zero_add]
  have mod (g h : Fin n) : (h.val+n*g.val)%n=h.val := by rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt h.isLt]
  cases a with
  | inl v => cases b with
    | inl w => simp [test,hg,adj]
    | inr z =>
      rcases z with ⟨g,h,j⟩
      simp only [test,enumeration_group,if_pos v.isLt,if_neg (ha g h j),pairIndex_aux,tag_aux,div,mod,
        IndexedRefinement.read,MachinePrograms.GroupInitial.tableWord_read,enumeration_group,attachment,adj]
      congr 1
      simp only [Fin.ext_iff]
      norm_num
  | inr z =>
    rcases z with ⟨g,h,j⟩
    cases b with
    | inl v =>
      simp only [test,if_neg (ha g h j),enumeration_group,if_pos v.isLt,pairIndex_aux,tag_aux,div,mod,
        IndexedRefinement.read,MachinePrograms.GroupInitial.tableWord_read,enumeration_group,attachment,adj]
      congr 1
      simp only [Fin.ext_iff]
      norm_num
    | inr z =>
      rcases z with ⟨g',h',j'⟩
      simp only [test,if_neg (ha g h j),if_neg (ha g' h' j'),pairIndex_aux,tag_aux,adj]
      congr 1
      have he : h.val+n*g.val=h'.val+n*g'.val ↔ g=g' ∧ h=h' := by
        change (finProdFinEquiv (g,h)).val=(finProdFinEquiv (g',h')).val ↔ _
        rw [Fin.val_inj,Equiv.apply_eq_iff_eq,Prod.mk.injEq]
      rw [he,and_assoc]



def numericAdj {n : ℕ} (f : Fin n → Fin n → Fin n) (x y : Fin (size n)) : Bool :=
  adj f ((enumeration n).symm x) ((enumeration n).symm y)

theorem test_numericAdj {n : ℕ} (f : Fin n → Fin n → Fin n) (x y : Fin (size n)) :
    test n (MachinePrograms.GroupInitial.tableWord f) x.val y.val=numericAdj f x y := by
  simpa only [Equiv.apply_symm_apply] using test_correct f ((enumeration n).symm x) ((enumeration n).symm y)

end GroupWL.IndexedGadget
