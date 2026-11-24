import GroupWL.MachinePrograms.ProductGroupOperation
import GroupWL.MachinePrograms.GeneratorImageSemantics
import GroupWL.MachinePrograms.GroupSaturationSemantics

/-! Exact finite-array semantics of extending numeric generator images. -/
namespace GroupWL.NumericGroupImages
open MachinePrograms MachinePrograms.FiniteSetArrays
variable {n m k : ℕ}

def seeds (identity : Fin n) (identity' : Fin m) (a : Fin k→Fin n) (b : Fin k→Fin m) : Finset (Fin (n*m)) :=
  insert (finProdFinEquiv (identity,identity')) (Finset.univ.image (fun i => finProdFinEquiv (a i,b i)))
def mask (op : Fin n→Fin n→Fin n) (op' : Fin m→Fin m→Fin m)
    (identity : Fin n) (identity' : Fin m) (a : Fin k→Fin n) (b : Fin k→Fin m) : List ℕ :=
  word (GroupSaturation.closureSet (ProductGroupTable.productOp op op') (seeds identity identity' a b) (n*m))
def expand (op : Fin n→Fin n→Fin n) (op' : Fin m→Fin m→Fin m)
    (identity : Fin n) (identity' : Fin m) (a : Fin k→Fin n) (b : Fin k→Fin m) (x : Fin n) : Fin m :=
  ⟨GeneratorImages.rowImage (mask op op' identity identity' a b) m identity'.val x.val,
    FirstNonzero.hit_getD_lt _ _ m identity'.val identity'.isLt⟩

variable {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H]

def pairEquiv (eG : Fin n≃G) (eH : Fin m≃H) : Fin (n*m)≃G×H :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr eG eH)

@[simp] theorem pairEquiv_pair (eG : Fin n≃G) (eH : Fin m≃H) (x : Fin n) (y : Fin m) :
    pairEquiv eG eH (finProdFinEquiv (x,y))=(eG x,eH y) := by simp [pairEquiv]

theorem mask_mem (eG : Fin n≃G) (eH : Fin m≃H)
    (op : Fin n→Fin n→Fin n) (op' : Fin m→Fin m→Fin m)
    (hop : ∀x y,eG (op x y)=eG x*eG y) (hop' : ∀x y,eH (op' x y)=eH x*eH y)
    (identity : Fin n) (identity' : Fin m) (hid : eG identity=1) (hid' : eH identity'=1)
    (a : Fin k→Fin n) (b : Fin k→Fin m) (x : Fin n) (y : Fin m) :
    (mask op op' identity identity' a b)[x.val*m+y.val]?.getD 0≠0 ↔
      (eG x,eH y)∈FiniteWordTypes.explore (eG ∘ a) (eH ∘ b) (Fintype.card (G×H)) := by
  have he : ∀u v,pairEquiv eG eH (ProductGroupTable.productOp op op' u v)=
      pairEquiv eG eH u*pairEquiv eG eH v := by
    intro u v
    apply Prod.ext
    · simpa [pairEquiv,ProductGroupTable.productOp] using hop (finProdFinEquiv.symm u).1 (finProdFinEquiv.symm v).1
    · simpa [pairEquiv,ProductGroupTable.productOp] using hop' (finProdFinEquiv.symm u).2 (finProdFinEquiv.symm v).2
  have hseed : (seeds identity identity' a b).image (pairEquiv eG eH)=
      insert 1 (Finset.univ.image (fun i => ((eG ∘ a) i,(eH ∘ b) i))) := by
    simp [seeds,Finset.image_insert,Finset.image_image,Function.comp_def,hid,hid']
    rfl
  have hm := GroupSaturation.mask_closure_mem (ProductGroupTable.productOp op op')
    (seeds identity identity' a b) (pairEquiv eG eH) he (eG ∘ a) (eH ∘ b) hseed
    (finProdFinEquiv (x,y))
  have hindex : x.val*m+y.val=(finProdFinEquiv (x,y)).val := by
    simp [finProdFinEquiv,Nat.add_comm,Nat.mul_comm]
  rw [hindex]
  unfold mask
  rw [read_word]
  simpa using hm

theorem expand_hom (eG : Fin n≃G) (eH : Fin m≃H)
    (op : Fin n→Fin n→Fin n) (op' : Fin m→Fin m→Fin m)
    (hop : ∀x y,eG (op x y)=eG x*eG y) (hop' : ∀x y,eH (op' x y)=eH x*eH y)
    (identity : Fin n) (identity' : Fin m) (hid : eG identity=1) (hid' : eH identity'=1)
    (a : Fin k→Fin n) (b : Fin k→Fin m) (ha : Refinement.Generates (eG ∘ a))
    (f : G→*H) (himages : ∀i,eH (b i)=f (eG (a i))) :
    expand op op' identity identity' a b=fun x => eH.symm (f (eG x)) := by
  have hb : eH ∘ b=f ∘ (eG ∘ a) := funext himages
  have hm : ∀x:Fin n,∀y:Fin m,
      (mask op op' identity identity' a b)[x.val*m+y.val]?.getD 0≠0 ↔
        (eG x,eH y)∈FiniteWordTypes.explore (eG ∘ a) (f ∘ (eG ∘ a)) (Fintype.card (G×H)) := by
    intro x y
    rw [←hb]
    exact mask_mem eG eH op op' hop hop' identity identity' hid hid' a b x y
  funext x
  apply Fin.ext
  exact GeneratorImages.rowImage_hom eG eH (eG ∘ a) ha f _ hm identity'.val x

end GroupWL.NumericGroupImages
