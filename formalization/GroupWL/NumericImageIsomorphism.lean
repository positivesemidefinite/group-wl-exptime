import GroupWL.MachinePrograms.IndexedImageTest

/-! Numeric generator-image search characterizes group isomorphism. -/
namespace GroupWL.NumericGroupImages
open MachinePrograms
variable {n m k : ℕ} {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
  [DecidableEq G] [DecidableEq H]

theorem exists_valid_iff (eG : Fin n≃G) (eH : Fin m≃H)
    (op : Fin n→Fin n→Fin n) (op' : Fin m→Fin m→Fin m)
    (hop : ∀x y,eG (op x y)=eG x*eG y) (hop' : ∀x y,eH (op' x y)=eH x*eH y)
    (identity : Fin n) (identity' : Fin m) (hid : eG identity=1) (hid' : eH identity'=1)
    (a : Fin k→Fin n) (ha : Refinement.Generates (eG ∘ a)) (hnm : n=m) :
    (∃b,GroupImageTest.Valid op op' identity identity' a b) ↔ Nonempty (G≃*H) := by
  constructor
  · rintro ⟨b,hb⟩
    have hg : op=GroupMapPrograms.numericOperation eG := by
      funext x y
      apply eG.injective
      simp [GroupMapPrograms.numericOperation,hop]
    have hh : op'=GroupMapPrograms.numericOperation eH := by
      funext x y
      apply eH.injective
      simp [GroupMapPrograms.numericOperation,hop']
    apply GroupMapPrograms.numeric_valid_isomorphic eG eH (expand op op' identity identity' a b) hnm
    simpa only [GroupImageTest.Valid,hg,hh] using hb
  · rintro ⟨f⟩
    let b : Fin k→Fin m := fun i => eH.symm (f (eG (a i)))
    have he := expand_hom eG eH op op' hop hop' identity identity' hid hid' a b ha f.toMonoidHom
      (fun i => by simp [b])
    refine ⟨b,?_⟩
    unfold GroupImageTest.Valid
    rw [he]
    constructor
    · intro x y
      apply eH.injective
      simp [hop,hop',f.map_mul]
    · exact eH.symm.injective.comp (f.injective.comp eG.injective)

theorem exists_index_iff (op : Fin n→Fin n→Fin n) (op' : Fin m→Fin m→Fin m)
    (identity : Fin n) (identity' : Fin m) (a : Fin k→Fin n) :
    (∃i<m^k,IndexedImageTest.Accepts op op' identity identity' a i) ↔
      ∃b,GroupImageTest.Valid op op' identity identity' a b := by
  constructor
  · rintro ⟨i,hi,h⟩
    exact ⟨finFunctionFinEquiv.symm (⟨i,hi⟩ : Fin (m^k)),by simpa [IndexedImageTest.Accepts,hi] using h⟩
  · rintro ⟨b,hb⟩
    let i : Fin (m^k) := finFunctionFinEquiv b
    refine ⟨i.val,i.isLt,?_⟩
    unfold IndexedImageTest.Accepts
    rw [dif_pos i.isLt]
    change GroupImageTest.Valid op op' identity identity' a (finFunctionFinEquiv.symm i)
    simpa only [i,Equiv.symm_apply_apply] using hb

end GroupWL.NumericGroupImages
