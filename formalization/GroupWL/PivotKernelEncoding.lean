import GroupWL.PivotElimination
import GroupWL.MachinePrograms.PivotMatrixCorrectness
import GroupWL.MachinePrograms.IdentityMatrix

/-! Exact matrix encodings linking materialized pivot elimination to its
finite-field Chart semantics. -/
namespace GroupWL.PivotKernelEncoding
open CachedElimination PivotElimination
open MachinePrograms.PivotMatrixCorrectness
open scoped BigOperators
variable {p n m k : ℕ} [Fact p.Prime]

theorem first_support_row (f : (Fin n → ZMod p) →ₗ[ZMod p] ZMod p) :
    MachinePrograms.PivotSearch.first (supportWord f) n =
      MachinePrograms.PivotSearch.first (rowWord f) n := by
  apply first_congr
  intro i hi
  have hs := supportWord_read f ⟨i,hi⟩
  have hr := rowWord_read f ⟨i,hi⟩
  simp only [Fin.val_mk] at hs hr
  rw [hs,hr,ZMod.val_eq_zero]
  by_cases h : f (Pi.single ⟨i,hi⟩ 1)=0 <;> simp [h]

theorem rowCoordinates_none_actual (f : (Fin n → ZMod p) →ₗ[ZMod p] ZMod p)
    (h : MachinePrograms.PivotSearch.first (rowWord f) n=none) :
    PivotElimination.rowCoordinates n f=
      PivotCoordinates.zeroChart n f (first_none_zero f ((first_support_row f).trans h)) :=
  rowCoordinates_none f ((first_support_row f).trans h)

theorem rowCoordinates_some_actual (f : (Fin (n+1) → ZMod p) →ₗ[ZMod p] ZMod p)
    (j : Fin (n+1)) (h : MachinePrograms.PivotSearch.first (rowWord f) (n+1)=some j.val)
    (hj : f (Pi.single j 1)≠0) :
    PivotElimination.rowCoordinates (n+1) f=PivotCoordinates.nonzeroPivotChart f j hj :=
  rowCoordinates_some f j ((first_support_row f).trans h) hj

theorem lowerTransposeData_comp
    (f : (Fin n → ZMod p) →ₗ[ZMod p] (Fin m → ZMod p))
    (g : (Fin k → ZMod p) →ₗ[ZMod p] (Fin n → ZMod p)) :
    lowerTransposeData (f.comp g)=MatrixEncoding.product (lowerTransposeData g) (lowerTransposeData f) := by
  unfold lowerTransposeData MatrixEncoding.product
  apply congrArg Vector.ofFn
  funext i
  apply congrArg Vector.ofFn
  funext j
  simp only [Vector.getElem_ofFn,LinearMap.comp_apply]
  have hx : g (Pi.single i 1)=∑l : Fin n,(g (Pi.single i 1) l) • Pi.single l 1 := by
    funext l
    simp [Pi.single_apply]
  conv_lhs => rw [hx,map_sum]
  simp [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]

theorem ofLinear_toLinear (A : MatrixData (F:=ZMod p) m n) : ofLinear (toLinear A)=A := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simp [ofLinear,toLinear,Pi.single_apply]

theorem ofLinear_comp
    (f : (Fin n → ZMod p) →ₗ[ZMod p] (Fin m → ZMod p))
    (g : (Fin k → ZMod p) →ₗ[ZMod p] (Fin n → ZMod p)) :
    ofLinear (f.comp g)=MatrixEncoding.product (ofLinear f) (ofLinear g) := by
  rw [←ofLinear_toLinear (MatrixEncoding.product (ofLinear f) (ofLinear g)),
    MatrixEncoding.product_toLinear,toLinear_ofLinear,toLinear_ofLinear]

theorem flat_diagonal_eq (i j : Fin n) (t : ℕ) (ht : t<n) :
    t*n+t=i.val*n+j.val ↔ i.val=t ∧ j.val=t := by
  constructor
  · intro h
    have he : finProdFinEquiv (⟨t,ht⟩,⟨t,ht⟩)=finProdFinEquiv (i,j) := by
      apply Fin.ext
      simpa [Nat.mul_comm,Nat.add_comm] using h
    have he := finProdFinEquiv.injective he
    have h₁ := congrArg (fun z : Fin n × Fin n => z.1.val) he
    have h₂ := congrArg (fun z : Fin n × Fin n => z.2.val) he
    exact ⟨h₁.symm,h₂.symm⟩
  · rintro ⟨hi,hj⟩
    simp [hi,hj]

theorem diagonalPrefix_read (n t : ℕ) (ht : t≤n) (i j : Fin n) :
    (MachinePrograms.IdentityMatrix.diagonalPrefix n t)[i.val*n+j.val]? =
      some (if i=j ∧ i.val<t then 1 else 0) := by
  induction t with
  | zero =>
    have hlt : i.val*n+j.val<n*n := by
      simpa [Nat.mul_comm,Nat.add_comm] using (finProdFinEquiv (i,j)).isLt
    simp [MachinePrograms.IdentityMatrix.diagonalPrefix,hlt]
  | succ t ih =>
    have htn : t<n := by omega
    rw [MachinePrograms.IdentityMatrix.diagonalPrefix,List.getElem?_set]
    simp only [MachinePrograms.IdentityMatrix.diagonalPrefix_length,
      MachinePrograms.IdentityMatrix.diagonal_lt htn,if_true,flat_diagonal_eq i j t htn,
      ih (by omega)]
    by_cases hij : i=j
    · subst j
      by_cases hit : i.val=t
      · simp [hit]
      · have he : i.val<t+1 ↔ i.val<t := by omega
        simp [hit,he]
    · have hne : ¬(i.val=t ∧ j.val=t) := by
        rintro ⟨hi,hj⟩
        exact hij (Fin.ext (hi.trans hj.symm))
      simp [hij,hne]

theorem diagonalPrefix_word (n : ℕ) :
    MachinePrograms.IdentityMatrix.diagonalPrefix n n =
      MatrixEncoding.word (ofLinear (LinearMap.id : (Fin n → ZMod p) →ₗ[ZMod p] (Fin n → ZMod p))) := by
  haveI : Fact (1<p) := ⟨(Fact.out : p.Prime).one_lt⟩
  apply List.ext_getElem?
  intro z
  by_cases hz : z<n*n
  · let i := (finProdFinEquiv.symm (⟨z,hz⟩ : Fin (n*n))).1
    let j := (finProdFinEquiv.symm (⟨z,hz⟩ : Fin (n*n))).2
    have he : z=i.val*n+j.val := by
      have h := congrArg Fin.val (finProdFinEquiv.apply_symm_apply (⟨z,hz⟩ : Fin (n*n)))
      simpa [i,j,Nat.mul_comm,Nat.add_comm] using h.symm
    rw [he,diagonalPrefix_read n n le_rfl i j]
    have hr := MatrixEncoding.word_read (ofLinear (LinearMap.id : (Fin n → ZMod p) →ₗ[ZMod p] (Fin n → ZMod p))) i j
    simp only [MachinePrograms.MatrixArithmetic.read] at hr
    have hw : (MatrixEncoding.word (ofLinear (LinearMap.id : (Fin n → ZMod p) →ₗ[ZMod p] (Fin n → ZMod p))))[i.val*n+j.val]? =
        some ((ofLinear (LinearMap.id : (Fin n → ZMod p) →ₗ[ZMod p] (Fin n → ZMod p)))[i][j].val) := by
      have hb : i.val*n+j.val<(MatrixEncoding.word (ofLinear (LinearMap.id : (Fin n → ZMod p) →ₗ[ZMod p] (Fin n → ZMod p)))).length := by simpa using (he ▸ hz)
      rw [List.getElem?_eq_getElem hb]
      simpa only [List.getElem?_eq_getElem hb,Option.getD_some] using congrArg some hr
    rw [hw]
    congr 1
    erw [ofLinear_entry]
    simp only [LinearMap.id_apply,Pi.single_apply,i.isLt,and_true]
    split_ifs <;> first | exact (ZMod.val_zero).symm | exact (ZMod.val_one p).symm
  · have hl : (MachinePrograms.IdentityMatrix.diagonalPrefix n n).length≤z := by simpa using (Nat.le_of_not_gt hz)
    have hr : (MatrixEncoding.word (ofLinear (LinearMap.id : (Fin n → ZMod p) →ₗ[ZMod p] (Fin n → ZMod p)))).length≤z := by simpa using (Nat.le_of_not_gt hz)
    rw [List.getElem?_eq_none hl,List.getElem?_eq_none hr]

end GroupWL.PivotKernelEncoding
