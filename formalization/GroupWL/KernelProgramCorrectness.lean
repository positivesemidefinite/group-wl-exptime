import GroupWL.PivotKernelEncoding
import GroupWL.MachinePrograms.KernelProgram

/-! Exact semantic agreement between the concrete array Gaussian loop and
its materialized kernel chart. -/
namespace GroupWL.KernelProgramCorrectness
open CoordinateElimination CachedElimination PivotElimination PivotKernelEncoding
open MachinePrograms KernelProgram PivotMatrixCorrectness
open scoped BigOperators
variable {p n m k : ℕ} [Fact p.Prime]

def encode {P : Submodule (ZMod p) (Fin n → ZMod p)} (D : Chart n P) : Data :=
  ⟨D.width,MatrixEncoding.word (ofLinear D.lift),MatrixEncoding.word (lowerTransposeData D.lower)⟩

theorem matrixProduct_word (A : MatrixData (F:=ZMod p) m n) (B : MatrixData (F:=ZMod p) n k) :
    matrixProduct (MatrixEncoding.word A) (MatrixEncoding.word B) m n k p=
      MatrixEncoding.word (MatrixEncoding.product A B) := (MatrixEncoding.word_product A B).symm

theorem equation_drop (A : List ℕ) (n i p : ℕ) (D : Data) :
    equation (A.drop n) n i p D=equation A n (i+1) p D := by
  unfold equation
  congr 1
  apply congrArg List.ofFn
  funext j
  simp [ArraySlice.value,List.getElem?_drop,Nat.add_mul,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]

theorem executeRows_succ (A : List ℕ) (p n m : ℕ) (D : Data) :
    executeRows A p n (m+1) D =
      eliminate p n (equation A n 0 p (executeRows (A.drop n) p n m D))
        (executeRows (A.drop n) p n m D) := by
  induction m generalizing D with
  | zero => rfl
  | succ m ih =>
    rw [executeRows,ih,executeRows,equation_drop]

def rowLinear (f : (Fin n → ZMod p) →ₗ[ZMod p] ZMod p) :
    (Fin n → ZMod p) →ₗ[ZMod p] (Fin 1 → ZMod p) := LinearMap.pi (fun _ => f)

theorem rowLinear_word (f : (Fin n → ZMod p) →ₗ[ZMod p] ZMod p) :
    MatrixEncoding.word (ofLinear (rowLinear f))=rowWord f := by
  simp only [MatrixEncoding.word,rowWord,Nat.one_mul]
  apply congrArg List.ofFn
  funext i
  erw [ofLinear_entry]
  have he : (finProdFinEquiv.symm (Fin.cast (Nat.one_mul n).symm i)).2=i := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt i.isLt
  change (f (Pi.single (finProdFinEquiv.symm (Fin.cast (Nat.one_mul n).symm i)).2 1)).val=_
  rw [he]

theorem row_slice (A : MatrixData (F:=ZMod p) m n) (i : Fin m) :
    List.ofFn (fun j : Fin n => ArraySlice.value (MatrixEncoding.word A) (i.val*n) j)=
      MatrixEncoding.word (ofLinear (rowLinear ((LinearMap.proj i).comp (toLinear A)))) := by
  rw [rowLinear_word]
  apply congrArg List.ofFn
  funext j
  change MatrixArithmetic.read (MatrixEncoding.word A) (i.val*n+j.val)=_
  rw [MatrixEncoding.word_read]
  congr 1
  simp [toLinear,Pi.single_apply]

theorem equation_encode (A : MatrixData (F:=ZMod p) m n) (i : Fin m)
    {P : Submodule (ZMod p) (Fin n → ZMod p)} (D : Chart n P) :
    equation (MatrixEncoding.word A) n i.val p (encode D)=
      rowWord (((LinearMap.proj i).comp (toLinear A)).comp D.lift) := by
  simp only [equation,encode]
  rw [row_slice,matrixProduct_word,←ofLinear_comp]
  change MatrixEncoding.word (ofLinear (rowLinear (((LinearMap.proj i).comp (toLinear A)).comp D.lift)))=_
  exact rowLinear_word _

def encodeMaps {w : ℕ}
    (L : (Fin w → ZMod p) →ₗ[ZMod p] (Fin n → ZMod p))
    (K : (Fin n → ZMod p) →ₗ[ZMod p] (Fin w → ZMod p)) : Data :=
  ⟨w,MatrixEncoding.word (ofLinear L),MatrixEncoding.word (lowerTransposeData K)⟩

def extendMaps {w : ℕ}
    (L : (Fin w → ZMod p) →ₗ[ZMod p] (Fin n → ZMod p))
    (K : (Fin n → ZMod p) →ₗ[ZMod p] (Fin w → ZMod p))
    (h : (Fin w → ZMod p) →ₗ[ZMod p] ZMod p) : Data :=
  let R := PivotElimination.rowCoordinates w h
  encodeMaps (L.comp R.lift) (R.lower.comp K)

theorem eliminate_maps {w : ℕ}
    (L : (Fin w → ZMod p) →ₗ[ZMod p] (Fin n → ZMod p))
    (K : (Fin n → ZMod p) →ₗ[ZMod p] (Fin w → ZMod p))
    (h : (Fin w → ZMod p) →ₗ[ZMod p] ZMod p) :
    eliminate p n (rowWord h) (encodeMaps L K)=extendMaps L K h := by
  cases w with
  | zero =>
    have hL : L=0 := Subsingleton.elim _ _
    have hK : K=0 := Subsingleton.elim _ _
    simp [hL,hK,eliminate,rowWord,PivotSearch.first,extendMaps,PivotElimination.rowCoordinates,
      PivotCoordinates.zeroChart,LinearMap.comp_id,LinearMap.id_comp]
  | succ w =>
    cases hx : PivotSearch.first (rowWord h) (w+1) with
    | none =>
      rw [extendMaps,rowCoordinates_none_actual h hx]
      simp [eliminate,rowWord_length,hx,PivotCoordinates.zeroChart,LinearMap.comp_id,LinearMap.id_comp]
    | some j =>
      obtain ⟨hjlt,hjne⟩ := PivotSearch.first_some (rowWord h) (w+1) j hx
      let jf : Fin (w+1) := ⟨j,hjlt⟩
      have hj : h (Pi.single jf 1)≠0 := by
        have he := rowWord_read h jf
        change (rowWord h)[j]?.getD 0=(h (Pi.single jf 1)).val at he
        rw [he] at hjne
        exact (ZMod.val_eq_zero _).not.mp hjne
      have hr := rowWord_read h jf
      change (rowWord h)[j]?.getD 0=(h (Pi.single jf 1)).val at hr
      rw [extendMaps,rowCoordinates_some_actual h jf hx hj]
      simp only [eliminate,rowWord_length,hx,encodeMaps,PivotCoordinates.nonzeroPivotChart_width,
        Nat.add_sub_cancel,hr,ZMod.natCast_zmod_val]
      change (⟨w,matrixProduct _
        (List.ofFn (fun i : Fin ((w+1)*w) => PivotMatrix.liftValue (rowWord h) w jf.val
          (-(h (Pi.single jf 1))⁻¹).val p i)) n (w+1) w p,
        matrixProduct _ (List.ofFn (fun i : Fin ((w+1)*w) => PivotMatrix.lowerValue w jf.val i)) n (w+1) w p⟩ : Data)=_
      rw [liftWord h jf hj,lowerWord h jf hj]
      erw [matrixProduct_word,matrixProduct_word]
      erw [ofLinear_comp L (PivotCoordinates.nonzeroPivotChart h jf hj).lift,
        lowerTransposeData_comp (PivotCoordinates.nonzeroPivotChart h jf hj).lower K]
      rfl

theorem word_nested (A : MatrixData (F:=ZMod p) m n) :
    MatrixEncoding.word A=(List.ofFn (fun i => List.ofFn (fun j => A[i][j].val))).flatten := by
  simp only [MatrixEncoding.word,List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have hlt : i.val*n+j.val<m*n := by simpa [Nat.mul_comm,Nat.add_comm] using (finProdFinEquiv (i,j)).isLt
  have he : (⟨i.val*n+j.val,hlt⟩ : Fin (m*n))=finProdFinEquiv (i,j) := by
    apply Fin.ext
    simp [Nat.mul_comm,Nat.add_comm]
  simp only [he,Equiv.symm_apply_apply]

theorem word_rows (f : (Fin n → ZMod p) →ₗ[ZMod p] (Fin m → ZMod p)) :
    MatrixEncoding.word (ofLinear f)=
      (List.ofFn (fun i => rowWord ((LinearMap.proj i).comp f))).flatten := by
  rw [word_nested]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  rw [ofLinear_entry]
  rfl

theorem word_tail (f : (Fin n → ZMod p) →ₗ[ZMod p] (Fin (m+1) → ZMod p)) :
    MatrixEncoding.word (ofLinear ((tailMap m).comp f))=
      (MatrixEncoding.word (ofLinear f)).drop n := by
  rw [word_rows]
  conv_rhs => rw [word_rows,List.ofFn_succ,List.flatten_cons]
  simp only [List.drop_append,rowWord_length,List.drop_length,Nat.sub_self,List.drop_zero,List.nil_append]
  have hd : (rowWord ((LinearMap.proj (0 : Fin (m+1))).comp f)).drop n=[] := by
    simpa only [rowWord_length] using (List.drop_length (l:=rowWord ((LinearMap.proj (0 : Fin (m+1))).comp f)))
  rw [hd,List.nil_append]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  rfl

theorem lowerTransposeData_id (n : ℕ) :
    lowerTransposeData (LinearMap.id : (Fin n → ZMod p) →ₗ[ZMod p] (Fin n → ZMod p))=
      ofLinear (LinearMap.id : (Fin n → ZMod p) →ₗ[ZMod p] (Fin n → ZMod p)) := by
  unfold lowerTransposeData ofLinear
  apply congrArg Vector.ofFn
  funext i
  apply congrArg Vector.ofFn
  funext j
  simp [Pi.single_apply,eq_comm]

theorem initial_encode (f : (Fin n → ZMod p) →ₗ[ZMod p] (Fin 0 → ZMod p)) :
    initial n=encode (PivotElimination.kernelChart 0 n f) := by
  simp only [encode,PivotElimination.kernelChart,materialize_width,materialize_lift,materialize_lower,
    lowerTransposeData_id,←diagonalPrefix_word]
  rfl

theorem encode_kernel_succ (f : (Fin n → ZMod p) →ₗ[ZMod p] (Fin (m+1) → ZMod p)) :
    encode (PivotElimination.kernelChart (m+1) n f)=
      let D := PivotElimination.kernelChart m n ((tailMap m).comp f)
      extendMaps D.lift D.lower ((LinearMap.proj 0).comp (f.comp D.lift)) := by
  simp only [PivotElimination.kernelChart,encode,materialize_width,materialize_lift,materialize_lower,
    extendMaps,encodeMaps]

theorem executeRows_encode (f : (Fin n → ZMod p) →ₗ[ZMod p] (Fin m → ZMod p)) :
    executeRows (MatrixEncoding.word (ofLinear f)) p n m (initial n)=
      encode (PivotElimination.kernelChart m n f) := by
  induction m with
  | zero => exact initial_encode f
  | succ m ih =>
    rw [executeRows_succ,←word_tail,ih]
    let D := PivotElimination.kernelChart m n ((tailMap m).comp f)
    change eliminate p n (equation (MatrixEncoding.word (ofLinear f)) n 0 p (encode D)) (encode D)=_
    erw [equation_encode (ofLinear f) (0 : Fin (m+1)) D,toLinear_ofLinear]
    change eliminate p n (rowWord ((LinearMap.proj 0).comp (f.comp D.lift))) (encodeMaps D.lift D.lower)=_
    rw [eliminate_maps,encode_kernel_succ]

end GroupWL.KernelProgramCorrectness
