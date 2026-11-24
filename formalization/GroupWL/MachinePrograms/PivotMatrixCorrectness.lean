import GroupWL.MatrixEncoding
import GroupWL.PivotCoordinates
import GroupWL.MachinePrograms.PivotMatrix

/-! The two concrete pivot arrays are the lift matrix and the transposed
retraction matrix of the proved one-equation kernel chart. -/
namespace GroupWL.MachinePrograms.PivotMatrixCorrectness
open CachedElimination PivotCoordinates PivotMatrix
variable {p n : ℕ} [Fact p.Prime]

def rowWord (f : (Fin n → ZMod p) →ₗ[ZMod p] ZMod p) : List ℕ :=
  List.ofFn (fun i => (f (Pi.single i 1)).val)

@[simp] theorem rowWord_length (f : (Fin n → ZMod p) →ₗ[ZMod p] ZMod p) :
    (rowWord f).length=n := List.length_ofFn

@[simp] theorem rowWord_read (f : (Fin n → ZMod p) →ₗ[ZMod p] ZMod p) (i : Fin n) :
    ((rowWord f)[i.val]?).getD 0=(f (Pi.single i 1)).val := by simp [rowWord]

theorem rowWord_lt (f : (Fin n → ZMod p) →ₗ[ZMod p] ZMod p) :
    ∀x∈rowWord f,x<p := by
  intro x hx
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  exact ZMod.val_lt _

def lowerTransposeData {m n : ℕ} (f : (Fin m → ZMod p) →ₗ[ZMod p] (Fin n → ZMod p)) :
    MatrixData (F:=ZMod p) m n := Vector.ofFn (fun i => Vector.ofFn (fun j => f (Pi.single i 1) j))

@[simp] theorem lowerTransposeData_entry {m n : ℕ}
    (f : (Fin m → ZMod p) →ₗ[ZMod p] (Fin n → ZMod p)) (i : Fin m) (j : Fin n) :
    (lowerTransposeData f)[i][j]=f (Pi.single i 1) j := by simp [lowerTransposeData]

theorem coordinate_eq_swap (j : Fin (n+1)) (k : Fin n) :
    coordinate j.val k.val=(Equiv.swap 0 j k.succ).val := by
  simp only [coordinate,Equiv.swap_apply_def,Fin.ext_iff,Fin.val_zero,Fin.val_succ,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,if_false]
  split_ifs <;> rfl

theorem swap_eq_iff (j i : Fin (n+1)) (k : Fin n) :
    Equiv.swap 0 j i=k.succ ↔ i=Equiv.swap 0 j k.succ := by
  constructor <;> intro h
  · simpa using congrArg (Equiv.swap 0 j) h
  · rw [h,Equiv.swap_apply_self]

theorem flat_div (i : Fin (n+1)) (k : Fin n) : (i.val*n+k.val)/n=i.val := by
  have hn : 0<n := Nat.zero_lt_of_lt k.isLt
  rw [Nat.mul_comm i.val n,Nat.mul_add_div hn,Nat.div_eq_of_lt k.isLt,Nat.add_zero]
theorem flat_mod (i : Fin (n+1)) (k : Fin n) : (i.val*n+k.val)%n=k.val := by
  simp [Nat.add_mod,Nat.mod_eq_of_lt k.isLt]

theorem lowerValue_entry (f : (Fin (n+1) → ZMod p) →ₗ[ZMod p] ZMod p)
    (j : Fin (n+1)) (hj : f (Pi.single j 1)≠0) (i : Fin (n+1)) (k : Fin n) :
    lowerValue n j.val (i.val*n+k.val)=
      ((nonzeroPivotChart f j hj).lower (Pi.single i 1) k).val := by
  rw [nonzeroPivot_lower_entry]
  simp only [lowerValue,flat_div,flat_mod,coordinate_eq_swap]
  have he : i.val=(Equiv.swap 0 j k.succ).val ↔ Equiv.swap 0 j k.succ=i := by
    rw [Fin.val_inj,eq_comm]
  simp only [he]
  haveI : Fact (1<p) := ⟨(Fact.out : p.Prime).one_lt⟩
  split_ifs <;> first | exact (ZMod.val_zero).symm | exact (ZMod.val_one p).symm

theorem liftValue_entry (f : (Fin (n+1) → ZMod p) →ₗ[ZMod p] ZMod p)
    (j : Fin (n+1)) (hj : f (Pi.single j 1)≠0) (i : Fin (n+1)) (k : Fin n) :
    liftValue (rowWord f) n j.val (-(f (Pi.single j 1))⁻¹).val p (i.val*n+k.val)=
      ((nonzeroPivotChart f j hj).lift (Pi.single k 1) i).val := by
  rw [nonzeroPivot_lift_entry]
  simp only [liftValue,flat_div,flat_mod,Fin.val_inj]
  by_cases he : i=j
  · subst i
    simp only [if_true,coordinate_eq_swap,rowWord_read]
    rw [ZMod.val_mul]
    exact congrArg (·%p) (Nat.mul_comm _ _)
  · simp only [he,if_false]
    rw [lowerValue_entry f j hj i k,nonzeroPivot_lower_entry]
    have hc : Equiv.swap 0 j k.succ=i ↔ Equiv.swap 0 j i=k.succ :=
      eq_comm.trans (swap_eq_iff j i k).symm
    simp only [hc]

theorem liftWord (f : (Fin (n+1) → ZMod p) →ₗ[ZMod p] ZMod p)
    (j : Fin (n+1)) (hj : f (Pi.single j 1)≠0) :
    List.ofFn (fun z : Fin ((n+1)*n) =>
      liftValue (rowWord f) n j.val (-(f (Pi.single j 1))⁻¹).val p z.val)=
      MatrixEncoding.word (ofLinear (nonzeroPivotChart f j hj).lift) := by
  unfold MatrixEncoding.word
  apply congrArg List.ofFn
  funext z
  let i := (finProdFinEquiv.symm z).1
  let k := (finProdFinEquiv.symm z).2
  have hz : z.val=i.val*n+k.val := by
    have h := congrArg Fin.val (finProdFinEquiv.apply_symm_apply z)
    simpa [i,k,Nat.mul_comm,Nat.add_comm] using h.symm
  change liftValue _ _ _ _ _ z.val=(ofLinear (nonzeroPivotChart f j hj).lift)[i][k].val
  rw [hz]
  erw [ofLinear_entry]
  exact liftValue_entry f j hj i k

theorem lowerWord (f : (Fin (n+1) → ZMod p) →ₗ[ZMod p] ZMod p)
    (j : Fin (n+1)) (hj : f (Pi.single j 1)≠0) :
    List.ofFn (fun z : Fin ((n+1)*n) => lowerValue n j.val z.val)=
      MatrixEncoding.word (lowerTransposeData (nonzeroPivotChart f j hj).lower) := by
  unfold MatrixEncoding.word
  apply congrArg List.ofFn
  funext z
  let i := (finProdFinEquiv.symm z).1
  let k := (finProdFinEquiv.symm z).2
  have hz : z.val=i.val*n+k.val := by
    have h := congrArg Fin.val (finProdFinEquiv.apply_symm_apply z)
    simpa [i,k,Nat.mul_comm,Nat.add_comm] using h.symm
  change lowerValue _ _ z.val=(lowerTransposeData (nonzeroPivotChart f j hj).lower)[i][k].val
  rw [hz]
  erw [lowerTransposeData_entry]
  exact lowerValue_entry f j hj i k

theorem program_chart_runs (f : (Fin (n+1) → ZMod p) →ₗ[ZMod p] ZMod p)
    (j : Fin (n+1)) (hj : f (Pi.single j 1)≠0)
    (S : State) (M : ℕ) (bounded : S.Bounded M)
    (width : S.scalar .width=n+1) (row : S.array .row=rowWord f)
    (modulus : S.scalar .modulus=p) (pivot : S.scalar .pivot=j.val)
    (inverse : S.scalar .negInverse=(-(f (Pi.single j 1))⁻¹).val)
    (small : p*p+p≤M) (size : (n+1)*n≤M) :
    ∃t≤17*((n+1)*n)+9,∃T,
      NatArrayLanguage.Runs (NatArrayLanguage.storageBound Reg Arr M) program S t T ∧
      T.Bounded M ∧ T.array .lift=MatrixEncoding.word (ofLinear (nonzeroPivotChart f j hj).lift) ∧
      T.array .lowerTranspose=MatrixEncoding.word (lowerTransposeData (nonzeroPivotChart f j hj).lower) := by
  obtain ⟨t,ht,T,hr,hT,hl,hL⟩ := program_runs S M bounded
    (by simp [width,row]) (by rw [modulus]; exact (Fact.out : p.Prime).pos)
    (by rwa [modulus]) (by simpa [width] using size)
    (by rw [inverse,modulus]; exact (ZMod.val_lt _).le)
    (by rw [row,modulus]; exact rowWord_lt f)
  simp only [width,Nat.add_sub_cancel, row,modulus,pivot,inverse] at ht hl hL
  exact ⟨t,ht,T,hr,hT,hl.trans (liftWord f j hj),hL.trans (lowerWord f j hj)⟩

end GroupWL.MachinePrograms.PivotMatrixCorrectness
