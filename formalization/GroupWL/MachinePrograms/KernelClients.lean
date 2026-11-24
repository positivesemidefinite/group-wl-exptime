import GroupWL.MachinePrograms.KernelProgram

/-! Semantic interfaces for the concrete clients embedded in Gaussian elimination. -/
namespace GroupWL.MachinePrograms.KernelProgram
open NatArrayLanguage

theorem multiply_runs (S : State) (M r k c p : ℕ) (A B : List ℕ)
    (bounded : S.Bounded M) (rows : S.scalar (mr .rows)=r)
    (inner : S.scalar (mr .inner)=k) (cols : S.scalar (mr .cols)=c)
    (modulus : S.scalar (mr .modulus)=p)
    (left : S.array (ma .left)=A) (right : S.array (ma .right)=B)
    (positive : 0<p) (small : p*p+p≤M) (size : r*c≤M)
    (leftLength : A.length=r*k) (rightLength : B.length=k*c)
    (leftSmall : ∀x∈A,x<p) (rightSmall : ∀x∈B,x<p) :
    ∃ t≤r*c*(12*k+9)+7,∃ T,Runs (storageBound Reg Arr M) multiply S t T ∧
      T.Bounded M ∧ T.left=S.left ∧ T.right.right=S.right.right ∧
      T.array (ma .output)=matrixProduct A B r k c p ∧
      T.scalar (mr .rows)=r ∧ T.scalar (mr .inner)=k ∧ T.scalar (mr .cols)=c ∧
      T.scalar (mr .modulus)=p := by
  have projRows : S.right.left.scalar .rows=r := rows
  have projInner : S.right.left.scalar .inner=k := inner
  have projCols : S.right.left.scalar .cols=c := cols
  have projMod : S.right.left.scalar .modulus=p := modulus
  have projLeft : S.right.left.array .left=A := left
  have projRight : S.right.left.array .right=B := right
  obtain ⟨t,ht,U,run,hU,hout⟩ := MatrixArithmetic.multiply_runs S.right.left M bounded.right.left
    (by omega) (by rwa [projMod]) (by rwa [projMod]) (by rwa [projRows,projCols])
    (by rwa [projLeft,projRows,projInner]) (by rwa [projRight,projInner,projCols])
    (by rwa [projLeft,projMod]) (by rwa [projRight,projMod])
  rw [projRows,projInner,projCols] at ht
  have out : U.array .output=matrixProduct A B r k c p := by
    simpa only [matrixProduct,MatrixArithmetic.matrixEntry,projRows,projCols,
      projInner,projMod,projLeft,projRight] using hout
  let T := S.left.join (U.join S.right.right)
  refine ⟨t,ht,T,multiply_client run bounded,bounded.left.join (hU.join bounded.right.right),rfl,rfl,out,?_,?_,?_,?_⟩
  · exact (run.scalar_eq_of_not_mem .rows (by decide)).trans projRows
  · exact (run.scalar_eq_of_not_mem .inner (by decide)).trans projInner
  · exact (run.scalar_eq_of_not_mem .cols (by decide)).trans projCols
  · exact (run.scalar_eq_of_not_mem .modulus (by decide)).trans projMod

theorem slice_runs (S : State) (M base n : ℕ) (xs : List ℕ) (bounded : S.Bounded M)
    (offset : S.scalar (cr .offset)=base) (length : S.scalar (cr .length)=n)
    (input : S.array (ca .input)=xs) (one : 1≤M) (valid : base+n≤xs.length) :
    ∃ t≤6*n+6,∃ T,Runs (storageBound Reg Arr M) slice S t T ∧ T.Bounded M ∧
      T.left=S.left ∧ T.right.left=S.right.left ∧
      T.right.right.left=S.right.right.left ∧ T.right.right.right.left=S.right.right.right.left ∧
      T.array (ca .output)=List.ofFn (fun i : Fin n => ArraySlice.value xs base i) := by
  have hb := bounded.right.right.right.right.left
  have ho : S.right.right.right.right.left.scalar .offset=base := offset
  have hl : S.right.right.right.right.left.scalar .length=n := length
  have hi : S.right.right.right.right.left.array .input=xs := input
  obtain ⟨t,ht,U,run,hU,hout⟩ := ArraySlice.program_runs S.right.right.right.right.left M hb one
    (by rwa [ho,hl,hi])
  rw [hl] at ht
  simp only [hi,ho,hl] at hout
  let T := S.left.join (S.right.left.join (S.right.right.left.join
    (S.right.right.right.left.join (U.join S.right.right.right.right.right))))
  refine ⟨t,ht,T,slice_client run bounded,?_,rfl,rfl,rfl,rfl,hout⟩
  exact bounded.left.join (bounded.right.left.join (bounded.right.right.left.join
    (bounded.right.right.right.left.join (hU.join bounded.right.right.right.right.right))))

theorem search_runs (S : State) (M : ℕ) (xs : List ℕ) (bounded : S.Bounded M)
    (input : S.array (sa .row)=xs) (one : 1≤M) :
    ∃ t≤8*xs.length+7,∃ T,Runs (storageBound Reg Arr M) search S t T ∧ T.Bounded M ∧
      T.left=S.left ∧ T.right.left=S.right.left ∧ T.right.right.right=S.right.right.right ∧
      T.array (sa .row)=xs ∧
      T.scalar (sr .found)=PivotSearch.flag (PivotSearch.first xs xs.length) ∧
      T.scalar (sr .pivot)=(PivotSearch.first xs xs.length).getD xs.length := by
  have hin : S.right.right.left.array .row=xs := input
  obtain ⟨t,ht,U,run,hU,hf,hp⟩ := PivotSearch.program_runs S.right.right.left M bounded.right.right.left one
  rw [hin] at ht hf hp
  let T := S.left.join (S.right.left.join (U.join S.right.right.right))
  exact ⟨t,ht,T,search_client run bounded,
    bounded.left.join (bounded.right.left.join (hU.join bounded.right.right.right)),rfl,rfl,rfl,
    (run.array_eq_of_not_mem .row (by decide)).trans hin,hf,hp⟩

theorem pivot_runs (p : ℕ) [NeZero p] (S : State) (M w j : ℕ) (xs : List ℕ)
    (bounded : S.Bounded M) (width : S.scalar (pr .width)=w)
    (pivotIndex : S.scalar (pr .pivot)=j) (modulus : S.scalar (pr .modulus)=p)
    (input : S.array (pa .row)=xs) (length : xs.length=w) (valid : j<w)
    (small : p*p+p≤M) (size : w*(w-1)≤M) (values : ∀x∈xs,x<p) :
    ∃ t≤17*(w*(w-1))+3*p+11,∃ T,Runs (storageBound Reg Arr M) (pivot p) S t T ∧ T.Bounded M ∧
      T.left=S.left ∧ T.right.left=S.right.left ∧ T.right.right.left=S.right.right.left ∧
      T.right.right.right.right=S.right.right.right.right ∧
      T.array (pa .lift)=List.ofFn (fun i : Fin (w*(w-1)) =>
        PivotMatrix.liftValue xs (w-1) j (-((xs[j]?.getD 0:ℕ):ZMod p)⁻¹).val p i) ∧
      T.array (pa .lowerTranspose)=List.ofFn (fun i : Fin (w*(w-1)) =>
        PivotMatrix.lowerValue (w-1) j i) := by
  have hw : S.right.right.right.left.scalar .width=w := width
  have hj : S.right.right.right.left.scalar .pivot=j := pivotIndex
  have hp : S.right.right.right.left.scalar .modulus=p := modulus
  have hi : S.right.right.right.left.array .row=xs := input
  obtain ⟨t,ht,U,run,hU,hl,hr⟩ := PivotMatrix.withInverse_runs p S.right.right.right.left M
    bounded.right.right.right.left hp (by rw [hw,hi,length]) (by rwa [hj,hi,length])
    small (by rwa [hw]) (by rwa [hi])
  simp only [hw,hj,hi] at ht hl hr
  let T := S.left.join (S.right.left.join (S.right.right.left.join (U.join S.right.right.right.right)))
  exact ⟨t,ht,T,pivot_client run bounded,
    bounded.left.join (bounded.right.left.join (bounded.right.right.left.join
      (hU.join bounded.right.right.right.right))),rfl,rfl,rfl,rfl,hl,hr⟩

theorem identity_runs (S : State) (M n : ℕ) (bounded : S.Bounded M)
    (dimension : S.scalar (ir .dimension)=n) (one : 1≤M) (size : n*n≤M) :
    ∃ t≤6*n+7,∃ T,Runs (storageBound Reg Arr M) identity S t T ∧ T.Bounded M ∧
      T.left=S.left ∧ T.array (ia .output)=IdentityMatrix.diagonalPrefix n n := by
  have hn : S.right.right.right.right.right.scalar .dimension=n := dimension
  obtain ⟨t,ht,U,run,hU,hout⟩ := IdentityMatrix.program_runs
    S.right.right.right.right.right M bounded.right.right.right.right.right one (by rwa [hn])
  rw [hn] at ht hout
  let T := S.left.join (S.right.left.join (S.right.right.left.join
    (S.right.right.right.left.join (S.right.right.right.right.left.join U))))
  exact ⟨t,ht,T,identity_client run bounded,
    bounded.left.join (bounded.right.left.join (bounded.right.right.left.join
      (bounded.right.right.right.left.join (bounded.right.right.right.right.left.join hU)))),rfl,hout⟩

end GroupWL.MachinePrograms.KernelProgram
