import GroupWL.MachinePrograms.InitialMatrixPrograms

/-! Decode both rows of a tuple-pair comparison while retaining both tables. -/
namespace GroupWL.MachinePrograms.InitialMatrixPrograms
open NatArrayLanguage
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def loadPair : Code := .seq (loadTuple false) (loadTuple true)

theorem loadPair_runs (S : Store Reg Arr) (B n m k cutoff i j : ℕ)
    (hS : S.Bounded B) (hn : S.scalar (.inr .leftCount)=n) (hm : S.scalar (.inr .rightCount)=m)
    (hcut : S.scalar (.inr .vectorLimit)=cutoff) (hi : S.scalar (.inr .row)=i)
    (hj : S.scalar (.inr .column)=j) (hk : S.scalar (.inr .arity)=k)
    (hone : S.scalar (.inr .one)=1) (hlen : (S.array (.inr .vector)).length=k)
    (hnpos : 0<n) (hmpos : 0<m) (h1 : 1≤B)
    (leftTable rightTable : List ℕ)
    (ht : S.array (.inr .fanouts)=leftTable) (ht' : S.array (.inr .targets)=rightTable) :
    ∃t≤12*k+22,∃T,Runs (storageBound Reg Arr B) loadPair S t T ∧ T.Bounded B ∧
      T.scalar (.inl .leftSize)=selectBase n m (decide (cutoff ≤ i)) ∧
      T.scalar (.inl .rightSize)=selectBase n m (decide (cutoff ≤ j)) ∧
      T.array (.inl .leftTable)=selectTable leftTable rightTable (decide (cutoff ≤ i)) ∧
      T.array (.inl .rightTable)=selectTable leftTable rightTable (decide (cutoff ≤ j)) ∧
      T.array (.inl .leftTuple)=IndexedRefinement.vectorWord (selectBase n m (decide (cutoff ≤ i))) k
        (selectCode cutoff i (decide (cutoff ≤ i))) ∧
      T.array (.inl .rightTuple)=IndexedRefinement.vectorWord (selectBase n m (decide (cutoff ≤ j))) k
        (selectCode cutoff j (decide (cutoff ≤ j))) ∧ (T.array (.inr .vector)).length=k := by
  obtain ⟨tl,htl,U,rl,hU,sizeL,tableL,tupleL,lenU⟩ := loadTuple_runs false S B n m k cutoff i
    hS hn hm hcut hi hk hone hlen hnpos hmpos h1 _ _ ht ht'
  have sfL (r : Reg) (h : r∉(loadTuple false).scalarWrites) : U.scalar r=S.scalar r := rl.scalar_eq_of_not_mem r h
  have afL (a : Arr) (h : a∉(loadTuple false).arrayWrites) : U.array a=S.array a := rl.array_eq_of_not_mem a h
  obtain ⟨tr,htr,V,rr,hV,sizeR,tableR,tupleR,lenV⟩ := loadTuple_runs true U B n m k cutoff j
    hU (by rw [sfL _ (by decide),hn]) (by rw [sfL _ (by decide),hm])
    (by rw [sfL _ (by decide),hcut]) (by change U.scalar (.inr .column)=_;rw [sfL _ (by decide),hj])
    (by rw [sfL _ (by decide),hk]) (by rw [sfL _ (by decide),hone]) lenU hnpos hmpos h1 _ _
    (by rw [afL _ (by decide),ht]) (by rw [afL _ (by decide),ht'])
  refine ⟨tl+tr,by omega,V,.seq rl rr,hV,?_,sizeR,?_,tableR,?_,tupleR,lenV⟩
  · exact (rr.scalar_eq_of_not_mem _ (by decide +kernel)).trans sizeL
  · exact (rr.array_eq_of_not_mem _ (by decide +kernel)).trans tableL
  · exact (rr.array_eq_of_not_mem _ (by decide +kernel)).trans tupleL

end GroupWL.MachinePrograms.InitialMatrixPrograms
