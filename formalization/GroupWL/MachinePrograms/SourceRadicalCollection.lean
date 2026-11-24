import GroupWL.MachinePrograms.SourceRadicalTables

/-! Complete polynomial execution of the readout-radical table builder. -/
namespace GroupWL.MachinePrograms.SourceRadicalTables
open NatArrayLanguage
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192

theorem program_runs (p : ℕ) [NeZero p] (scope coefficients dimensions : List ℕ) (b r M : ℕ)
    (hp : 1<p) (hscope : b*r≤scope.length) (hcoeff : b*r*2≤coefficients.length)
    (values : ∀ x∈coefficients,x<p) (hdims : r≤dimensions.length)
    (dims : ∀ i<r,dimensions[i]?.getD 0≤2)
    (hM : 2*b+2≤M) (hpM : p*p+p≤M) (hbM : b*b≤M) (hsize : b*r*b≤M)
    (S : State) (bounded : S.Bounded M)
    (hsc : S.array (.inr .scope)=scope) (hco : S.array (.inr .coefficients)=coefficients)
    (hdi : S.array (.inr .dimensions)=dimensions) (hb : S.scalar (.inr .blocks)=b)
    (hr : S.scalar (.inr .readouts)=r) :
    ∃ t≤r*(290*(b+p+4)^4+18)+9, ∃ T,
      Runs (storageBound Reg Arr M) (program p) S t T ∧ T.Bounded M ∧
      Ready scope coefficients dimensions b r T ∧
      T.array (.inr .output)=collect p scope coefficients dimensions b r r ∧
      T.array (.inr .widths)=List.ofFn (fun j : Fin r => width p scope coefficients dimensions b r j.val) := by
  have hrM : r≤M := hr ▸ bounded.1 (.inr .readouts)
  have hbr : b*r≤M := hscope.trans (hsc ▸ bounded.2.1 (.inr .scope))
  have hrb : r*b≤M := by simpa [Nat.mul_comm] using hbr
  have hbsize : b*(r*b)≤M := by simpa [Nat.mul_assoc] using hsize
  have valid : ValidAtoms M initialAtoms S := by
    simp [initialAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,Store.setArray,hb,hr,hrb,hbsize]
    omega
  obtain ⟨first,hUB⟩ := atoms_runs bounded initialAtoms valid
  let U := applyAtoms initialAtoms S
  have hUR : Ready scope coefficients dimensions b r U := by
    simp [Ready,U,initialAtoms,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,
      hsc,hco,hdi,hb,hr,Nat.mul_assoc]
  have hUone : U.scalar (.inr .one)=1 := by
    simp [U,initialAtoms,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray]
  have hUout : U.array (.inr .output)=collect p scope coefficients dimensions b r 0 := by
    simp [U,initialAtoms,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,
      hb,hr,collect,Nat.mul_assoc]
  have hUwidths : U.array (.inr .widths)=List.replicate r 0 := by
    simp [U,initialAtoms,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,hr]
  let I (i : ℕ) (V : State) : Prop := Ready scope coefficients dimensions b r V ∧ V.Bounded M ∧
    V.scalar (.inr .index)=i ∧ V.scalar (.inr .remaining)=r-i ∧ V.scalar (.inr .one)=1 ∧
    V.array (.inr .output)=collect p scope coefficients dimensions b r i ∧
    ArrayTabulation.Prefix (width p scope coefficients dimensions b r) r i (V.array (.inr .widths))
  have copied : (U.setScalar (.inr .remaining) (U.scalar (.inr .readouts))).Bounded M := hUB.setScalar _ (hUB.1 _)
  have start : I 0 ((U.setScalar (.inr .remaining) (U.scalar (.inr .readouts))).setScalar (.inr .index) 0) := by
    refine ⟨?_,copied.setScalar _ (Nat.zero_le M),?_,?_,?_,hUout,?_⟩
    · simpa [Ready,Store.setScalar] using hUR
    · simp
    · simpa [Store.setScalar] using hUR.2.2.2.2.1
    · simpa [Store.setScalar] using hUone
    · simpa only [Store.setScalar_array,hUwidths] using
        ArrayTabulation.Prefix.zero (width p scope coefficients dimensions b r) r
  have control : ∀ i≤r, ∀ V, I i V → V.scalar (.inr .index)=i ∧ V.scalar (.inr .remaining)=r-i ∧
      V.scalar (.inr .one)=1 ∧ V.size≤storageBound Reg Arr M := by
    intro i hi V hV
    exact ⟨hV.2.2.1,hV.2.2.2.1,hV.2.2.2.2.1,Store.size_le_of_bounded hV.2.1⟩
  have step : ∀ i<r, ∀ V, I i V → ∃ t≤290*(b+p+4)^4+15, ∃ W,
      Runs (storageBound Reg Arr M) (body p) V t W ∧
      W.scalar (.inr .index)=i ∧ W.scalar (.inr .remaining)=r-i ∧ W.scalar (.inr .one)=1 ∧
      (W.setScalar (.inr .index) (i+1)).size≤storageBound Reg Arr M ∧
      I (i+1) (advance (.inr .index) (.inr .remaining) W) := by
    intro i hi V hV
    rcases hV with ⟨hVR,hVB,hVi,hVrem,hVone,hVout,hVwidths⟩
    obtain ⟨t,ht,W,run,hWB,hWR,hout,hwidths,hframe⟩ := body_runs p scope coefficients dimensions b r M
      hp hscope hcoeff values hdims dims hM hpM hbM V hVB hVR (by rw [hVi]; exact hi)
    have hWi : W.scalar (.inr .index)=i := (hframe .index (by decide)).trans hVi
    have hWrem : W.scalar (.inr .remaining)=r-i := (hframe .remaining (by decide)).trans hVrem
    have hWone : W.scalar (.inr .one)=1 := (hframe .one (by decide)).trans hVone
    have hnext : (advance (.inr .index) (.inr .remaining) W).Bounded M :=
      (hWB.setScalar _ (by rw [hWi]; omega)).setScalar _ ((Nat.sub_le _ _).trans (hWB.1 _))
    refine ⟨t,ht,W,run,hWi,hWrem,hWone,Store.size_le_of_bounded (hWB.setScalar _ (by omega)),?_,hnext,?_,?_,?_,?_,?_⟩
    · simpa [Ready,advance,Store.setScalar] using hWR
    · simp [advance,Store.setScalar,hWi]
    · simp [advance,Store.setScalar,hWrem]
      omega
    · simp [advance,Store.setScalar,hWone]
    · change W.array (.inr .output)=_
      rw [hout,hVout,hVi]
      rfl
    · change ArrayTabulation.Prefix _ _ _ (W.array (.inr .widths))
      rw [hwidths,hVi]
      exact hVwidths.write hi
  obtain ⟨t,ht,T,last,hT⟩ := countedLoop_runs (storageBound Reg Arr M)
    (.inr .index) (.inr .remaining) (.inr .readouts) (.inr .one) (body p) r
    (290*(b+p+4)^4+15) I U (Store.size_le_of_bounded hUB) (Store.size_le_of_bounded copied)
    start control (by decide) (by decide) step
  have hnorm : 290*(b+p+4)^4+15+3=290*(b+p+4)^4+18 := by omega
  rw [hnorm] at ht
  refine ⟨6+t,by omega,T,first.seq last,hT.2.1,hT.1,hT.2.2.2.2.2.1,hT.2.2.2.2.2.2.complete⟩

theorem cost_le (p b r : ℕ) :
    r*(290*(b+p+4)^4+18)+9≤310*(r+1)*(b+p+4)^4 := by
  have hpow : 1≤(b+p+4)^4 := by
    have h : 0<(b+p+4)^4 := by positivity
    omega
  have hmul := Nat.mul_le_mul_left r hpow
  nlinarith

end GroupWL.MachinePrograms.SourceRadicalTables
