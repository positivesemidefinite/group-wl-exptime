import GroupWL.MachinePrograms.NatArrayCountedLoops
import GroupWL.MachinePrograms.ArrayTabulation

/-! A finite-control table loop with exact output and primitive time bound.
The supplied cell is executable syntax; its invariant is used only in the proof. -/
namespace GroupWL.MachinePrograms.NatArrayLanguage

variable {R A : Type*} [DecidableEq R] [DecidableEq A] [Fintype R] [Fintype A]

/-- Registers are length, position, remaining, one, zero. -/
def materialize (reg : Fin 5 ↪ R) (output : A) (result : R) (cell : Program R A) : Program R A :=
  .seq (atoms [.const (reg 3) 1,.const (reg 4) 0,.allocate output (reg 0) (reg 4)])
    (countedLoop (reg 1) (reg 2) (reg 0) (reg 3)
      (.seq cell (.atom (.write output (reg 1) result))))

theorem materialize_runs (reg : Fin 5 ↪ R) (output : A) (result : R) (cell : Program R A)
    (P : Store R A → Prop) (f : ℕ → ℕ) (M n c : ℕ)
    (hM : 1 ≤ M)
    (scalarStable : ∀ S, P S → ∀ i : Fin 4, ∀ v, P (S.setScalar (reg i.succ) v))
    (outputStable : ∀ S, P S → ∀ xs, P (S.setArray output xs))
    (cellRuns : ∀ S, P S → S.Bounded M → S.scalar (reg 1) < n →
      ∃ t ≤ c, ∃ T, Runs (storageBound R A M) cell S t T ∧ T.Bounded M ∧ P T ∧
        T.scalar result = f (S.scalar (reg 1)) ∧ T.array output = S.array output ∧
        ∀ i : Fin 4, T.scalar (reg i.castSucc) = S.scalar (reg i.castSucc))
    (S : Store R A) (hS : S.Bounded M) (hP : P S) (hn : S.scalar (reg 0) = n) :
    ∃ t ≤ n*(c+4)+6, ∃ T, Runs (storageBound R A M) (materialize reg output result cell) S t T ∧
      T.Bounded M ∧ P T ∧ T.array output = List.ofFn (fun i : Fin n => f i.val) := by
  have heq (i j : Fin 5) : reg i = reg j ↔ i = j := reg.injective.eq_iff
  have hnM : n ≤ M := hn ▸ hS.1 (reg 0)
  let init := [Atom.const (reg 3) 1,Atom.const (reg 4) 0,Atom.allocate output (reg 0) (reg 4)]
  have hvalid : ValidAtoms M init S := by
    simp [init,ValidAtoms,Atom.Valid,Atom.SmallResult,hM]
  obtain ⟨hinit,hinitB⟩ := atoms_runs hS init hvalid
  let U := applyAtoms init S
  have hU : U = ((S.setScalar (reg 3) 1).setScalar (reg 4) 0).setArray output (List.replicate n 0) := by
    simp [U,init,applyAtoms,Atom.apply,Store.setScalar,heq,hn]
  have hUP : P U := by
    rw [hU]
    exact outputStable _ (scalarStable _ (scalarStable _ hP 2 1) 3 0) _
  have hUn : U.scalar (reg 0) = n := by rw [hU]; simp [Store.setScalar,heq,hn]
  let I (i : ℕ) (T : Store R A) : Prop := P T ∧ T.Bounded M ∧ T.scalar (reg 0) = n ∧
    T.scalar (reg 1) = i ∧ T.scalar (reg 2) = n-i ∧ T.scalar (reg 3) = 1 ∧
    ArrayTabulation.Prefix f n i (T.array output)
  have hcopy : (U.setScalar (reg 2) (U.scalar (reg 0))).Bounded M :=
    hinitB.setScalar _ (hinitB.1 _)
  have hstart : I 0 ((U.setScalar (reg 2) (U.scalar (reg 0))).setScalar (reg 1) 0) := by
    refine ⟨scalarStable _ (scalarStable _ hUP 1 _) 0 _,hcopy.setScalar _ (Nat.zero_le M),?_,?_,?_,?_,?_⟩
    · simp [Store.setScalar,heq,hUn]
    · simp
    · simp [Store.setScalar,heq,hUn]
    · rw [hU]; simp [Store.setScalar,heq]
    · change ArrayTabulation.Prefix f n 0 (U.array output)
      rw [hU]
      simpa using ArrayTabulation.Prefix.zero f n
  have hcontrol : ∀ i ≤ n, ∀ T, I i T →
      T.scalar (reg 1) = i ∧ T.scalar (reg 2) = n-i ∧ T.scalar (reg 3) = 1 ∧
      T.size ≤ storageBound R A M := by
    intro i hi T hT
    exact ⟨hT.2.2.2.1,hT.2.2.2.2.1,hT.2.2.2.2.2.1,Store.size_le_of_bounded hT.2.1⟩
  have hstep : ∀ i < n, ∀ T, I i T →
      ∃ t ≤ c+1, ∃ V, Runs (storageBound R A M) (.seq cell (.atom (.write output (reg 1) result))) T t V ∧
        V.scalar (reg 1) = i ∧ V.scalar (reg 2) = n-i ∧ V.scalar (reg 3) = 1 ∧
        (V.setScalar (reg 1) (i+1)).size ≤ storageBound R A M ∧
        I (i+1) (advance (reg 1) (reg 2) V) := by
    intro i hi T hT
    obtain ⟨t,ht,V,hcell,hVB,hVP,hvalue,harray,hframe⟩ :=
      cellRuns T hT.1 hT.2.1 (by rw [hT.2.2.2.1]; exact hi)
    have hv0 : V.scalar (reg 0) = n := (hframe 0).trans hT.2.2.1
    have hv1 : V.scalar (reg 1) = i := (hframe 1).trans hT.2.2.2.1
    have hv2 : V.scalar (reg 2) = n-i := (hframe 2).trans hT.2.2.2.2.1
    have hv3 : V.scalar (reg 3) = 1 := (hframe 3).trans hT.2.2.2.2.2.1
    have hprefix : ArrayTabulation.Prefix f n i (V.array output) := by
      rw [harray]; exact hT.2.2.2.2.2.2
    have hwrite := atom_runs hVB (Atom.write output (reg 1) result)
      (by change V.scalar (reg 1) < (V.array output).length; rw [hv1,hprefix.1]; exact hi) trivial
    let W := (Atom.write output (reg 1) result).apply V
    have hWB : W.Bounded M := Atom.apply_bounded hVB _ trivial
    have hWP : P W := outputStable _ hVP _
    have hWprefix : ArrayTabulation.Prefix f n (i+1) (W.array output) := by
      have hval : V.scalar result = f i := by simpa only [hT.2.2.2.1] using hvalue
      simpa only [W,Atom.apply,Store.setArray_same,hv1,hval] using hprefix.write hi
    have hnextB : (advance (reg 1) (reg 2) W).Bounded M :=
      (hWB.setScalar _ (by change V.scalar (reg 1)+1 ≤ M; rw [hv1]; omega)).setScalar _
        ((Nat.sub_le _ _).trans (hWB.1 _))
    refine ⟨t+1,by omega,W,hcell.seq hwrite,hv1,hv2,hv3,?_,?_,hnextB,?_,?_,?_,?_,?_⟩
    · exact Store.size_le_of_bounded (hWB.setScalar _ (by omega))
    · exact scalarStable _ (scalarStable _ hWP 0 _) 1 _
    · simp [advance,Store.setScalar,heq,W,Atom.apply,hv0]
    · simp [advance,Store.setScalar,heq,W,Atom.apply,hv1]
    · simp [advance,Store.setScalar,heq,W,Atom.apply,hv2]
      omega
    · simp [advance,Store.setScalar,heq,W,Atom.apply,hv3]
    · exact hWprefix
  obtain ⟨t,ht,T,hloop,hT⟩ := countedLoop_runs (storageBound R A M)
    (reg 1) (reg 2) (reg 0) (reg 3) _ n (c+1) I U
    (Store.size_le_of_bounded hinitB) (Store.size_le_of_bounded hcopy) hstart hcontrol
    (reg.injective.ne (by decide)) (reg.injective.ne (by decide)) hstep
  have hce : c+1+3 = c+4 := by omega
  rw [hce] at ht
  refine ⟨3+t,by omega,T,?_,hT.2.1,hT.1,hT.2.2.2.2.2.2.complete⟩
  exact hinit.seq hloop

end GroupWL.MachinePrograms.NatArrayLanguage
