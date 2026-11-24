import GroupWL.MachinePrograms.CandidateDecoderBody
import GroupWL.MachinePrograms.CandidateDecoderBounds

namespace GroupWL.MachinePrograms.CandidateDecoder
open NatArrayLanguage
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

private structure Invariant (p D q M j : ℕ) [Fact p.Prime] (S : State) : Prop where
  bounded : S.Bounded M
  data : Data p j q S
  level_eq : S.scalar (.inr .level)=j
  todo_eq : S.scalar (.inr .todo)=D-j
  one_eq : S.scalar (.inr .one)=1
  prime_eq : S.scalar (.inr .prime)=p
  order_eq : S.scalar (.inr .order)=p^j
  code_eq : S.scalar (.inr .code)=q/NumericCandidateCodes.radix p j

theorem loop_runs {p : ℕ} [Fact p.Prime] (S : State) (M D q : ℕ)
    (hb : S.Bounded M) (hdata : Data p 0 q S)
    (hd : S.scalar (.inr .dimension)=D) (hone : S.scalar (.inr .one)=1)
    (hp : S.scalar (.inr .prime)=p) (hn : S.scalar (.inr .order)=1)
    (hq : S.scalar (.inr .code)=q)
    (hroom : ((p^D)*(p^D))*((p^D)*(p^D))≤M) (hpow : (p^D)^D≤M) (hexp : 2*p≤M) :
    ∃t≤D*(CandidateExtend.budget p (p^D) D+3*D+20)+3,∃T,
      Runs (storageBound Reg Arr M)
        (countedLoop (.inr .level) (.inr .todo) (.inr .dimension) (.inr .one) body) S t T ∧
      T.Bounded M ∧ Data p D q T ∧ T.scalar (.inr .order)=p^D ∧
      T.scalar (.inr .code)=q/NumericCandidateCodes.radix p D := by
  have hDM : D≤M := by simpa [hd] using hb.1 (.inr .dimension)
  have hN : 1≤p^D := one_le_pow₀ (Fact.out : p.Prime).one_le
  have hfour : (p^D)^4≤M := by convert hroom using 1 <;> ring
  let C := CandidateExtend.budget p (p^D) D+3*D+17
  let I : ℕ → State → Prop := fun j T => Invariant p D q M j T
  have hcopy := hb.setScalar (Sum.inr Control.todo) (show S.scalar (.inr .dimension)≤M from hb.1 _)
  have hstart : I 0 ((S.setScalar (.inr .todo) (S.scalar (.inr .dimension))).setScalar (.inr .level) 0) := by
    refine ⟨hcopy.setScalar _ (by omega),?_,?_,?_,?_,?_,?_,?_⟩
    · exact (hdata.scalarUpdate .todo _ (by decide)).scalarUpdate .level _ (by decide)
    · simp
    · simp [hd]
    · simp [hone]
    · simp [hp]
    · simp [hn]
    · simp [hq,NumericCandidateCodes.radix]
  have hcontrol : ∀j≤D,∀T,I j T → T.scalar (.inr .level)=j ∧ T.scalar (.inr .todo)=D-j ∧
      T.scalar (.inr .one)=1 ∧ T.size≤storageBound Reg Arr M := by
    intro j hj T hT
    exact ⟨hT.level_eq,hT.todo_eq,hT.one_eq,Store.size_le_of_bounded hT.bounded⟩
  have hstep : ∀j<D,∀T,I j T → ∃t≤C,∃U,Runs (storageBound Reg Arr M) body T t U ∧
      U.scalar (.inr .level)=j ∧ U.scalar (.inr .todo)=D-j ∧ U.scalar (.inr .one)=1 ∧
      (U.setScalar (.inr .level) (j+1)).size≤storageBound Reg Arr M ∧
      I (j+1) (advance (.inr .level) (.inr .todo) U) := by
    intro j hj T hT
    have hjD : j≤D := by omega
    have hpn : p^j≤p^D := Nat.pow_le_pow_right (Fact.out : p.Prime).one_le hjD
    have hpn' : p^(j+1)≤p^D := Nat.pow_le_pow_right (Fact.out : p.Prime).one_le (by omega)
    have hr : (p^j)*(p^j)*((p^j)*(p^j))≤M := by
      exact (by gcongr : (p^j)*(p^j)*((p^j)*(p^j))≤(p^D)*(p^D)*((p^D)*(p^D))).trans hroom
    have hpw : (p^j)^j≤M := ((Nat.pow_le_pow_left hpn j).trans (Nat.pow_le_pow_right hN hjD)).trans hpow
    have hcb : (p*(p^j))^3≤M := by
      rw [←pow_succ']
      exact ((Nat.pow_le_pow_left hpn' 3).trans (Nat.pow_le_pow_right hN (by decide : 3≤4))).trans hfour
    have hnext : p^(j+1)≤M := hpn'.trans (by
      have h := Nat.pow_le_pow_right hN (by decide : 1≤4)
      simpa using h.trans hfour)
    obtain ⟨t,ht,U,run,hU,hdataU,hnU,hqU⟩ := body_runs T M q hT.bounded hT.data hT.order_eq hT.level_eq
      hT.prime_eq hT.code_eq hr hpw hexp hcb hnext
    have hbudget := CandidateExtend.budget_mono (p:=p) hpn hjD hN
    have hlevel := (body_frame run .level (by decide)).trans hT.level_eq
    have htodo := (body_frame run .todo (by decide)).trans hT.todo_eq
    have h1 := (body_frame run .one (by decide)).trans hT.one_eq
    have hprime := (body_frame run .prime (by decide)).trans hT.prime_eq
    have hmid := hU.setScalar (Sum.inr Control.level) (show j+1≤M by omega)
    refine ⟨t,by dsimp [C]; omega,U,run,hlevel,htodo,h1,Store.size_le_of_bounded hmid,?_⟩
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [advance,hlevel] using hmid.setScalar (Sum.inr Control.todo)
        (show U.scalar (.inr .todo)-1≤M by rw [htodo]; omega)
    · exact (hdataU.scalarUpdate .level _ (by decide)).scalarUpdate .todo _ (by decide)
    · simp [advance,hlevel]
    · simp [advance,htodo]; omega
    · simpa [advance] using h1
    · simpa [advance] using hprime
    · simpa [advance] using hnU
    · simpa [advance] using hqU
  obtain ⟨t,ht,T,run,hT⟩ := countedLoop_runs (storageBound Reg Arr M)
    (.inr .level) (.inr .todo) (.inr .dimension) (.inr .one) body D C I S
    (Store.size_le_of_bounded hb) (Store.size_le_of_bounded hcopy) hstart hcontrol
    (by decide) (by decide) hstep
  exact ⟨t,by simpa [C,Nat.add_assoc] using ht,T,run,hT.bounded,hT.data,hT.order_eq,hT.code_eq⟩

theorem base_tableWord (p : ℕ) [Fact p.Prime] :
    GroupInitial.tableWord (NumericGroupGenerators.operation (NumericPGroupCandidates.baseGroup p))=[0] := by
  rfl

theorem decode_runs {p : ℕ} [Fact p.Prime] (S : State) (M D q : ℕ)
    (hb : S.Bounded M) (hd : S.scalar (.inr .dimension)=D) (hq : S.scalar (.inr .code)=q)
    (hroom : ((p^D)*(p^D))*((p^D)*(p^D))≤M) (hpow : (p^D)^D≤M) (hexp : 2*p≤M) :
    ∃t≤D*(CandidateExtend.budget p (p^D) D+3*D+20)+9,∃T,
      Runs (storageBound Reg Arr M) (decode p) S t T ∧ T.Bounded M ∧ Data p D q T ∧
      T.scalar (.inr .order)=p^D ∧ T.scalar (.inr .code)=q/NumericCandidateCodes.radix p D := by
  have h1 : 1≤M := by have := (Fact.out : p.Prime).pos; omega
  have hpM : p≤M := by omega
  have hv : ValidAtoms M (prepare p) S := by
    simp [prepare,ValidAtoms,Atom.Valid,Atom.SmallResult,h1,hpM]
  obtain ⟨pre,hU⟩ := atoms_runs hb (prepare p) hv
  let U := applyAtoms (prepare p) S
  have hdata : Data p 0 q U := by
    constructor
    · simp [U,applyAtoms,prepare,Atom.apply,Store.setScalar,Store.setArray,NumericPGroupCandidates.decode]
    · intro g hg
      simp only [NumericPGroupCandidates.decode,Option.some.injEq] at hg
      subst g
      rw [base_tableWord]
      simp [U,applyAtoms,prepare,Atom.apply,Store.setScalar,Store.setArray]
  obtain ⟨t,ht,T,run,hT,hdataT,hnT,hqT⟩ := loop_runs U M D q hU hdata
    (by simp [U,applyAtoms,prepare,Atom.apply,Store.setScalar,Store.setArray,hd])
    (by simp [U,applyAtoms,prepare,Atom.apply,Store.setScalar,Store.setArray])
    (by simp [U,applyAtoms,prepare,Atom.apply,Store.setScalar,Store.setArray])
    (by simp [U,applyAtoms,prepare,Atom.apply,Store.setScalar,Store.setArray])
    (by simp [U,applyAtoms,prepare,Atom.apply,Store.setScalar,Store.setArray,hq]) hroom hpow hexp
  exact ⟨6+t,by omega,T,.seq pre run,hT,hdataT,hnT,hqT⟩

end GroupWL.MachinePrograms.CandidateDecoder
