import GroupWL.MachinePrograms.NatArrayPredicateSearch

namespace GroupWL.MachinePrograms.NatArrayPredicateSearch
open NatArrayLanguage
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
variable {R A : Type*} [DecidableEq R] [DecidableEq A] [Fintype R] [Fintype A]

private theorem mapped_frame (p : Program R A) (r : Control) :
    (Sum.inr r : Reg R)∉(p.map Sum.inl (Sum.inl : A→Arr A)).scalarWrites := by
  induction p with
  | skip => simp [Program.map,Program.scalarWrites]
  | atom a => cases a <;> simp [Program.map,Atom.map,Program.scalarWrites,Atom.scalarWrites]
  | seq p q ih ih' => simp [Program.map,Program.scalarWrites,ih,ih']
  | branch _ p q ih ih' => simp [Program.map,Program.scalarWrites,ih,ih']
  | «while» _ p ih => exact ih

theorem body_frame {p : Program R A} {input output : R} {B S T t}
    (h : Runs B (body p input output) S t T) (r : Control)
    (hr : r∈({.limit,.one,.index,.todo} : Finset Control)) : T.scalar (.inr r)=S.scalar (.inr r) := by
  apply h.scalar_eq_of_not_mem
  have hm := mapped_frame p r
  cases r <;> simp_all [body,latch,atoms,NatArrayLanguage.sequence,Program.scalarWrites,Atom.scalarWrites]

private structure Invariant (Good : Store R A → Prop) (P : ℕ→Prop) [DecidablePred P]
    (M N i : ℕ) (S : State R A) : Prop where
  bounded : S.Bounded M
  good : Good S.left
  index_eq : S.scalar (.inr .index)=i
  todo_eq : S.scalar (.inr .todo)=N-i
  one_eq : S.scalar (.inr .one)=1
  found_eq : S.scalar (.inr .found)=if (hit P i).isSome then 1 else 0
  result_eq : S.scalar (.inr .result)=(hit P i).getD 0

theorem loop_runs (p : Program R A) (input output : R)
    (Good : Store R A → Prop) (P : ℕ→Prop) [DecidablePred P]
    (S : State R A) (M N c : ℕ) (hb : S.Bounded M) (hM : 1≤M)
    (hg : Good S.left) (hsetup : ∀S i,Good S → Good (S.setScalar input i))
    (hcode : ∀U i,U.Bounded M → Good U → U.scalar input=i → i<N →
      ∃t≤c,∃V,Runs (storageBound R A M) p U t V ∧ V.Bounded M ∧ Good V ∧ (V.scalar output=1 ↔ P i))
    (hN : S.scalar (.inr .limit)=N) (hone : S.scalar (.inr .one)=1)
    (hfound : S.scalar (.inr .found)=0) (hresult : S.scalar (.inr .result)=0) :
    ∃t≤N*(c+9)+3,∃T,Runs (storageBound (Reg R) (Arr A) M)
      (countedLoop (.inr .index) (.inr .todo) (.inr .limit) (.inr .one) (body p input output)) S t T ∧
      T.Bounded M ∧ Good T.left ∧ T.scalar (.inr .found)=(if (hit P N).isSome then 1 else 0) ∧
      T.scalar (.inr .result)=(hit P N).getD 0 := by
  have hNM : N≤M := by simpa [hN] using hb.1 (.inr .limit)
  let I := Invariant Good P M N
  have hcopy := hb.setScalar (Sum.inr Control.todo) (show S.scalar (.inr .limit)≤M from hb.1 _)
  have hstart : I 0 ((S.setScalar (.inr .todo) (S.scalar (.inr .limit))).setScalar (.inr .index) 0) := by
    refine ⟨hcopy.setScalar _ (by omega),?_,?_,?_,?_,?_,?_⟩
    · simpa using hg
    · simp
    · simp [hN]
    · simp [hone]
    · simp [hfound]
    · simp [hresult]
  have hcontrol : ∀i≤N,∀T,I i T → T.scalar (.inr .index)=i ∧ T.scalar (.inr .todo)=N-i ∧
      T.scalar (.inr .one)=1 ∧ T.size≤storageBound (Reg R) (Arr A) M := by
    intro i hi T hT
    exact ⟨hT.index_eq,hT.todo_eq,hT.one_eq,Store.size_le_of_bounded hT.bounded⟩
  have hstep : ∀i<N,∀T,I i T → ∃t≤c+6,∃U,Runs (storageBound (Reg R) (Arr A) M)
      (body p input output) T t U ∧ U.scalar (.inr .index)=i ∧ U.scalar (.inr .todo)=N-i ∧
      U.scalar (.inr .one)=1 ∧ (U.setScalar (.inr .index) (i+1)).size≤storageBound (Reg R) (Arr A) M ∧
      I (i+1) (advance (.inr .index) (.inr .todo) U) := by
    intro i hi T hT
    obtain ⟨t,ht,U,run,hU,hgU,hf,hr⟩ := body_runs p input output Good P T M N c i hT.bounded hM hi
      hT.good hsetup hcode hT.index_eq hT.one_eq hT.found_eq hT.result_eq
    have hui := (body_frame run .index (by decide)).trans hT.index_eq
    have hut := (body_frame run .todo (by decide)).trans hT.todo_eq
    have huone := (body_frame run .one (by decide)).trans hT.one_eq
    have hmid := hU.setScalar (Sum.inr Control.index) (show i+1≤M by omega)
    refine ⟨t,ht,U,run,hui,hut,huone,Store.size_le_of_bounded hmid,?_⟩
    refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [advance,hui] using hmid.setScalar (Sum.inr Control.todo)
        (show U.scalar (.inr .todo)-1≤M by rw [hut]; omega)
    · simpa [advance] using hgU
    · simp [advance,hui]
    · simp [advance,hut]; omega
    · simpa [advance] using huone
    · simpa [advance] using hf
    · simpa [advance] using hr
  obtain ⟨t,ht,T,run,hT⟩ := countedLoop_runs (storageBound (Reg R) (Arr A) M)
    (.inr .index) (.inr .todo) (.inr .limit) (.inr .one) (body p input output) N (c+6) I S
    (Store.size_le_of_bounded hb) (Store.size_le_of_bounded hcopy) hstart hcontrol
    (by simp) (by simp) hstep
  exact ⟨t,by omega,T,run,hT.bounded,hT.good,hT.found_eq,hT.result_eq⟩

theorem search_runs (p : Program R A) (input output : R)
    (Good : Store R A → Prop) (P : ℕ→Prop) [DecidablePred P]
    (S : State R A) (M N c : ℕ) (hb : S.Bounded M) (hM : 1≤M)
    (hg : Good S.left) (hsetup : ∀S i,Good S → Good (S.setScalar input i))
    (hcode : ∀U i,U.Bounded M → Good U → U.scalar input=i → i<N →
      ∃t≤c,∃V,Runs (storageBound R A M) p U t V ∧ V.Bounded M ∧ Good V ∧ (V.scalar output=1 ↔ P i))
    (hN : S.scalar (.inr .limit)=N) :
    ∃t≤N*(c+9)+6,∃T,Runs (storageBound (Reg R) (Arr A) M) (search p input output) S t T ∧
      T.Bounded M ∧ Good T.left ∧ T.scalar (.inr .found)=(if (hit P N).isSome then 1 else 0) ∧
      T.scalar (.inr .result)=(hit P N).getD 0 := by
  let pre : List (Atom (Reg R) (Arr A)) := [.const (.inr .one) 1,.const (.inr .found) 0,.const (.inr .result) 0]
  have hv : ValidAtoms M pre S := by simp [pre,ValidAtoms,Atom.Valid,Atom.SmallResult,hM]
  obtain ⟨init,hU⟩ := atoms_runs hb pre hv
  let U := applyAtoms pre S
  obtain ⟨t,ht,T,run,hT,hgT,hf,hr⟩ := loop_runs p input output Good P U M N c hU hM
    (by simpa [U,applyAtoms,pre,Atom.apply] using hg) hsetup hcode
    (by simp [U,applyAtoms,pre,Atom.apply,hN]) (by simp [U,applyAtoms,pre,Atom.apply])
    (by simp [U,applyAtoms,pre,Atom.apply]) (by simp [U,applyAtoms,pre,Atom.apply])
  exact ⟨3+t,by omega,T,.seq init run,hT,hgT,hf,hr⟩

theorem hit_exists (P : ℕ→Prop) [DecidablePred P] (N : ℕ) (hex : ∃i<N,P i) :
    ∃i<N,hit P N=some i ∧ P i := by
  cases h : hit P N with
  | none =>
    obtain ⟨i,hi,hP⟩ := hex
    have hn := List.find?_eq_none.mp h i (List.mem_range.mpr hi)
    simp [hP] at hn
  | some i =>
    exact ⟨i,List.mem_range.mp (List.mem_of_find?_eq_some h),rfl,by simpa using List.find?_some h⟩

theorem hit_isSome_iff (P : ℕ→Prop) [DecidablePred P] (N : ℕ) :
    (hit P N).isSome=true ↔ ∃i<N,P i := by
  constructor
  · intro hp
    cases h : hit P N with
    | none => simp [h] at hp
    | some i => exact ⟨i,List.mem_range.mp (List.mem_of_find?_eq_some h),by simpa using List.find?_some h⟩
  · intro hex
    obtain ⟨i,hi,hh,hp⟩ := hit_exists P N hex
    simp [hh]

end GroupWL.MachinePrograms.NatArrayPredicateSearch
