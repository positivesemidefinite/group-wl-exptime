import GroupWL.MachinePrograms.GroupMapPrograms

/-! A quadratic scan decides whether a numeric function is an injective
multiplication-preserving map. -/
namespace GroupWL.MachinePrograms.GroupMapPrograms

open NatArrayLanguage
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def validationPrelude : List (Atom Reg Arr) := [
  .const .one 1,.const .result 1,.binary .mul .total .sourceOrder .sourceOrder]
def validate : Code := .seq (atoms validationPrelude)
  (countedLoop .position .todo .total .one checkPosition)
def prefixValid (n m : ℕ) (source target images : List ℕ) (k : ℕ) : Prop :=
  ∀ i<k,pairValid n m source target images (i/n) (i%n)
instance (n m : ℕ) (source target images : List ℕ) (k : ℕ) :
    Decidable (prefixValid n m source target images k) := inferInstanceAs (Decidable (∀ i<k,_))

theorem prefixValid_succ (n m : ℕ) (source target images : List ℕ) (i : ℕ) :
    prefixValid n m source target images (i+1) ↔ prefixValid n m source target images i ∧
      pairValid n m source target images (i/n) (i%n) := by
  constructor
  · intro h; exact ⟨fun j hj => h j (by omega),h i (by omega)⟩
  · rintro ⟨h,hi⟩ j hj
    by_cases he : j=i
    · exact he ▸ hi
    · exact h j (by omega)

private structure ValidationState (S : State) (n m M i : ℕ) (T : State) : Prop where
  bounded : T.Bounded M
  sourceOrder_eq : T.scalar .sourceOrder=n
  targetOrder_eq : T.scalar .targetOrder=m
  position_eq : T.scalar .position=i
  todo_eq : T.scalar .todo=n*n-i
  one_eq : T.scalar .one=1
  arrays_eq : T.array=S.array
  result_eq : T.scalar .result=if prefixValid n m (S.array .source) (S.array .target) (S.array .images) i then 1 else 0

private def fixedRegisters : Finset Reg := {.sourceOrder,.targetOrder,.one,.position,.todo,.total}
theorem checkPosition_scalarFrame {B S T t} (h : Runs B checkPosition S t T)
    (r : Reg) (hr : r∈fixedRegisters) : T.scalar r=S.scalar r := by
  apply h.scalar_eq_of_not_mem
  have hdis : ∀ r∈fixedRegisters,r∉checkPosition.scalarWrites := by decide
  exact hdis r hr

theorem checkPosition_arrayFrame {B S T t} (h : Runs B checkPosition S t T) :
    T.array=S.array := by
  funext a
  exact h.array_eq_of_not_mem a ((by decide : ∀a,a∉checkPosition.arrayWrites) a)

theorem validationLoop_runs (S : State) (n m M : ℕ)
    (hb : S.Bounded M) (hn : S.scalar .sourceOrder=n) (hm : S.scalar .targetOrder=m)
    (hone : S.scalar .one=1) (htotal : S.scalar .total=n*n)
    (hresult : S.scalar .result=1) (hnpos : 0<n) (hmpos : 0<m)
    (hsource : (S.array .source).length=n*n) (htarget : (S.array .target).length=m*m)
    (himages : (S.array .images).length=n)
    (hsourceVals : ∀ v∈S.array .source,v<n) (himageVals : ∀ v∈S.array .images,v<m)
    (hroom : n*n≤M) (hroom' : m*m≤M) :
    ∃ t≤19*(n*n)+3,∃ T,Runs (storageBound Reg Arr M)
      (countedLoop .position .todo .total .one checkPosition) S t T ∧ T.Bounded M ∧
      T.scalar .result=if prefixValid n m (S.array .source) (S.array .target) (S.array .images) (n*n) then 1 else 0 := by
  let I := ValidationState S n m M
  have hcopy : (S.setScalar .todo (S.scalar .total)).Bounded M :=
    hb.setScalar _ (by simpa [htotal] using hroom)
  have hstart : I 0 ((S.setScalar .todo (S.scalar .total)).setScalar .position 0) := by
    refine ⟨hcopy.setScalar _ (by omega),?_,?_,?_,?_,?_,?_,?_⟩
    · simp [hn]
    · simp [hm]
    · simp
    · simp [htotal]
    · simp [hone]
    · rfl
    · simp [hresult,prefixValid]
  have hcontrol : ∀ i≤n*n,∀ T,I i T →
      T.scalar .position=i ∧ T.scalar .todo=n*n-i ∧ T.scalar .one=1 ∧
        T.size≤storageBound Reg Arr M := by
    intro i hi T hT
    exact ⟨hT.position_eq,hT.todo_eq,hT.one_eq,Store.size_le_of_bounded hT.bounded⟩
  have hstep : ∀ i<n*n,∀ T,I i T →
      ∃ t≤16,∃ U,Runs (storageBound Reg Arr M) checkPosition T t U ∧
        U.scalar .position=i ∧ U.scalar .todo=n*n-i ∧ U.scalar .one=1 ∧
        (U.setScalar .position (i+1)).size≤storageBound Reg Arr M ∧
        I (i+1) (advance .position .todo U) := by
    intro i hi T hT
    obtain ⟨U,run,hU,hres⟩ := checkPosition_runs T n m M i hT.bounded hT.sourceOrder_eq
      hT.targetOrder_eq hT.position_eq hi hmpos (by simpa [hT.arrays_eq] using hsource)
      (by simpa [hT.arrays_eq] using htarget) (by simpa [hT.arrays_eq] using himages)
      (by simpa [hT.arrays_eq] using hsourceVals) (by simpa [hT.arrays_eq] using himageVals)
      (by rw [hT.result_eq]; split_ifs <;> omega) hroom hroom'
    have frame (r : Reg) (hr : r∈fixedRegisters) := checkPosition_scalarFrame run r hr
    have hpos : U.scalar .position=i := (frame _ (by decide)).trans hT.position_eq
    have htodo : U.scalar .todo=n*n-i := (frame _ (by decide)).trans hT.todo_eq
    have h1 : U.scalar .one=1 := (frame _ (by decide)).trans hT.one_eq
    have hmid := hU.setScalar Reg.position (show i+1≤M by omega)
    refine ⟨16,le_rfl,U,run,hpos,htodo,h1,Store.size_le_of_bounded hmid,?_⟩
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [advance,hpos] using hmid.setScalar Reg.todo
        (show U.scalar .todo-1≤M by rw [htodo]; omega)
    · simpa [advance] using (frame .sourceOrder (by decide)).trans hT.sourceOrder_eq
    · simpa [advance] using (frame .targetOrder (by decide)).trans hT.targetOrder_eq
    · simp [advance,hpos]
    · simp [advance,htodo]; omega
    · simpa [advance] using h1
    · exact (checkPosition_arrayFrame run).trans hT.arrays_eq
    · change U.scalar .result = _
      rw [hres,hT.result_eq,hT.arrays_eq]
      simp only [prefixValid_succ]
      by_cases hp : prefixValid n m (S.array .source) (S.array .target) (S.array .images) i <;>
        by_cases ht : pairValid n m (S.array .source) (S.array .target) (S.array .images) (i/n) (i%n) <;> simp [hp,ht]
  obtain ⟨t,ht,T,run,hT⟩ := countedLoop_runs (storageBound Reg Arr M)
    .position .todo .total .one checkPosition (n*n) 16 I S
    (Store.size_le_of_bounded hb) (Store.size_le_of_bounded hcopy) hstart hcontrol
    (by decide) (by decide) hstep
  exact ⟨t,by omega,T,run,hT.bounded,hT.result_eq⟩

theorem validate_runs (S : State) (n m M : ℕ)
    (hb : S.Bounded M) (hn : S.scalar .sourceOrder=n) (hm : S.scalar .targetOrder=m)
    (hnpos : 0<n) (hmpos : 0<m)
    (hsource : (S.array .source).length=n*n) (htarget : (S.array .target).length=m*m)
    (himages : (S.array .images).length=n)
    (hsourceVals : ∀ v∈S.array .source,v<n) (himageVals : ∀ v∈S.array .images,v<m)
    (hroom : n*n≤M) (hroom' : m*m≤M) :
    ∃ t≤19*(n*n)+6,∃ T,Runs (storageBound Reg Arr M) validate S t T ∧ T.Bounded M ∧
      T.scalar .result=if prefixValid n m (S.array .source) (S.array .target) (S.array .images) (n*n) then 1 else 0 := by
  have hM : 1≤M := by nlinarith
  have hv : ValidAtoms M validationPrelude S := by
    simp [validationPrelude,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,
      BinaryOp.eval,Store.setScalar,hn,hM,hroom]
  obtain ⟨pre,hU⟩ := atoms_runs hb validationPrelude hv
  let U := applyAtoms validationPrelude S
  obtain ⟨t,ht,T,run,hT,ho⟩ := validationLoop_runs U n m M hU
    (by simp [U,applyAtoms,validationPrelude,Atom.apply,Store.setScalar,hn])
    (by simp [U,applyAtoms,validationPrelude,Atom.apply,Store.setScalar,hm])
    (by simp [U,applyAtoms,validationPrelude,Atom.apply,Store.setScalar])
    (by simp [U,applyAtoms,validationPrelude,Atom.apply,Store.setScalar,BinaryOp.eval,hn])
    (by simp [U,applyAtoms,validationPrelude,Atom.apply,Store.setScalar])
    hnpos hmpos hsource htarget himages hsourceVals himageVals hroom hroom'
  exact ⟨3+t,by omega,T,.seq pre run,hT,ho⟩

theorem prefixValid_complete {n m : ℕ} (hn : 0<n) (source target images : List ℕ) :
    prefixValid n m source target images (n*n) ↔
      ∀ x y : Fin n,pairValid n m source target images x.val y.val := by
  constructor
  · intro h x y
    have hi : y.val+n*x.val<n*n := by nlinarith [x.isLt,y.isLt]
    have hh := h _ hi
    simpa only [Nat.add_mul_div_left _ _ hn,Nat.div_eq_of_lt y.isLt,Nat.zero_add,
      Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt y.isLt] using hh
  · intro h i hi
    exact h ⟨i/n,Nat.div_lt_of_lt_mul hi⟩ ⟨i%n,Nat.mod_lt _ hn⟩

end GroupWL.MachinePrograms.GroupMapPrograms
