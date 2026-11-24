import GroupWL.MachinePrograms.GroupTablePrograms

/-! A cubic finite scan validates every group axiom on the materialized
multiplication table. Its loop bound is polynomial in the table order. -/
namespace GroupWL.MachinePrograms.GroupTablePrograms

open NatArrayLanguage
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def decodeTripleAtoms : List (Atom Reg Arr) := [
  .divmod .quotient .z .position .order,
  .divmod .x .y .quotient .order]

def checkPosition : Code := .seq (atoms decodeTripleAtoms) checkTriple

def validationPrelude : List (Atom Reg Arr) := [
  .const .one 1, .const .result 1,
  .binary .mul .total .order .order,
  .binary .mul .total .total .order]

def validate : Code := .seq (atoms validationPrelude)
  (countedLoop .position .todo .total .one checkPosition)

def prefixValid (n e : ℕ) (xs : List ℕ) (k : ℕ) : Prop :=
  ∀ i<k, tripleValid n e xs (i/n/n) ((i/n)%n) (i%n)

instance (n e : ℕ) (xs : List ℕ) (k : ℕ) : Decidable (prefixValid n e xs k) :=
  inferInstanceAs (Decidable (∀ i<k, _))

theorem prefixValid_succ (n e : ℕ) (xs : List ℕ) (i : ℕ) :
    prefixValid n e xs (i+1) ↔ prefixValid n e xs i ∧
      tripleValid n e xs (i/n/n) ((i/n)%n) (i%n) := by
  constructor
  · intro h; exact ⟨fun j hj => h j (by omega),h i (by omega)⟩
  · rintro ⟨h,hi⟩ j hj
    by_cases he : j=i
    · exact he ▸ hi
    · exact h j (by omega)

theorem checkPosition_runs (S : State) (n M e i : ℕ)
    (hb : S.Bounded M) (hn : S.scalar .order=n) (he : S.scalar .identity=e)
    (hi : S.scalar .position=i) (helt : e<n) (hilt : i<n^3)
    (hlen : (S.array .table).length=n*n) (hvals : ∀ v∈S.array .table,v<n)
    (hresult : S.scalar .result≤1) (hroom : n^3≤M) :
    ∃ T,Runs (storageBound Reg Arr M) checkPosition S 33 T ∧ T.Bounded M ∧
      T.scalar .result = S.scalar .result *
        (if tripleValid n e (S.array .table) (i/n/n) ((i/n)%n) (i%n) then 1 else 0) := by
  have hpos : 0<n := by omega
  have hsq : n*n≤M := by nlinarith [Nat.mul_le_mul_left (n*n) (show 1≤n by omega)]
  have hx : i/n/n<n := by
    rw [Nat.div_div_eq_div_mul]
    apply (Nat.div_lt_iff_lt_mul (by positivity : 0<n*n)).mpr
    nlinarith
  have hv : ValidAtoms M decodeTripleAtoms S := by
    simp [decodeTripleAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,
      Store.setScalar,hn,hpos]
  obtain ⟨hr,hU⟩ := atoms_runs hb decodeTripleAtoms hv
  let U := applyAtoms decodeTripleAtoms S
  have hscalar (r : Reg) (hrx : r≠.x) (hry : r≠.y) (hrz : r≠.z)
      (hrq : r≠.quotient) : U.scalar r=S.scalar r := by
    simp [U,applyAtoms,decodeTripleAtoms,Atom.apply,Store.setScalar,hrx,hry,hrz,hrq]
  obtain ⟨ht,hT,hout⟩ := checkTriple_runs U n M e (i/n/n) ((i/n)%n) (i%n) hU
    (by rw [hscalar _ (by decide) (by decide) (by decide) (by decide)]; exact hn)
    (by rw [hscalar _ (by decide) (by decide) (by decide) (by decide)]; exact he)
    (by simp [U,applyAtoms,decodeTripleAtoms,Atom.apply,Store.setScalar,hn,hi])
    (by simp [U,applyAtoms,decodeTripleAtoms,Atom.apply,Store.setScalar,hn,hi])
    (by simp [U,applyAtoms,decodeTripleAtoms,Atom.apply,Store.setScalar,hn,hi])
    helt hx (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos) hlen hvals
    (by rw [hscalar _ (by decide) (by decide) (by decide) (by decide)]; exact hresult) hsq
  refine ⟨applyAtoms checkTripleAtoms U,.seq hr ht,hT,?_⟩
  simpa only [hscalar .result (by decide) (by decide) (by decide) (by decide)] using hout

private structure ValidationState (S : State) (n e M i : ℕ) (T : State) : Prop where
  bounded : T.Bounded M
  order_eq : T.scalar .order=n
  identity_eq : T.scalar .identity=e
  position_eq : T.scalar .position=i
  todo_eq : T.scalar .todo=n^3-i
  one_eq : T.scalar .one=1
  table_eq : T.array .table=S.array .table
  result_eq : T.scalar .result=if prefixValid n e (S.array .table) i then 1 else 0

private def fixedRegisters : Finset Reg := {.order,.identity,.one,.position,.todo,.total}

theorem checkPosition_scalarFrame {B S T t} (h : Runs B checkPosition S t T)
    (r : Reg) (hr : r∈fixedRegisters) : T.scalar r=S.scalar r := by
  apply h.scalar_eq_of_not_mem
  have hdis : ∀ r∈fixedRegisters,r∉checkPosition.scalarWrites := by decide
  exact hdis r hr

theorem checkPosition_arrayFrame {B S T t} (h : Runs B checkPosition S t T) :
    T.array .table=S.array .table := h.array_eq_of_not_mem .table (by decide)

theorem validationLoop_runs (S : State) (n M e : ℕ)
    (hb : S.Bounded M) (hn : S.scalar .order=n) (he : S.scalar .identity=e)
    (hone : S.scalar .one=1) (htotal : S.scalar .total=n^3)
    (hresult : S.scalar .result=1) (helt : e<n)
    (hlen : (S.array .table).length=n*n) (hvals : ∀ v∈S.array .table,v<n)
    (hroom : n^3≤M) :
    ∃ t≤36*n^3+3,∃ T,
      Runs (storageBound Reg Arr M)
        (countedLoop .position .todo .total .one checkPosition) S t T ∧
      T.Bounded M ∧ T.scalar .result=if prefixValid n e (S.array .table) (n^3) then 1 else 0 := by
  let I := ValidationState S n e M
  have hcopy : (S.setScalar .todo (S.scalar .total)).Bounded M :=
    hb.setScalar _ (by simpa [htotal] using hroom)
  have hstart : I 0 ((S.setScalar .todo (S.scalar .total)).setScalar .position 0) := by
    refine ⟨hcopy.setScalar _ (by omega),?_,?_,?_,?_,?_,?_,?_⟩
    · simp [hn]
    · simp [he]
    · simp
    · simp [htotal]
    · simp [hone]
    · rfl
    · simp [hresult,prefixValid]
  have hcontrol : ∀ i≤n^3,∀ T,I i T →
      T.scalar .position=i ∧ T.scalar .todo=n^3-i ∧ T.scalar .one=1 ∧
        T.size≤storageBound Reg Arr M := by
    intro i hi T hT
    exact ⟨hT.position_eq,hT.todo_eq,hT.one_eq,Store.size_le_of_bounded hT.bounded⟩
  have hstep : ∀ i<n^3,∀ T,I i T →
      ∃ t≤33,∃ U,Runs (storageBound Reg Arr M) checkPosition T t U ∧
        U.scalar .position=i ∧ U.scalar .todo=n^3-i ∧ U.scalar .one=1 ∧
        (U.setScalar .position (i+1)).size≤storageBound Reg Arr M ∧
        I (i+1) (advance .position .todo U) := by
    intro i hi T hT
    obtain ⟨U,run,hU,hres⟩ := checkPosition_runs T n M e i hT.bounded hT.order_eq
      hT.identity_eq hT.position_eq helt hi (by simpa [hT.table_eq] using hlen)
      (by simpa [hT.table_eq] using hvals) (by rw [hT.result_eq]; split_ifs <;> omega) hroom
    have frame (r : Reg) (hr : r∈fixedRegisters) := checkPosition_scalarFrame run r hr
    have hpos : U.scalar .position=i := (frame _ (by decide)).trans hT.position_eq
    have htodo : U.scalar .todo=n^3-i := (frame _ (by decide)).trans hT.todo_eq
    have h1 : U.scalar .one=1 := (frame _ (by decide)).trans hT.one_eq
    have hmid := hU.setScalar Reg.position (show i+1≤M by omega)
    refine ⟨33,le_rfl,U,run,hpos,htodo,h1,Store.size_le_of_bounded hmid,?_⟩
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [advance,hpos] using hmid.setScalar Reg.todo
        (show U.scalar .todo-1≤M by rw [htodo]; omega)
    · simpa [advance] using (frame .order (by decide)).trans hT.order_eq
    · simpa [advance] using (frame .identity (by decide)).trans hT.identity_eq
    · simp [advance,hpos]
    · simp [advance,htodo]; omega
    · simpa [advance] using h1
    · simpa [advance] using (checkPosition_arrayFrame run).trans hT.table_eq
    · change U.scalar .result = _
      rw [hres,hT.result_eq,hT.table_eq]
      simp only [prefixValid_succ]
      by_cases hp : prefixValid n e (S.array .table) i <;>
        by_cases ht : tripleValid n e (S.array .table) (i/n/n) ((i/n)%n) (i%n) <;> simp [hp,ht]
  obtain ⟨t,ht,T,run,hT⟩ := countedLoop_runs (storageBound Reg Arr M)
    .position .todo .total .one checkPosition (n^3) 33 I S
    (Store.size_le_of_bounded hb) (Store.size_le_of_bounded hcopy) hstart hcontrol
    (by decide) (by decide) hstep
  exact ⟨t,by omega,T,run,hT.bounded,hT.result_eq⟩

theorem validate_runs (S : State) (n M e : ℕ)
    (hb : S.Bounded M) (hn : S.scalar .order=n) (he : S.scalar .identity=e)
    (helt : e<n) (hlen : (S.array .table).length=n*n)
    (hvals : ∀ v∈S.array .table,v<n) (hroom : n^3≤M) :
    ∃ t≤36*n^3+7,∃ T,Runs (storageBound Reg Arr M) validate S t T ∧
      T.Bounded M ∧ T.scalar .result=if prefixValid n e (S.array .table) (n^3) then 1 else 0 := by
  have hpos : 0<n := by omega
  have hM : 1≤M := by have := one_le_pow₀ (show 1≤n by omega) (n:=3); omega
  have hsq : n*n≤M := by nlinarith [Nat.mul_le_mul_left (n*n) (show 1≤n by omega)]
  have hv : ValidAtoms M validationPrelude S := by
    simp [validationPrelude,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,
      BinaryOp.eval,Store.setScalar,hn,hM,hsq]
    nlinarith
  obtain ⟨hr,hU⟩ := atoms_runs hb validationPrelude hv
  let U := applyAtoms validationPrelude S
  obtain ⟨t,ht,T,run,hT,hout⟩ := validationLoop_runs U n M e hU
    (by simp [U,applyAtoms,validationPrelude,Atom.apply,Store.setScalar,hn])
    (by simp [U,applyAtoms,validationPrelude,Atom.apply,Store.setScalar,he])
    (by simp [U,applyAtoms,validationPrelude,Atom.apply,Store.setScalar])
    (by simp [U,applyAtoms,validationPrelude,Atom.apply,Store.setScalar,BinaryOp.eval,hn]; ring)
    (by simp [U,applyAtoms,validationPrelude,Atom.apply,Store.setScalar])
    helt hlen hvals hroom
  exact ⟨4+t,by omega,T,.seq hr run,hT,hout⟩

theorem prefixValid_complete {n e : ℕ} (hn : 0<n) (xs : List ℕ) :
    prefixValid n e xs (n^3) ↔
      ∀ x y z : Fin n,tripleValid n e xs x.val y.val z.val := by
  constructor
  · intro h x y z
    have hrow : x.val*n+y.val+1≤n*n := by
      have := table_index_lt x.isLt y.isLt
      omega
    have hmul := Nat.mul_le_mul_right n hrow
    have hi : z.val+n*(y.val+n*x.val)<n^3 := by nlinarith [z.isLt]
    have hh := h _ hi
    simpa only [Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt z.isLt,
      Nat.div_eq_of_lt y.isLt,Nat.zero_add,Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt z.isLt,Nat.mod_eq_of_lt y.isLt] using hh
  · intro h i hi
    have hx : i/n/n<n := by
      rw [Nat.div_div_eq_div_mul]
      apply (Nat.div_lt_iff_lt_mul (by positivity : 0<n*n)).mpr
      nlinarith
    exact h ⟨i/n/n,hx⟩ ⟨(i/n)%n,Nat.mod_lt _ hn⟩ ⟨i%n,Nat.mod_lt _ hn⟩

theorem validate_correct (S : State) (n M : ℕ) (identity : Fin n)
    (op : Fin n → Fin n → Fin n) (hb : S.Bounded M)
    (hn : S.scalar .order=n) (he : S.scalar .identity=identity.val)
    (hlen : (S.array .table).length=n*n) (hvals : ∀ v∈S.array .table,v<n)
    (hread : ∀ x y : Fin n,operation n (S.array .table) x.val y.val=(op x y).val)
    (hroom : n^3≤M) :
    ∃ t≤36*n^3+7,∃ T,Runs (storageBound Reg Arr M) validate S t T ∧
      T.Bounded M ∧ (T.scalar .result=1 ↔ VerifiedGroupTable.Valid identity op) := by
  obtain ⟨t,ht,T,run,hT,ho⟩ := validate_runs S n M identity.val hb hn he identity.isLt
    hlen hvals hroom
  refine ⟨t,ht,T,run,hT,?_⟩
  rw [ho]
  have hpos : 0<n := by have := identity.isLt; omega
  have hc := (prefixValid_complete hpos (S.array .table)).trans
    (tripleValid_iff hpos identity op (S.array .table) hread)
  simpa using hc

end GroupWL.MachinePrograms.GroupTablePrograms
