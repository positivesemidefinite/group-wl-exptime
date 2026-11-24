import GroupWL.MachinePrograms.ExtensionTablePrograms

/-! Full cyclic-extension table construction and its polynomial execution
bound, including allocation and every entry of the output table. -/
namespace GroupWL.MachinePrograms.ExtensionTablePrograms
open NatArrayLanguage
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

theorem Context.scalarUpdate {p n B : ℕ} {mul : Fin n → Fin n → Fin n} {θ : Fin n → Fin n}
    {c e : Fin n} {S : Store Reg Arr} (ctx : Context (p:=p) mul θ c e B S)
    (r : Reg) (v : ℕ) (hv : v≤B)
    (hr : r∉({.tail,.prime,.size,.square,.carry,.identity,.one} : Finset Reg)) :
    Context (p:=p) mul θ c e B (S.setScalar r v) := by
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hr
  refine ⟨ctx.bounded.setScalar r hv,?_,?_,?_,?_,?_,?_,?_,ctx.table_eq,ctx.image_eq,ctx.output_length⟩
  all_goals first
    | simpa [Ne.symm hr.1] using ctx.tail_eq
    | simpa [Ne.symm hr.2.1] using ctx.prime_eq
    | simpa [Ne.symm hr.2.2.1] using ctx.size_eq
    | simpa [Ne.symm hr.2.2.2.1] using ctx.square_eq
    | simpa [Ne.symm hr.2.2.2.2.1] using ctx.carry_eq
    | simpa [Ne.symm hr.2.2.2.2.2.1] using ctx.identity_eq
    | simpa [Ne.symm hr.2.2.2.2.2.2] using ctx.one_eq

def fillTable : Code := countedLoop .index .remaining .square .one cell

private structure Invariant {p n : ℕ} (hp : 0<p) (mul : Fin n → Fin n → Fin n)
    (θ : Fin n → Fin n) (c e : Fin n) (B i : ℕ) (S : Store Reg Arr) : Prop where
  context : Context (p:=p) mul θ c e B S
  index_eq : S.scalar .index=i
  remaining_eq : S.scalar .remaining=(p*n)*(p*n)-i
  filled : ∀ j < i,IndexedRefinement.read (S.array .output) j=
    IndexedRefinement.read (GroupInitial.tableWord (operation hp mul θ c e)) j

theorem fillTable_runs {p n B : ℕ} (hp : 0<p) (hn : 0<n)
    (mul : Fin n → Fin n → Fin n) (θ : Fin n → Fin n) (c e : Fin n)
    (S : Store Reg Arr) (ctx : Context (p:=p) mul θ c e B S)
    (hexp : 2*p≤B) (htable : n*n≤B) (hroom : (p*n)*(p*n)≤B) :
    ∃t≤(p*n)*(p*n)*(4*p+23)+3,∃T,Runs (storageBound Reg Arr B) fillTable S t T ∧
      Context (p:=p) mul θ c e B T ∧ T.array .output=GroupInitial.tableWord (operation hp mul θ c e) := by
  let N := p*n
  let I := Invariant hp mul θ c e B
  have hsize : p*n≤B := (Nat.le_mul_self _).trans hroom
  have hNroom : N*N≤B := hroom
  have ccopy := ctx.scalarUpdate .remaining (S.scalar .square) (by simpa [ctx.square_eq] using hroom) (by decide)
  have cstart := ccopy.scalarUpdate .index 0 (Nat.zero_le _) (by decide)
  have start : I 0 ((S.setScalar .remaining (S.scalar .square)).setScalar .index 0) := by
    refine ⟨cstart,by simp,by simp [ctx.square_eq],?_⟩
    intro j hj; omega
  have control : ∀i≤N*N,∀T,I i T → T.scalar .index=i ∧ T.scalar .remaining=N*N-i ∧
      T.scalar .one=1 ∧ T.size≤storageBound Reg Arr B := by
    intro i hi T hT
    exact ⟨hT.index_eq,hT.remaining_eq,hT.context.one_eq,Store.size_le_of_bounded hT.context.bounded⟩
  have step : ∀i<N*N,∀T,I i T → ∃t≤4*p+20,∃U,Runs (storageBound Reg Arr B) cell T t U ∧
      U.scalar .index=i ∧ U.scalar .remaining=N*N-i ∧ U.scalar .one=1 ∧
      (U.setScalar .index (i+1)).size≤storageBound Reg Arr B ∧ I (i+1) (advance .index .remaining U) := by
    intro i hi T hT
    let pair : Fin N × Fin N := finProdFinEquiv.symm ⟨i,hi⟩
    have hcode : (finProdFinEquiv pair).val=i := congrArg Fin.val (Equiv.apply_symm_apply finProdFinEquiv ⟨i,hi⟩)
    obtain ⟨t,ht,U,run,cU,hout⟩ := cell_runs hp hn mul θ c e pair.1 pair.2 T hT.context
      (by rw [hcode]; exact hT.index_eq) hexp htable hsize
    have hiU : U.scalar .index=i := by rw [run.scalar_eq_of_not_mem _ (by decide),hT.index_eq]
    have hrU : U.scalar .remaining=N*N-i := by rw [run.scalar_eq_of_not_mem _ (by decide),hT.remaining_eq]
    have cmid := cU.scalarUpdate .index (i+1) (by omega) (by decide)
    have cnext := cmid.scalarUpdate .remaining (U.scalar .remaining-1) (by rw [hrU]; omega) (by decide)
    refine ⟨t,ht,U,run,hiU,hrU,cU.one_eq,Store.size_le_of_bounded cmid.bounded,?_,?_,?_,?_⟩
    · simpa [advance,hiU] using cnext
    · simp [advance,hiU]
    · simp [advance,hrU,N]; omega
    · intro j hj
      change IndexedRefinement.read (U.array .output) j=_
      rw [hout,hT.index_eq]
      by_cases hji : i=j
      · subst j
        rw [IndexedRefinement.read,List.getElem?_set_self (by simpa [hT.context.output_length] using hi)]
        simp only [Option.getD_some]
        have hread := GroupInitial.tableWord_read (operation hp mul θ c e) pair.1 pair.2
        have hcode' : pair.2.val+(p*n)*pair.1.val=i := hcode
        simpa only [IndexedRefinement.read,hcode'] using hread.symm
      · simp only [IndexedRefinement.read,List.getElem?_set_ne hji]
        exact hT.filled j (by omega)
  obtain ⟨t,ht,T,run,hT⟩ := countedLoop_runs (storageBound Reg Arr B) .index .remaining .square .one
    cell (N*N) (4*p+20) I S (Store.size_le_of_bounded ctx.bounded) (Store.size_le_of_bounded ccopy.bounded)
    start control (by decide) (by decide) step
  refine ⟨t,ht,T,run,hT.context,?_⟩
  apply List.ext_getElem
  · simpa using hT.context.output_length
  · intro i hi hi'
    have h := hT.filled i (by simpa [hT.context.output_length] using hi)
    simpa only [IndexedRefinement.read,List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hi',Option.getD_some] using h

structure Input {p n : ℕ} (mul : Fin n → Fin n → Fin n) (θ : Fin n → Fin n)
    (c e : Fin n) (B : ℕ) (S : Store Reg Arr) : Prop where
  bounded : S.Bounded B
  tail_eq : S.scalar .tail=n
  prime_eq : S.scalar .prime=p
  carry_eq : S.scalar .carry=c.val
  identity_eq : S.scalar .identity=e.val
  table_eq : S.array .table=GroupInitial.tableWord mul
  image_eq : S.array .image=mapWord θ

def prepare : List (Atom Reg Arr) := [
  .const .one 1,.const .zero 0,.binary .mul .size .prime .tail,
  .binary .mul .square .size .size,.allocate .output .square .zero]

def generate : Code := .seq (atoms prepare) fillTable

theorem generate_runs {p n B : ℕ} (hp : 0<p) (hn : 0<n)
    (mul : Fin n → Fin n → Fin n) (θ : Fin n → Fin n) (c e : Fin n)
    (S : Store Reg Arr) (input : Input (p:=p) mul θ c e B S)
    (hexp : 2*p≤B) (htable : n*n≤B) (hroom : (p*n)*(p*n)≤B) :
    ∃t≤(p*n)*(p*n)*(4*p+23)+8,∃T,Runs (storageBound Reg Arr B) generate S t T ∧
      T.Bounded B ∧ T.array .output=GroupInitial.tableWord (operation hp mul θ c e) := by
  have h1 : 1≤B := by omega
  have hsize : p*n≤B := (Nat.le_mul_self _).trans hroom
  have valid : ValidAtoms B prepare S := by
    simp only [prepare,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,Function.update_apply,reduceCtorEq,if_false,if_true,input.tail_eq,input.prime_eq]
    exact ⟨trivial,h1,trivial,Nat.zero_le _,trivial,hsize,trivial,hroom,trivial,trivial,trivial⟩
  obtain ⟨rp,hP⟩ := atoms_runs input.bounded prepare valid
  let P := applyAtoms prepare S
  have ctx : Context (p:=p) mul θ c e B P := by
    refine ⟨hP,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    all_goals simp only [P,applyAtoms,prepare,List.foldl_cons,List.foldl_nil,Atom.apply,BinaryOp.eval,
      Store.setScalar,Store.setArray,Function.update_apply,reduceCtorEq,if_false,if_true,
      input.tail_eq,input.prime_eq,input.carry_eq,input.identity_eq,input.table_eq,input.image_eq,
      List.length_replicate]
  obtain ⟨t,ht,T,run,cT,hout⟩ := fillTable_runs hp hn mul θ c e P ctx hexp htable hroom
  exact ⟨5+t,by omega,T,.seq rp run,cT.bounded,hout⟩

theorem generate_runs_polynomial {p n B : ℕ} (hp : 0<p) (hn : 0<n)
    (mul : Fin n → Fin n → Fin n) (θ : Fin n → Fin n) (c e : Fin n)
    (S : Store Reg Arr) (input : Input (p:=p) mul θ c e B S)
    (hexp : 2*p≤B) (htable : n*n≤B) (hroom : (p*n)*(p*n)≤B) :
    ∃t≤40*(B+1)^2,∃T,Runs (40*(B+1)^2) generate S t T ∧
      T.Bounded B ∧ T.array .output=GroupInitial.tableWord (operation hp mul θ c e) := by
  obtain ⟨t,ht,T,run,hT,hout⟩ := generate_runs hp hn mul θ c e S input hexp htable hroom
  have htime : (p*n)*(p*n)*(4*p+23)+8≤40*(B+1)^2 := by
    have h := Nat.mul_le_mul hroom (show 4*p+23≤2*B+23 by omega)
    nlinarith
  have hspace : storageBound Reg Arr B≤40*(B+1)^2 := by
    unfold storageBound
    have hc : Fintype.card Reg+3*Fintype.card Arr≤40 := by decide
    exact Nat.mul_le_mul_right _ hc
  exact ⟨t,ht.trans htime,T,run.mono hspace,hT,hout⟩

end GroupWL.MachinePrograms.ExtensionTablePrograms
