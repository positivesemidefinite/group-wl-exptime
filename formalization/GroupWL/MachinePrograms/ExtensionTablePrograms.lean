import GroupWL.MachinePrograms.GroupInitial
import GroupWL.PGroupDecomposition

/-! Operational construction of the multiplication table for a cyclic
extension. All products and conjugation images are fetched from arrays. -/
namespace GroupWL.MachinePrograms.ExtensionTablePrograms
open NatArrayLanguage
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

inductive Reg where
  | tail | prime | size | square | carry | identity | one | zero
  | index | remaining | row | column | leftExponent | rightExponent | current | rightTail
  | exponent | carryFlag | residue | factor | iteration | iterationTodo | address | value
  deriving DecidableEq,Fintype
inductive Arr where
  | table | image | output
  deriving DecidableEq,Fintype
abbrev Code := Program Reg Arr

def mapWord {n : ℕ} (θ : Fin n → Fin n) : List ℕ := List.ofFn (fun x => (θ x).val)
@[simp] theorem mapWord_length {n : ℕ} (θ : Fin n → Fin n) : (mapWord θ).length=n := List.length_ofFn
@[simp] theorem mapWord_read {n : ℕ} (θ : Fin n → Fin n) (x : Fin n) :
    (mapWord θ)[x.val]?.getD 0=(θ x).val := by simp [mapWord,x.isLt]

def iterateMap : Code := countedLoop .iteration .iterationTodo .rightExponent .one
  (.atom (.read .current .image .current))

theorem iterateMap_runs {n B : ℕ} (θ : Fin n → Fin n) (x : Fin n) (j : ℕ)
    (S : Store Reg Arr) (hS : S.Bounded B) (hmap : S.array .image=mapWord θ)
    (hx : S.scalar .current=x.val) (hj : S.scalar .rightExponent=j) (hone : S.scalar .one=1) :
    ∃t≤4*j+3,∃T,Runs (storageBound Reg Arr B) iterateMap S t T ∧ T.Bounded B ∧
      T.scalar .current=(θ^[j] x).val := by
  have hjB : j≤B := by simpa [hj] using hS.1 .rightExponent
  let I : ℕ → Store Reg Arr → Prop := fun i T => T.Bounded B ∧
    T.scalar .iteration=i ∧ T.scalar .iterationTodo=j-i ∧ T.scalar .one=1 ∧
    T.array .image=mapWord θ ∧ T.scalar .current=(θ^[i] x).val
  have copyB := hS.setScalar Reg.iterationTodo (hS.1 Reg.rightExponent)
  have start : I 0 ((S.setScalar .iterationTodo (S.scalar .rightExponent)).setScalar .iteration 0) := by
    refine ⟨copyB.setScalar _ (Nat.zero_le _),?_,?_,?_,?_,?_⟩ <;> simp [hj,hone,hmap,hx]
  have control : ∀i≤j,∀T,I i T → T.scalar .iteration=i ∧ T.scalar .iterationTodo=j-i ∧
      T.scalar .one=1 ∧ T.size≤storageBound Reg Arr B := by
    intro i hi T hT
    exact ⟨hT.2.1,hT.2.2.1,hT.2.2.2.1,Store.size_le_of_bounded hT.1⟩
  have step : ∀i<j,∀T,I i T → ∃t≤1,∃U,
      Runs (storageBound Reg Arr B) (.atom (.read .current .image .current)) T t U ∧
      U.scalar .iteration=i ∧ U.scalar .iterationTodo=j-i ∧ U.scalar .one=1 ∧
      (U.setScalar .iteration (i+1)).size≤storageBound Reg Arr B ∧
      I (i+1) (advance .iteration .iterationTodo U) := by
    intro i hi T hT
    have valid : (Atom.read Reg.current Arr.image Reg.current).Valid T := by
      simpa [Atom.Valid,hT.2.2.2.2.1,hT.2.2.2.2.2] using (θ^[i] x).isLt
    have run := atom_runs hT.1 (.read .current .image .current) valid trivial
    let U := (Atom.read Reg.current Arr.image Reg.current).apply T
    have hU : U.Bounded B := Atom.apply_bounded hT.1 _ trivial
    have valU : U.scalar .current=(θ^[i+1] x).val := by
      simp only [U,Atom.apply,Store.setScalar_same,hT.2.2.2.2.1,hT.2.2.2.2.2,mapWord_read,Function.iterate_succ_apply']
    have ixU : U.scalar .iteration=i := by simpa [U,Atom.apply] using hT.2.1
    have remU : U.scalar .iterationTodo=j-i := by simpa [U,Atom.apply] using hT.2.2.1
    have oneU : U.scalar .one=1 := by simpa [U,Atom.apply] using hT.2.2.2.1
    have mid := hU.setScalar Reg.iteration (show i+1≤B by omega)
    refine ⟨1,le_rfl,U,run,ixU,remU,oneU,Store.size_le_of_bounded mid,?_,?_,?_,?_,?_,?_⟩
    · simpa [advance,ixU] using mid.setScalar Reg.iterationTodo (show U.scalar .iterationTodo-1≤B by rw [remU]; omega)
    · simp [advance,ixU]
    · simp [advance,remU]; omega
    · simpa [advance] using oneU
    · simpa [advance,U,Atom.apply] using hT.2.2.2.2.1
    · simpa [advance] using valU
  obtain ⟨t,ht,T,run,hT⟩ := countedLoop_runs (storageBound Reg Arr B) .iteration .iterationTodo
    .rightExponent .one _ j 1 I S (Store.size_le_of_bounded hS) (Store.size_le_of_bounded copyB)
    start control (by decide) (by decide) step
  exact ⟨t,by omega,T,run,hT.1,hT.2.2.2.2.2⟩

theorem code_div {p n : ℕ} (a : Fin p × Fin n) :
    (finProdFinEquiv a).val/n=a.1.val := by
  change (finProdFinEquiv.symm (finProdFinEquiv a)).1.val=a.1.val
  rw [Equiv.symm_apply_apply]

theorem code_mod {p n : ℕ} (a : Fin p × Fin n) :
    (finProdFinEquiv a).val%n=a.2.val := by
  change (finProdFinEquiv.symm (finProdFinEquiv a)).2.val=a.2.val
  rw [Equiv.symm_apply_apply]

def operation {p n : ℕ} (hp : 0<p) (mul : Fin n → Fin n → Fin n)
    (θ : Fin n → Fin n) (c e : Fin n) (a b : Fin (p*n)) : Fin (p*n) :=
  let x := finProdFinEquiv.symm a
  let y := finProdFinEquiv.symm b
  finProdFinEquiv (⟨(x.1.val+y.1.val)%p,Nat.mod_lt _ hp⟩,
    mul (mul (if (x.1.val+y.1.val)/p=0 then e else c) (θ^[y.1.val] x.2)) y.2)

def prelude : List (Atom Reg Arr) := [
  .divmod .row .column .index .size,
  .divmod .leftExponent .current .row .tail,
  .divmod .rightExponent .rightTail .column .tail,
  .binary .add .exponent .leftExponent .rightExponent,
  .divmod .carryFlag .residue .exponent .prime,
  .copy .factor .identity]

def selectCarry : Code := .branch .carryFlag (.atom (.copy .factor .carry)) .skip

def finish : List (Atom Reg Arr) := [
  .binary .mul .address .tail .factor,
  .binary .add .address .current .address,
  .read .current .table .address,
  .binary .mul .address .tail .current,
  .binary .add .address .rightTail .address,
  .read .current .table .address,
  .binary .mul .value .tail .residue,
  .binary .add .value .current .value,
  .write .output .index .value]

def cell : Code := sequence [atoms prelude,selectCarry,iterateMap,atoms finish]

theorem prelude_runs {p n B : ℕ} (hp : 0<p) (hn : 0<n) (a b : Fin p × Fin n)
    (S : Store Reg Arr) (hS : S.Bounded B) (hsize : S.scalar .size=p*n)
    (htail : S.scalar .tail=n) (hprime : S.scalar .prime=p)
    (hindex : S.scalar .index=(finProdFinEquiv (finProdFinEquiv a,finProdFinEquiv b)).val)
    (hroom : 2*p≤B) :
    ∃T,Runs (storageBound Reg Arr B) (atoms prelude) S 6 T ∧ T.Bounded B ∧
      T.scalar .current=a.2.val ∧ T.scalar .rightTail=b.2.val ∧
      T.scalar .rightExponent=b.1.val ∧ T.scalar .residue=(a.1.val+b.1.val)%p ∧
      T.scalar .carryFlag=(a.1.val+b.1.val)/p ∧ T.scalar .factor=S.scalar .identity := by
  have hexp : a.1.val+b.1.val≤B := by have := a.1.isLt; have := b.1.isLt; omega
  have valid : ValidAtoms B prelude S := by
    simp only [prelude,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,Function.update_apply,reduceCtorEq,if_true,if_false,
      hsize,htail,hprime,hindex,code_div,code_mod]
    exact ⟨⟨by decide,Nat.mul_pos hp hn⟩,trivial,⟨by decide,hn⟩,trivial,
      ⟨by decide,hn⟩,trivial,trivial,hexp,⟨by decide,hp⟩,trivial,trivial,trivial,trivial⟩
  obtain ⟨run,hT⟩ := atoms_runs hS prelude valid
  refine ⟨applyAtoms prelude S,run,hT,?_,?_,?_,?_,?_,?_⟩
  all_goals simp only [applyAtoms,prelude,List.foldl_cons,List.foldl_nil,Atom.apply,BinaryOp.eval,
    Store.setScalar,Function.update_apply,reduceCtorEq,if_true,if_false,
    hsize,htail,hprime,hindex,code_div,code_mod]

theorem selectCarry_runs {B : ℕ} (S : Store Reg Arr) (hS : S.Bounded B) :
    ∃t≤2,∃T,Runs (storageBound Reg Arr B) selectCarry S t T ∧ T.Bounded B ∧
      T.scalar .factor=(if S.scalar .carryFlag=0 then S.scalar .factor else S.scalar .carry) := by
  by_cases h : S.scalar .carryFlag=0
  · exact ⟨1,by omega,S,.branch_zero h (.skip (Store.size_le_of_bounded hS)),hS,by simp [h]⟩
  · let T := (Atom.copy Reg.factor Reg.carry).apply S
    exact ⟨2,le_rfl,T,.branch_nonzero h (atom_runs hS _ trivial trivial),
      Atom.apply_bounded hS _ trivial,by simp [T,Atom.apply,h]⟩

theorem finish_runs {p n B : ℕ} (mul : Fin n → Fin n → Fin n)
    (r : Fin p) (f x y : Fin n) (S : Store Reg Arr) (hS : S.Bounded B)
    (ht : S.array .table=GroupInitial.tableWord mul) (hn : S.scalar .tail=n)
    (hr : S.scalar .residue=r.val) (hf : S.scalar .factor=f.val)
    (hx : S.scalar .current=x.val) (hy : S.scalar .rightTail=y.val)
    (hindex : S.scalar .index<(S.array .output).length)
    (hroom : n*n≤B) (hsize : p*n≤B) :
    ∃T,Runs (storageBound Reg Arr B) (atoms finish) S 9 T ∧ T.Bounded B ∧
      T.array .output=(S.array .output).set (S.scalar .index)
        (finProdFinEquiv (r,mul (mul f x) y)).val := by
  have hi₁ := (finProdFinEquiv (f,x)).isLt
  have hi₂ := (finProdFinEquiv (mul f x,y)).isLt
  have hv := (finProdFinEquiv (r,mul (mul f x) y)).isLt
  have hm₁ : n*f.val≤B := (Nat.mul_le_mul_left n (Nat.le_of_lt f.isLt)).trans hroom
  have hm₂ : n*(mul f x).val≤B := (Nat.mul_le_mul_left n (Nat.le_of_lt (mul f x).isLt)).trans hroom
  have hm₃ : n*r.val≤B := by
    have h := Nat.mul_le_mul_left n (Nat.le_of_lt r.isLt)
    nlinarith
  have valid : ValidAtoms B finish S := by
    simp only [finish,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,Function.update_apply,reduceCtorEq,if_true,if_false,hn,hr,hf,hx,hy,ht,
      GroupInitial.tableWord_length,GroupInitial.tableWord_read]
    exact ⟨trivial,hm₁,trivial,(Nat.le_of_lt hi₁).trans hroom,hi₁,trivial,
      trivial,hm₂,trivial,(Nat.le_of_lt hi₂).trans hroom,hi₂,trivial,
      trivial,hm₃,trivial,(Nat.le_of_lt hv).trans hsize,hindex,trivial,trivial⟩
  obtain ⟨run,hT⟩ := atoms_runs hS finish valid
  refine ⟨applyAtoms finish S,run,hT,?_⟩
  simp only [applyAtoms,finish,List.foldl_cons,List.foldl_nil,Atom.apply,BinaryOp.eval,
    Store.setScalar,Function.update_apply,reduceCtorEq,if_true,if_false,hn,hr,hf,hx,hy,ht,
    GroupInitial.tableWord_read,Store.setArray_same]
  rfl

structure Context {p n : ℕ} (mul : Fin n → Fin n → Fin n) (θ : Fin n → Fin n)
    (c e : Fin n) (B : ℕ) (S : Store Reg Arr) : Prop where
  bounded : S.Bounded B
  tail_eq : S.scalar .tail=n
  prime_eq : S.scalar .prime=p
  size_eq : S.scalar .size=p*n
  square_eq : S.scalar .square=(p*n)*(p*n)
  carry_eq : S.scalar .carry=c.val
  identity_eq : S.scalar .identity=e.val
  one_eq : S.scalar .one=1
  table_eq : S.array .table=GroupInitial.tableWord mul
  image_eq : S.array .image=mapWord θ
  output_length : (S.array .output).length=(p*n)*(p*n)

theorem cell_runs {p n B : ℕ} (hp : 0<p) (hn : 0<n)
    (mul : Fin n → Fin n → Fin n) (θ : Fin n → Fin n) (c e : Fin n)
    (a b : Fin (p*n)) (S : Store Reg Arr) (ctx : Context (p:=p) mul θ c e B S)
    (hindex : S.scalar .index=(finProdFinEquiv (a,b)).val)
    (hexp : 2*p≤B) (htable : n*n≤B) (hsize : p*n≤B) :
    ∃t≤4*p+20,∃T,Runs (storageBound Reg Arr B) cell S t T ∧
      Context (p:=p) mul θ c e B T ∧ T.array .output=(S.array .output).set (S.scalar .index)
        (operation hp mul θ c e a b).val := by
  let x : Fin p × Fin n := finProdFinEquiv.symm a
  let y : Fin p × Fin n := finProdFinEquiv.symm b
  obtain ⟨U,r₀,hU,hx,hy,hj,hr,hq,hf⟩ := prelude_runs hp hn x y S ctx.bounded
    ctx.size_eq ctx.tail_eq ctx.prime_eq (by
      have xx : finProdFinEquiv x=a := Equiv.apply_symm_apply _ a
      have yy : finProdFinEquiv y=b := Equiv.apply_symm_apply _ b
      rw [xx,yy]; exact hindex) hexp
  obtain ⟨tc,htc,V,rc,hV,hfV⟩ := selectCarry_runs U hU
  have pre : Runs (storageBound Reg Arr B) (.seq (atoms prelude) selectCarry) S (6+tc) V := .seq r₀ rc
  have hjV : V.scalar .rightExponent=y.1.val := by rw [rc.scalar_eq_of_not_mem _ (by decide)]; exact hj
  have hxV : V.scalar .current=x.2.val := by rw [rc.scalar_eq_of_not_mem _ (by decide)]; exact hx
  have hmapV : V.array .image=mapWord θ := by rw [pre.array_eq_of_not_mem _ (by decide)]; exact ctx.image_eq
  have honeV : V.scalar .one=1 := by rw [pre.scalar_eq_of_not_mem _ (by decide)]; exact ctx.one_eq
  obtain ⟨ti,hti,W,ri,hW,hcurrent⟩ := iterateMap_runs θ x.2 y.1.val V hV hmapV hxV hjV honeV
  have first : Runs (storageBound Reg Arr B) (sequence [atoms prelude,selectCarry,iterateMap]) S (6+(tc+(ti+0))) W :=
    .seq r₀ (.seq rc (.seq ri (.skip ri.end_bound)))
  let f : Fin n := if (x.1.val+y.1.val)/p=0 then e else c
  let r : Fin p := ⟨(x.1.val+y.1.val)%p,Nat.mod_lt _ hp⟩
  have hfW : W.scalar .factor=f.val := by
    rw [ri.scalar_eq_of_not_mem _ (by decide),hfV,hq,hf,
      r₀.scalar_eq_of_not_mem Reg.carry (by decide),ctx.identity_eq,ctx.carry_eq]
    dsimp [f]
    split_ifs <;> rfl
  have hrW : W.scalar .residue=r.val := by
    rw [ri.scalar_eq_of_not_mem _ (by decide),rc.scalar_eq_of_not_mem _ (by decide)]
    exact hr
  have hyW : W.scalar .rightTail=y.2.val := by
    rw [ri.scalar_eq_of_not_mem _ (by decide),rc.scalar_eq_of_not_mem _ (by decide)]
    exact hy
  have tailW : W.scalar .tail=n := by rw [first.scalar_eq_of_not_mem _ (by decide)]; exact ctx.tail_eq
  have tableW : W.array .table=GroupInitial.tableWord mul := by rw [first.array_eq_of_not_mem _ (by decide)]; exact ctx.table_eq
  have indexW : W.scalar .index=S.scalar .index := first.scalar_eq_of_not_mem _ (by decide)
  have outW : W.array .output=S.array .output := first.array_eq_of_not_mem _ (by decide)
  obtain ⟨T,rf,hT,hout⟩ := finish_runs mul r f (θ^[y.1.val] x.2) y.2 W hW tableW tailW hrW hfW hcurrent hyW
    (by rw [indexW,outW,ctx.output_length,hindex]; exact (finProdFinEquiv (a,b)).isLt) htable hsize
  have full : Runs (storageBound Reg Arr B) cell S (6+(tc+(ti+(9+0)))) T :=
    .seq r₀ (.seq rc (.seq ri (.seq rf (.skip rf.end_bound))))
  have output : T.array .output=(S.array .output).set (S.scalar .index) (operation hp mul θ c e a b).val := by
    rw [hout,outW,indexW]
    rfl
  refine ⟨6+(tc+(ti+(9+0))),by have := y.1.isLt; omega,T,full,?_,output⟩
  refine ⟨hT,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [full.scalar_eq_of_not_mem _ (by decide)]; exact ctx.tail_eq
  · rw [full.scalar_eq_of_not_mem _ (by decide)]; exact ctx.prime_eq
  · rw [full.scalar_eq_of_not_mem _ (by decide)]; exact ctx.size_eq
  · rw [full.scalar_eq_of_not_mem _ (by decide)]; exact ctx.square_eq
  · rw [full.scalar_eq_of_not_mem _ (by decide)]; exact ctx.carry_eq
  · rw [full.scalar_eq_of_not_mem _ (by decide)]; exact ctx.identity_eq
  · rw [full.scalar_eq_of_not_mem _ (by decide)]; exact ctx.one_eq
  · rw [full.array_eq_of_not_mem _ (by decide)]; exact ctx.table_eq
  · rw [full.array_eq_of_not_mem _ (by decide)]; exact ctx.image_eq
  · simpa [output] using ctx.output_length

end GroupWL.MachinePrograms.ExtensionTablePrograms
