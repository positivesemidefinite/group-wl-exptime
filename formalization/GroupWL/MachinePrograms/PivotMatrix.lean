import GroupWL.MachinePrograms.MatrixArithmetic
import GroupWL.MachinePrograms.ArrayFiniteTable

/-! A materialized one-equation kernel chart. Both output arrays are stored
ambient-coordinate first; the second is the transpose of the retraction. -/
namespace GroupWL.MachinePrograms.PivotMatrix

open NatArrayLanguage
set_option maxHeartbeats 2000000

inductive Reg where
  | width | cols | modulus | pivot | negInverse | one | zero | total
  | index | todo | row | col | coordinate | flag | value | quotient
  deriving DecidableEq,Fintype
inductive Arr where
  | row | lift | lowerTranspose
  deriving DecidableEq,Fintype
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def coordinate (pivot col : ℕ) : ℕ := if col+1=pivot then 0 else col+1
def lowerValue (cols pivot index : ℕ) : ℕ :=
  if index/cols=coordinate pivot (index%cols) then 1 else 0
def liftValue (xs : List ℕ) (cols pivot neg p index : ℕ) : ℕ :=
  if index/cols=pivot then
    (xs[coordinate pivot (index%cols)]?).getD 0*neg%p
  else lowerValue cols pivot index

def splitAtoms : List (Atom Reg Arr) := [
  .divmod .row .col .index .cols,
  .binary .add .coordinate .col .one,
  .binary .eq .flag .coordinate .pivot]
def lowerAtoms : List (Atom Reg Arr) := [
  .binary .eq .value .row .coordinate,
  .write .lowerTranspose .index .value,
  .binary .eq .flag .row .pivot]
def pivotAtoms : List (Atom Reg Arr) := [
  .read .value .row .coordinate,
  .binary .mul .value .value .negInverse,
  .divmod .quotient .value .value .modulus]
def cell : Code := .seq (atoms splitAtoms)
  (.seq (.branch .flag (.atom (.const .coordinate 0)) .skip)
    (.seq (atoms lowerAtoms)
      (.seq (.branch .flag (atoms pivotAtoms) .skip)
        (.atom (.write .lift .index .value)))))
def program : Code := .seq (atoms [
  .const .one 1,.const .zero 0,.binary .sub .cols .width .one,
  .binary .mul .total .width .cols,
  .allocate .lift .total .zero,.allocate .lowerTranspose .total .zero])
  (countedLoop .index .todo .total .one cell)

theorem coordinate_lt {w j c : ℕ} (hw : 0<w) (hc : c<w-1) : coordinate j c<w := by
  unfold coordinate
  split_ifs <;> omega

theorem cell_runs (S : State) (M : ℕ) (bounded : S.Bounded M)
    (one : S.scalar .one=1) (cols : S.scalar .cols=S.scalar .width-1)
    (width : S.scalar .width=(S.array .row).length)
    (positive : 0<S.scalar .modulus)
    (small : S.scalar .modulus*S.scalar .modulus+S.scalar .modulus≤M)
    (inverse : S.scalar .negInverse≤S.scalar .modulus)
    (values : ∀ x∈S.array .row,x<S.scalar .modulus)
    (index : S.scalar .index<S.scalar .width*S.scalar .cols)
    (liftLength : (S.array .lift).length=S.scalar .width*S.scalar .cols)
    (lowerLength : (S.array .lowerTranspose).length=S.scalar .width*S.scalar .cols) :
    ∃ t≤14,∃ T,Runs (storageBound Reg Arr M) cell S t T ∧ T.Bounded M ∧
      T.array .lift=(S.array .lift).set (S.scalar .index)
        (liftValue (S.array .row) (S.scalar .cols) (S.scalar .pivot)
          (S.scalar .negInverse) (S.scalar .modulus) (S.scalar .index)) ∧
      T.array .lowerTranspose=(S.array .lowerTranspose).set (S.scalar .index)
        (lowerValue (S.scalar .cols) (S.scalar .pivot) (S.scalar .index)) := by
  have htotal : 0<S.scalar .width*S.scalar .cols := by omega
  have hc : 0<S.scalar .cols := Nat.pos_of_mul_pos_left htotal
  have hw : 0<S.scalar .width := Nat.pos_of_mul_pos_right htotal
  have hr : S.scalar .index/S.scalar .cols<S.scalar .width := (Nat.div_lt_iff_lt_mul hc).mpr index
  have hcol := Nat.mod_lt (S.scalar .index) hc
  have hcoord := coordinate_lt (j:=S.scalar .pivot) hw (by omega : S.scalar .index%S.scalar .cols<S.scalar .width-1)
  have hwidth := bounded.1 Reg.width
  have h1 : 1≤M := by omega
  have hsplit : ValidAtoms M splitAtoms S := by
    simp [splitAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar,one]
    exact ⟨hc,by omega,by split_ifs <;> omega⟩
  obtain ⟨splitRun,hU⟩ := atoms_runs bounded splitAtoms hsplit
  let U := applyAtoms splitAtoms S
  let V := U.setScalar .coordinate (coordinate (S.scalar .pivot) (S.scalar .index%S.scalar .cols))
  have hV : V.Bounded M := hU.setScalar _ (by omega)
  have swapRun : ∃ t≤2,Runs (storageBound Reg Arr M)
      (.branch .flag (.atom (.const .coordinate 0)) .skip) U t V := by
    by_cases he : S.scalar .index%S.scalar .cols+1=S.scalar .pivot
    · refine ⟨2,by omega,.branch_nonzero ?_ ?_⟩
      · simp [U,applyAtoms,splitAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,one,he]
      · simpa [V,coordinate,he] using atom_runs hU (.const Reg.coordinate 0) trivial (show 0≤M by omega)
    · have hv : V=U := by
        apply Store.ext
        · intro r
          by_cases h : r=Reg.coordinate
          · subst r; simp [V,U,applyAtoms,splitAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,coordinate,one,he]
          · simp [V,Store.setScalar,h]
        · intro a; rfl
      refine ⟨1,by omega,.branch_zero ?_ ?_⟩
      · simp [U,applyAtoms,splitAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,one,he]
      · rw [hv]; exact .skip (Store.size_le_of_bounded hU)
  obtain ⟨ts,hts,swapRun⟩ := swapRun
  have hlow : ValidAtoms M lowerAtoms V := by
    simp [lowerAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,V,U,applyAtoms,splitAtoms,lowerLength]
    exact ⟨by split_ifs <;> omega,index,by split_ifs <;> omega⟩
  obtain ⟨lowerRun,hW⟩ := atoms_runs hV lowerAtoms hlow
  let W := applyAtoms lowerAtoms V
  have hscalar (r : Reg) : W.scalar r =
      (V.setScalar .value (lowerValue (S.scalar .cols) (S.scalar .pivot) (S.scalar .index))
        |>.setScalar .flag (if S.scalar .index/S.scalar .cols=S.scalar .pivot then 1 else 0)).scalar r := by
    simp [W,applyAtoms,lowerAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,V,U,
      splitAtoms,lowerValue,one]
  have rowArray : W.array .row=S.array .row := rfl
  have liftArray : W.array .lift=S.array .lift := rfl
  have lowerArray : W.array .lowerTranspose=(S.array .lowerTranspose).set (S.scalar .index)
      (lowerValue (S.scalar .cols) (S.scalar .pivot) (S.scalar .index)) := by
    simp [W,applyAtoms,lowerAtoms,V,U,splitAtoms,Atom.apply,BinaryOp.eval,
      Store.setScalar,Store.setArray,lowerValue,one]
  have valueRun : ∃ t≤4,∃ X,Runs (storageBound Reg Arr M)
      (.branch .flag (atoms pivotAtoms) .skip) W t X ∧ X.Bounded M ∧
      X.scalar .value=liftValue (S.array .row) (S.scalar .cols) (S.scalar .pivot)
        (S.scalar .negInverse) (S.scalar .modulus) (S.scalar .index) := by
    by_cases he : S.scalar .index/S.scalar .cols=S.scalar .pivot
    · have hval : (S.array .row)[coordinate (S.scalar .pivot) (S.scalar .index%S.scalar .cols)]?.getD 0<S.scalar .modulus :=
        MatrixArithmetic.read_lt values positive _
      have hpiv : ValidAtoms M pivotAtoms W := by
        simp [pivotAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
          Store.setScalar,hscalar,V,U,applyAtoms,splitAtoms,rowArray]
        exact ⟨by omega,by nlinarith,positive⟩
      obtain ⟨run,hX⟩ := atoms_runs hW pivotAtoms hpiv
      refine ⟨4,by omega,applyAtoms pivotAtoms W,.branch_nonzero ?_ run,hX,?_⟩
      · simp [hscalar,he]
      · simp [applyAtoms,pivotAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,hscalar,
          V,U,splitAtoms,rowArray,liftValue,he]
    · refine ⟨1,by omega,W,.branch_zero ?_ (.skip (Store.size_le_of_bounded hW)),hW,?_⟩
      · simp [hscalar,he]
      · simp [hscalar,liftValue,he]
  obtain ⟨tv,htv,X,valueRun,hX,hvalue⟩ := valueRun
  have hxindex : X.scalar .index=S.scalar .index := by
    rw [valueRun.scalar_eq_of_not_mem .index (by decide),hscalar]
    simp [V,U,applyAtoms,splitAtoms,Atom.apply,Store.setScalar]
  have hxlift : X.array .lift=S.array .lift := (valueRun.array_eq_of_not_mem .lift (by decide)).trans liftArray
  have hxlower : X.array .lowerTranspose=W.array .lowerTranspose := valueRun.array_eq_of_not_mem .lowerTranspose (by decide)
  let write : Atom Reg Arr := .write .lift .index .value
  have hvalid : write.Valid X := by change X.scalar .index<(X.array .lift).length; rwa [hxindex,hxlift,liftLength]
  have writeRun := atom_runs hX write hvalid trivial
  have hT := write.apply_bounded hX trivial
  refine ⟨3+(ts+(3+(tv+1))),by omega,write.apply X,
    .seq splitRun (.seq swapRun (.seq lowerRun (.seq valueRun writeRun))),hT,?_,?_⟩
  · simp [write,Atom.apply,hxlift,hxindex,hvalue]
  · simp [write,Atom.apply,hxlower,lowerArray]

def inputs : Finset Reg := {.width,.cols,.modulus,.pivot,.negInverse,.one,.total}

structure Invariant (S : State) (M i : ℕ) (T : State) : Prop where
  bounded : T.Bounded M
  inputs : ∀ r∈inputs,T.scalar r=S.scalar r
  row : T.array .row=S.array .row
  index : T.scalar .index=i
  todo : T.scalar .todo=S.scalar .total-i
  lift : ArrayTabulation.Prefix
    (liftValue (S.array .row) (S.scalar .cols) (S.scalar .pivot)
      (S.scalar .negInverse) (S.scalar .modulus)) (S.scalar .total) i (T.array .lift)
  lower : ArrayTabulation.Prefix
    (lowerValue (S.scalar .cols) (S.scalar .pivot)) (S.scalar .total) i (T.array .lowerTranspose)

theorem loop_runs (S : State) (M : ℕ) (bounded : S.Bounded M)
    (one : S.scalar .one=1) (cols : S.scalar .cols=S.scalar .width-1)
    (width : S.scalar .width=(S.array .row).length)
    (total : S.scalar .total=S.scalar .width*S.scalar .cols)
    (positive : 0<S.scalar .modulus)
    (small : S.scalar .modulus*S.scalar .modulus+S.scalar .modulus≤M)
    (inverse : S.scalar .negInverse≤S.scalar .modulus)
    (values : ∀ x∈S.array .row,x<S.scalar .modulus)
    (lift : S.array .lift=List.replicate (S.scalar .total) 0)
    (lower : S.array .lowerTranspose=List.replicate (S.scalar .total) 0) :
    ∃ t≤17*S.scalar .total+3,∃ T,
      Runs (storageBound Reg Arr M) (countedLoop .index .todo .total .one cell) S t T ∧ T.Bounded M ∧
      T.array .lift=List.ofFn (fun i : Fin (S.scalar .total) =>
        liftValue (S.array .row) (S.scalar .cols) (S.scalar .pivot)
          (S.scalar .negInverse) (S.scalar .modulus) i) ∧
      T.array .lowerTranspose=List.ofFn (fun i : Fin (S.scalar .total) =>
        lowerValue (S.scalar .cols) (S.scalar .pivot) i) := by
  let S₀ := S.setScalar .todo (S.scalar .total)
  let S₁ := S₀.setScalar .index 0
  have h₀ : S₀.Bounded M := bounded.setScalar _ (bounded.1 .total)
  have h₁ : S₁.Bounded M := h₀.setScalar _ (Nat.zero_le _)
  have hstart : Invariant S M 0 S₁ := by
    refine ⟨h₁,?_,rfl,?_,?_,?_,?_⟩
    · intro r hr
      have hn : ∀ r∈inputs,r≠Reg.index ∧ r≠Reg.todo := by decide
      obtain ⟨hi,ht⟩ := hn r hr
      simp [S₁,S₀,Store.setScalar,hi,ht]
    · simp [S₁]
    · simp [S₁,S₀]
    · simpa [S₁,S₀,lift] using ArrayTabulation.Prefix.zero
        (liftValue (S.array .row) (S.scalar .cols) (S.scalar .pivot)
          (S.scalar .negInverse) (S.scalar .modulus)) (S.scalar .total)
    · simpa [S₁,S₀,lower] using ArrayTabulation.Prefix.zero
        (lowerValue (S.scalar .cols) (S.scalar .pivot)) (S.scalar .total)
  have control : ∀ i≤S.scalar .total,∀ T,Invariant S M i T →
      T.scalar .index=i ∧ T.scalar .todo=S.scalar .total-i ∧ T.scalar .one=1 ∧
      T.size≤storageBound Reg Arr M := by
    intro i hi T hT
    exact ⟨hT.index,hT.todo,(hT.inputs .one (by decide)).trans one,Store.size_le_of_bounded hT.bounded⟩
  have body : ∀ i<S.scalar .total,∀ T,Invariant S M i T →
      ∃ t≤14,∃ U,Runs (storageBound Reg Arr M) cell T t U ∧
        U.scalar .index=i ∧ U.scalar .todo=S.scalar .total-i ∧ U.scalar .one=1 ∧
        (U.setScalar .index (i+1)).size≤storageBound Reg Arr M ∧
        Invariant S M (i+1) (advance .index .todo U) := by
    intro i hi T hT
    have hw := hT.inputs .width (by decide)
    have hc := hT.inputs .cols (by decide)
    have hp := hT.inputs .modulus (by decide)
    have hj := hT.inputs .pivot (by decide)
    have hn := hT.inputs .negInverse (by decide)
    have ho := (hT.inputs .one (by decide)).trans one
    obtain ⟨t,ht,U,run,hU,hlift,hlower⟩ := cell_runs T M hT.bounded ho
      (by rwa [hc,hw]) (by rwa [hw,hT.row]) (by rwa [hp]) (by rwa [hp])
      (by rwa [hn,hp]) (by rwa [hT.row,hp]) (by rwa [hT.index,hw,hc,←total])
      (by rw [hT.lift.1,hw,hc,total]) (by rw [hT.lower.1,hw,hc,total])
    rw [hT.row,hc,hj,hn,hp,hT.index] at hlift
    rw [hc,hj,hT.index] at hlower
    have hix : U.scalar .index=i := (run.scalar_eq_of_not_mem .index (by decide)).trans hT.index
    have htod : U.scalar .todo=S.scalar .total-i := (run.scalar_eq_of_not_mem .todo (by decide)).trans hT.todo
    have hone : U.scalar .one=1 := (run.scalar_eq_of_not_mem .one (by decide)).trans ho
    have hiM : i+1≤M := le_trans (by omega) (bounded.1 .total)
    have hmid := hU.setScalar Reg.index hiM
    have hfinal : (advance .index .todo U).Bounded M := by
      simpa only [advance,hix] using hmid.setScalar Reg.todo ((Nat.sub_le _ _).trans (hU.1 .todo))
    refine ⟨t,ht,U,run,hix,htod,hone,Store.size_le_of_bounded hmid,hfinal,?_,?_,?_,?_,?_,?_⟩
    · intro r hr
      have hn : ∀ r∈inputs,r≠Reg.index ∧ r≠Reg.todo ∧ r∉cell.scalarWrites := by decide
      obtain ⟨hri,hrt,hrw⟩ := hn r hr
      simpa [advance,Store.setScalar,hri,hrt] using
        (run.scalar_eq_of_not_mem r hrw).trans (hT.inputs r hr)
    · exact (run.array_eq_of_not_mem .row (by decide)).trans hT.row
    · simp [advance,hix]
    · simp [advance,htod,Nat.sub_sub]
    · change ArrayTabulation.Prefix _ _ _ (U.array .lift)
      rw [hlift]; exact hT.lift.write hi
    · change ArrayTabulation.Prefix _ _ _ (U.array .lowerTranspose)
      rw [hlower]; exact hT.lower.write hi
  obtain ⟨t,ht,T,run,hT⟩ := countedLoop_runs (storageBound Reg Arr M)
    Reg.index Reg.todo Reg.total Reg.one cell (S.scalar .total) 14 (Invariant S M) S
    (Store.size_le_of_bounded bounded) (Store.size_le_of_bounded h₀) hstart control
    (by decide) (by decide) body
  exact ⟨t,by nlinarith,T,run,hT.bounded,hT.lift.complete,hT.lower.complete⟩

theorem program_runs (S : State) (M : ℕ) (bounded : S.Bounded M)
    (width : S.scalar .width=(S.array .row).length)
    (positive : 0<S.scalar .modulus)
    (small : S.scalar .modulus*S.scalar .modulus+S.scalar .modulus≤M)
    (size : S.scalar .width*(S.scalar .width-1)≤M)
    (inverse : S.scalar .negInverse≤S.scalar .modulus)
    (values : ∀ x∈S.array .row,x<S.scalar .modulus) :
    ∃ t≤17*(S.scalar .width*(S.scalar .width-1))+9,∃ T,
      Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧
      T.array .lift=List.ofFn (fun i : Fin (S.scalar .width*(S.scalar .width-1)) =>
        liftValue (S.array .row) (S.scalar .width-1) (S.scalar .pivot)
          (S.scalar .negInverse) (S.scalar .modulus) i) ∧
      T.array .lowerTranspose=List.ofFn (fun i : Fin (S.scalar .width*(S.scalar .width-1)) =>
        lowerValue (S.scalar .width-1) (S.scalar .pivot) i) := by
  let pre : List (Atom Reg Arr) := [
    .const .one 1,.const .zero 0,.binary .sub .cols .width .one,
    .binary .mul .total .width .cols,
    .allocate .lift .total .zero,.allocate .lowerTranspose .total .zero]
  have h1 : 1≤M := by nlinarith
  have valid : ValidAtoms M pre S := by
    simp [pre,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray]
    exact ⟨h1,by have := bounded.1 Reg.width; omega,size⟩
  obtain ⟨preRun,hU⟩ := atoms_runs bounded pre valid
  let U := applyAtoms pre S
  have hscalar (r : Reg) (h : r≠Reg.one ∧ r≠Reg.zero ∧ r≠Reg.cols ∧ r≠Reg.total) : U.scalar r=S.scalar r := by
    rcases h with ⟨h1,h2,h3,h4⟩
    simp [U,pre,applyAtoms,Atom.apply,Store.setScalar,Store.setArray,h1,h2,h3,h4]
  have hrow : U.array .row=S.array .row := rfl
  have hc : U.scalar .cols=S.scalar .width-1 := by simp [U,pre,applyAtoms,Atom.apply,Store.setScalar,BinaryOp.eval,Store.setArray]
  have ht : U.scalar .total=S.scalar .width*(S.scalar .width-1) := by simp [U,pre,applyAtoms,Atom.apply,Store.setScalar,BinaryOp.eval,Store.setArray]
  obtain ⟨t,htime,T,run,hT,hl,hr⟩ := loop_runs U M hU
    (by simp [U,pre,applyAtoms,Atom.apply,Store.setScalar,Store.setArray])
    (by rw [hc,hscalar .width (by decide)]) (by rw [hrow,hscalar .width (by decide)]; exact width)
    (by rw [ht,hc,hscalar .width (by decide)])
    (by rwa [hscalar .modulus (by decide)]) (by rwa [hscalar .modulus (by decide)])
    (by rwa [hscalar .negInverse (by decide),hscalar .modulus (by decide)])
    (by rwa [hrow,hscalar .modulus (by decide)])
    (by simp [U,pre,applyAtoms,Atom.apply,Store.setScalar,Store.setArray,BinaryOp.eval])
    (by simp [U,pre,applyAtoms,Atom.apply,Store.setScalar,Store.setArray,BinaryOp.eval])
  simp only [ht,hc,hrow,hscalar .pivot (by decide),hscalar .negInverse (by decide),
    hscalar .modulus (by decide)] at htime hl hr
  exact ⟨6+t,by omega,T,.seq preRun run,hT,hl,hr⟩

end GroupWL.MachinePrograms.PivotMatrix
