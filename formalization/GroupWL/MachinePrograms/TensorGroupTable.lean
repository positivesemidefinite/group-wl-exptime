import GroupWL.MachinePrograms.TensorGroupProduct
import GroupWL.MachinePrograms.NatArrayPower

/-! Materializing every entry of the tensor-group multiplication table. -/
namespace GroupWL.MachinePrograms.TensorGroupProgram
open NatArrayLanguage
open TensorGroupCode

def tableEntry (S : State) (half i : ℕ) : ℕ := multiplication
  (S.array (.inl .coefficients)) (S.scalar (l .modulus)) (S.scalar (l .inputDimension))
  (S.scalar (l .outputDimension)) half (i/S.scalar (a .order)) (i%S.scalar (a .order))

def tableCell (half : ℕ) : Code :=
  .seq (.atom (.divmod (l .left) (l .right) (a .pairIndex) (a .order)))
    (.seq (product half) (.atom (.write (.inr ()) (a .pairIndex) (a .result))))

@[simp] theorem product_scalarWrites (half : ℕ) : (product half).scalarWrites=(product 0).scalarWrites := rfl
@[simp] theorem product_arrayWrites (half : ℕ) : (product half).arrayWrites=(product 0).arrayWrites := rfl
@[simp] theorem tableCell_scalarWrites (half : ℕ) : (tableCell half).scalarWrites=(tableCell 0).scalarWrites := rfl
@[simp] theorem tableCell_arrayWrites (half : ℕ) : (tableCell half).arrayWrites=(tableCell 0).arrayWrites := rfl

def tableLoop (half : ℕ) : Code := countedLoop (a .pairIndex) (a .pairTodo) (a .square) (l .one) (tableCell half)

theorem tableCell_runs (S : State) (M half : ℕ) (bounded : S.Bounded M)
    (positive : 0<S.scalar (l .modulus))
    (room : (S.scalar (l .modulus))^3+3*S.scalar (l .modulus)≤M)
    (length : (S.array (.inl .coefficients)).length=
      S.scalar (l .inputDimension)*S.scalar (l .inputDimension)*S.scalar (l .outputDimension))
    (small : ∀x∈S.array (.inl .coefficients),x<S.scalar (l .modulus))
    (halfSmall : half<S.scalar (l .modulus))
    (dimension : S.scalar (l .inputDimension)+S.scalar (l .outputDimension)≤M)
    (power : (S.scalar (l .modulus))^(S.scalar (l .inputDimension)+S.scalar (l .outputDimension))≤M)
    (order : 0<S.scalar (a .order))
    (index : S.scalar (a .pairIndex)<(S.array (.inr ())).length) :
    ∃t≤(S.scalar (l .inputDimension)+S.scalar (l .outputDimension))*
        (14*(S.scalar (l .inputDimension))^2+9*S.scalar (l .inputDimension)+23)+12,∃T,
      Runs (storageBound Reg Arr M) (tableCell half) S t T ∧ T.Bounded M ∧
      T.scalar (l .one)=1 ∧ T.array (.inr ())=(S.array (.inr ())).set (S.scalar (a .pairIndex))
        (tableEntry S half (S.scalar (a .pairIndex))) := by
  let divide : Atom Reg Arr := .divmod (l .left) (l .right) (a .pairIndex) (a .order)
  let V := divide.apply S
  have valid : divide.Valid S := ⟨by decide,order⟩
  have first := atom_runs bounded divide valid trivial
  have hV := divide.apply_bounded bounded trivial
  obtain ⟨t,ht,U,run,hU,one,result⟩ := product_runs V M half hV positive room length small halfSmall dimension power
  have hn : V.scalar (l .inputDimension)=S.scalar (l .inputDimension) := rfl
  have hm : V.scalar (l .outputDimension)=S.scalar (l .outputDimension) := rfl
  have ix : U.scalar (a .pairIndex)=S.scalar (a .pairIndex) :=
    (run.scalar_eq_of_not_mem _ (by simp only [product_scalarWrites,product_arrayWrites,tableCell_scalarWrites,tableCell_arrayWrites];decide +kernel)).trans (by rfl)
  have output : U.array (.inr ())=S.array (.inr ()) :=
    (run.array_eq_of_not_mem _ (by simp only [product_scalarWrites,product_arrayWrites,tableCell_scalarWrites,tableCell_arrayWrites];decide +kernel)).trans (by rfl)
  let write : Atom Reg Arr := .write (.inr ()) (a .pairIndex) (a .result)
  have last := atom_runs hU write (by change U.scalar (a .pairIndex)<(U.array (.inr ())).length;rw [ix,output];exact index) trivial
  refine ⟨1+(t+1),by rw [hn,hm] at ht;omega,write.apply U,.seq first (.seq run last),write.apply_bounded hU trivial,one,?_⟩
  simp only [write,Atom.apply,Store.setArray,Function.update_apply,ite_true,output,ix,result]
  rfl

def tableInputs : Finset Reg := {l .inputDimension,l .outputDimension,l .modulus,a .order,a .square}

structure TableState (S : State) (M half i : ℕ) (T : State) : Prop where
  bounded : T.Bounded M
  inputs : ∀r∈tableInputs,T.scalar r=S.scalar r
  one : T.scalar (l .one)=1
  coefficients : T.array (.inl .coefficients)=S.array (.inl .coefficients)
  written : ArrayTabulation.Prefix (tableEntry S half) (S.scalar (a .square)) i (T.array (.inr ()))
  index : T.scalar (a .pairIndex)=i
  remaining : T.scalar (a .pairTodo)=S.scalar (a .square)-i

theorem tableLoop_runs (S : State) (M half : ℕ) (bounded : S.Bounded M)
    (one : S.scalar (l .one)=1) (positive : 0<S.scalar (l .modulus))
    (room : (S.scalar (l .modulus))^3+3*S.scalar (l .modulus)≤M)
    (length : (S.array (.inl .coefficients)).length=
      S.scalar (l .inputDimension)*S.scalar (l .inputDimension)*S.scalar (l .outputDimension))
    (small : ∀x∈S.array (.inl .coefficients),x<S.scalar (l .modulus))
    (halfSmall : half<S.scalar (l .modulus))
    (dimension : S.scalar (l .inputDimension)+S.scalar (l .outputDimension)≤M)
    (power : (S.scalar (l .modulus))^(S.scalar (l .inputDimension)+S.scalar (l .outputDimension))≤M)
    (order : 0<S.scalar (a .order))
    (output : S.array (.inr ())=List.replicate (S.scalar (a .square)) 0) :
    ∃t≤S.scalar (a .square)*((S.scalar (l .inputDimension)+S.scalar (l .outputDimension))*
        (14*(S.scalar (l .inputDimension))^2+9*S.scalar (l .inputDimension)+23)+15)+3,∃T,
      Runs (storageBound Reg Arr M) (tableLoop half) S t T ∧ T.Bounded M ∧
      T.array (.inr ())=List.ofFn (fun i : Fin (S.scalar (a .square)) =>tableEntry S half i.val) := by
  let S₀ := S.setScalar (a .pairTodo) (S.scalar (a .square))
  let S₁ := S₀.setScalar (a .pairIndex) 0
  have h₀ : S₀.Bounded M := bounded.setScalar _ (bounded.1 (a .square))
  have h₁ : S₁.Bounded M := h₀.setScalar _ (by omega)
  have start : TableState S M half 0 S₁ := by
    refine ⟨h₁,?_,?_,rfl,?_,?_,?_⟩
    · intro r hr
      have hd : ∀r∈tableInputs,r≠a .pairTodo ∧ r≠a .pairIndex := by decide
      simp [S₁,S₀,Store.setScalar,(hd r hr).1,(hd r hr).2]
    · simpa [S₁,S₀,Store.setScalar,a,l] using one
    · change ArrayTabulation.Prefix _ _ _ (S.array (.inr ()))
      rw [output]
      exact ArrayTabulation.Prefix.zero _ _
    · simp [S₁]
    · simp [S₁,S₀,Store.setScalar,a]
  have control : ∀i≤S.scalar (a .square),∀T,TableState S M half i T →
      T.scalar (a .pairIndex)=i ∧ T.scalar (a .pairTodo)=S.scalar (a .square)-i ∧
      T.scalar (l .one)=1 ∧ T.size≤storageBound Reg Arr M := by
    intro i hi T hT
    exact ⟨hT.index,hT.remaining,hT.one,Store.size_le_of_bounded hT.bounded⟩
  have body : ∀i<S.scalar (a .square),∀T,TableState S M half i T →
      ∃t≤(S.scalar (l .inputDimension)+S.scalar (l .outputDimension))*
          (14*(S.scalar (l .inputDimension))^2+9*S.scalar (l .inputDimension)+23)+12,∃U,
        Runs (storageBound Reg Arr M) (tableCell half) T t U ∧ U.scalar (a .pairIndex)=i ∧
        U.scalar (a .pairTodo)=S.scalar (a .square)-i ∧ U.scalar (l .one)=1 ∧
        (U.setScalar (a .pairIndex) (i+1)).size≤storageBound Reg Arr M ∧
        TableState S M half (i+1) (advance (a .pairIndex) (a .pairTodo) U) := by
    intro i hi T hT
    have hn := hT.inputs (l .inputDimension) (by decide)
    have hm := hT.inputs (l .outputDimension) (by decide)
    have hp := hT.inputs (l .modulus) (by decide)
    have ho := hT.inputs (a .order) (by decide)
    obtain ⟨t,ht,U,run,hU,uone,uout⟩ := tableCell_runs T M half hT.bounded (by omega)
      (by simpa only [hp] using room) (by simpa only [hT.coefficients,hn,hm] using length)
      (by simpa only [hT.coefficients,hp] using small) (by omega)
      (by omega) (by simpa only [hp,hn,hm] using power) (by omega)
      (by rw [hT.index,hT.written.1];exact hi)
    have frame (r : Reg) (hr : r∈tableInputs ∨ r=a .pairIndex ∨ r=a .pairTodo) : U.scalar r=T.scalar r := by
      apply run.scalar_eq_of_not_mem
      have hd : ∀r∈tableInputs,r∉(tableCell half).scalarWrites := by simp only [product_scalarWrites,product_arrayWrites,tableCell_scalarWrites,tableCell_arrayWrites];decide +kernel
      rcases hr with hr|hr|hr
      · exact hd r hr
      · subst r;simp only [tableCell_scalarWrites];decide +kernel
      · subst r;simp only [tableCell_scalarWrites];decide +kernel
    have ix : U.scalar (a .pairIndex)=i := (frame _ (by simp)).trans hT.index
    have rem : U.scalar (a .pairTodo)=S.scalar (a .square)-i := (frame _ (by simp)).trans hT.remaining
    have mid : (U.setScalar (a .pairIndex) (i+1)).Bounded M :=
      hU.setScalar _ ((by omega : i+1≤S.scalar (a .square)).trans (bounded.1 (a .square)))
    have final : (advance (a .pairIndex) (a .pairTodo) U).Bounded M := by
      simpa only [advance,ix] using mid.setScalar (a .pairTodo)
        ((Nat.sub_le _ _).trans (hU.1 (a .pairTodo)))
    refine ⟨t,by simpa only [hn,hm] using ht,U,run,ix,rem,uone,Store.size_le_of_bounded mid,final,?_,?_,?_,?_,?_,?_⟩
    · intro r hr
      have hd : ∀r∈tableInputs,r≠a .pairIndex ∧ r≠a .pairTodo := by decide
      simpa [advance,Store.setScalar,(hd r hr).1,(hd r hr).2] using
        (frame r (Or.inl hr)).trans (hT.inputs r hr)
    · simpa [advance,Store.setScalar,a,l] using uone
    · exact (run.array_eq_of_not_mem _ (by simp only [product_scalarWrites,product_arrayWrites,tableCell_scalarWrites,tableCell_arrayWrites];decide +kernel)).trans hT.coefficients
    · change ArrayTabulation.Prefix _ _ _ (U.array (.inr ()))
      rw [uout,hT.index]
      have he : tableEntry T half i=tableEntry S half i := by
        simp only [tableEntry,hT.coefficients,hp,hn,hm,ho]
      rw [he]
      exact hT.written.write hi
    · simpa [advance,Store.setScalar,a,l] using ix
    · simpa [advance,Store.setScalar,a,l,Nat.sub_sub] using congrArg (fun n=>n-1) rem
  obtain ⟨t,ht,T,run,hT⟩ := countedLoop_runs (storageBound Reg Arr M)
    (a .pairIndex) (a .pairTodo) (a .square) (l .one) (tableCell half)
    (S.scalar (a .square)) ((S.scalar (l .inputDimension)+S.scalar (l .outputDimension))*
      (14*(S.scalar (l .inputDimension))^2+9*S.scalar (l .inputDimension)+23)+12)
    (TableState S M half) S (Store.size_le_of_bounded bounded) (Store.size_le_of_bounded h₀)
    start control (by decide) (by decide) body
  exact ⟨t,by omega,T,run,hT.bounded,hT.written.complete⟩

end GroupWL.MachinePrograms.TensorGroupProgram
