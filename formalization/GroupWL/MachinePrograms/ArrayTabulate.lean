import GroupWL.MachinePrograms.NatArrayProofs
import GroupWL.MachinePrograms.NatArrayCountedLoops
import GroupWL.IndexedRefinement

/-! A counted array-materialization loop for concrete point programs. -/
namespace GroupWL.MachinePrograms.ArrayTabulate
open NatArrayLanguage
variable {R A : Type*} [DecidableEq R] [DecidableEq A] [Fintype R] [Fintype A]

def cell (index value : R) (output : A) (body : Program R A) : Program R A :=
  .seq body (.atom (.write output index value))
def fill (index todo limit one value : R) (output : A) (body : Program R A) : Program R A :=
  countedLoop index todo limit one (cell index value output body)
def tabulate (index todo limit one zero value : R) (output : A) (body : Program R A) : Program R A :=
  .seq (.atom (.allocate output limit zero)) (fill index todo limit one value output body)

private structure Invariant (index todo one : R) (output : A) {n : ℕ} (f : Fin n → ℕ)
    (P : Store R A → Prop) (B i : ℕ) (S : Store R A) : Prop where
  bounded : S.Bounded B
  context : P S
  index_eq : S.scalar index=i
  todo_eq : S.scalar todo=n-i
  one_eq : S.scalar one=1
  length_eq : (S.array output).length=n
  values_eq : ∀ j : Fin n,j.val < i → IndexedRefinement.read (S.array output) j.val=f j

theorem fill_runs (index todo limit one value : R) (output : A) (body : Program R A)
    {n : ℕ} (f : Fin n → ℕ) (P : Store R A → Prop) (B c : ℕ)
    (hindex : ∀ S x,P S → P (S.setScalar index x))
    (htodo : ∀ S x,P S → P (S.setScalar todo x))
    (houtput : ∀ S xs,P S → P (S.setArray output xs))
    (hit : index≠todo) (hio : index≠one) (hto : todo≠one)
    (point : ∀ i : Fin n,∀ S,P S → S.Bounded B → S.scalar index=i.val →
      S.scalar todo=n-i.val → S.scalar one=1 →
      ∃ t≤c,∃ T,Runs (storageBound R A B) body S t T ∧ T.Bounded B ∧ P T ∧
        T.scalar index=i.val ∧ T.scalar todo=n-i.val ∧ T.scalar one=1 ∧
        T.scalar value=f i ∧ T.array output=S.array output)
    (S : Store R A) (hS : S.Bounded B) (hP : P S) (hn : S.scalar limit=n)
    (hone : S.scalar one=1) (hlen : (S.array output).length=n) :
    ∃ t≤n*(c+4)+3,∃ T,Runs (storageBound R A B) (fill index todo limit one value output body) S t T ∧
      T.Bounded B ∧ P T ∧ T.array output=List.ofFn f := by
  have hnB : n≤B := by simpa [hn] using hS.1 limit
  let I := Invariant index todo one output f P B
  have copyBound := hS.setScalar todo (hS.1 limit)
  have start : I 0 ((S.setScalar todo (S.scalar limit)).setScalar index 0) := by
    refine ⟨copyBound.setScalar _ (Nat.zero_le _),hindex _ _ (htodo _ _ hP),?_,?_,?_,hlen,?_⟩
    · simp
    · simp [Store.setScalar,hit,Ne.symm hit,hn]
    · simp [Store.setScalar,Ne.symm hio,Ne.symm hto,hone]
    · intro j hj;omega
  have control : ∀ i≤n,∀ U,I i U → U.scalar index=i ∧ U.scalar todo=n-i ∧ U.scalar one=1 ∧
      U.size≤storageBound R A B := by
    intro i hi U hU
    exact ⟨hU.index_eq,hU.todo_eq,hU.one_eq,Store.size_le_of_bounded hU.bounded⟩
  have step : ∀ i<n,∀ U,I i U → ∃ t≤c+1,∃ V,
      Runs (storageBound R A B) (cell index value output body) U t V ∧
      V.scalar index=i ∧ V.scalar todo=n-i ∧ V.scalar one=1 ∧
      (V.setScalar index (i+1)).size≤storageBound R A B ∧ I (i+1) (advance index todo V) := by
    intro i hi U hU
    let j : Fin n := ⟨i,hi⟩
    obtain ⟨t,ht,V,run,hV,hPV,hvi,hvt,hvo,hvalue,harray⟩ := point j U hU.context hU.bounded
      hU.index_eq hU.todo_eq hU.one_eq
    have valid : (Atom.write output index value).Valid V := by
      simpa only [Atom.Valid,hvi,harray,hU.length_eq] using hi
    have write := atom_runs hV (.write output index value) valid trivial
    let W := V.setArray output ((V.array output).set i (f j))
    have write' : Runs (storageBound R A B) (.atom (.write output index value)) V 1 W := by
      simpa only [Atom.apply,hvi,hvalue] using write
    have hW : W.Bounded B := by
      have hh := (Atom.write output index value).apply_bounded hV trivial
      simpa only [Atom.apply,hvi,hvalue] using hh
    have wi : W.scalar index=i := hvi
    have wt : W.scalar todo=n-i := hvt
    have wo : W.scalar one=1 := hvo
    have mid := hW.setScalar index (show i+1≤B by omega)
    refine ⟨t+1,by omega,W,Runs.seq run write',wi,wt,wo,Store.size_le_of_bounded mid,?_⟩
    refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [advance,wi] using mid.setScalar todo (show W.scalar todo-1≤B by rw [wt];omega)
    · exact htodo _ _ (hindex _ _ (houtput _ _ hPV))
    · simp [advance,Store.setScalar,hit,wi]
    · simp [advance,wt];omega
    · simp [advance,Store.setScalar,Ne.symm hio,Ne.symm hto,wo]
    · simp [advance,W,Store.setArray,harray,hU.length_eq]
    · intro z hz
      change IndexedRefinement.read (W.array output) z.val=f z
      simp only [W,Store.setArray,Function.update_self,harray]
      by_cases hzi : z.val=i
      · have hzj : z=j := Fin.ext hzi
        subst z
        simp [IndexedRefinement.read,hU.length_eq,j,hi]
      · have hzl : z.val < i := by omega
        simpa [IndexedRefinement.read,List.getElem?_set,hzi,Ne.symm hzi] using hU.values_eq z hzl
  obtain ⟨t,ht,T,run,hT⟩ := countedLoop_runs (storageBound R A B) index todo limit one
    (cell index value output body) n (c+1) I S (Store.size_le_of_bounded hS)
    (Store.size_le_of_bounded copyBound) start control hit (Ne.symm hio) step
  refine ⟨t,by omega,T,run,hT.bounded,hT.context,?_⟩
  apply List.ext_getElem
  · simpa using hT.length_eq
  · intro i hi hi'
    have hin : i<n := by simpa [hT.length_eq] using hi
    have hv := hT.values_eq ⟨i,hin⟩ hin
    simpa only [IndexedRefinement.read,List.getElem?_eq_getElem hi,Option.getD_some,List.getElem_ofFn] using hv

theorem tabulate_runs (index todo limit one zero value : R) (output : A) (body : Program R A)
    {n : ℕ} (f : Fin n → ℕ) (P : Store R A → Prop) (B c : ℕ)
    (hindex : ∀ S x,P S → P (S.setScalar index x))
    (htodo : ∀ S x,P S → P (S.setScalar todo x))
    (houtput : ∀ S xs,P S → P (S.setArray output xs))
    (hit : index≠todo) (hio : index≠one) (hto : todo≠one)
    (point : ∀ i : Fin n,∀ S,P S → S.Bounded B → S.scalar index=i.val →
      S.scalar todo=n-i.val → S.scalar one=1 →
      ∃ t≤c,∃ T,Runs (storageBound R A B) body S t T ∧ T.Bounded B ∧ P T ∧
        T.scalar index=i.val ∧ T.scalar todo=n-i.val ∧ T.scalar one=1 ∧
        T.scalar value=f i ∧ T.array output=S.array output)
    (S : Store R A) (hS : S.Bounded B) (hP : P S) (hn : S.scalar limit=n)
    (hone : S.scalar one=1) (hzero : S.scalar zero=0) :
    ∃ t≤n*(c+4)+4,∃ T,
      Runs (storageBound R A B) (tabulate index todo limit one zero value output body) S t T ∧
      T.Bounded B ∧ P T ∧ T.array output=List.ofFn f := by
  have first := atom_runs hS (.allocate output limit zero) trivial trivial
  let U := (Atom.allocate output limit zero).apply S
  have hU : U.Bounded B := Atom.apply_bounded hS _ trivial
  have hp : P U := houtput _ _ hP
  obtain ⟨t,ht,T,last,hT,hPT,hword⟩ := fill_runs index todo limit one value output body f P B c
    hindex htodo houtput hit hio hto point U hU hp hn hone (by simp [U,Atom.apply,hn])
  exact ⟨1+t,by omega,T,Runs.seq first last,hT,hPT,hword⟩
end GroupWL.MachinePrograms.ArrayTabulate
