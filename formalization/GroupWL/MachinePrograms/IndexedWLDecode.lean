import GroupWL.MachinePrograms.IndexedWL
import GroupWL.MachinePrograms.NatArrayFrames
import GroupWL.MachinePrograms.NatArrayCountedLoops

/-! Bounded operational decoding of tuple indices by repeated division. -/
namespace GroupWL.MachinePrograms.IndexedWL
open NatArrayLanguage GroupWL.IndexedRefinement
set_option maxRecDepth 2048

def decodeAtoms : List (Atom Reg Arr) := [
  .divmod .quotient .digit .decodeValue .n,
  .write .vector .coordinate .digit,
  .copy .decodeValue .quotient]

def decodeBody : Code := atoms decodeAtoms

theorem decodeBody_runs (S : Store Reg Arr) (m n v i : ℕ)
    (hS : S.Bounded m) (hn : S.scalar .n=n) (hpos : 0<n)
    (hv : S.scalar .decodeValue=v/n^i) (hi : S.scalar .coordinate=i)
    (hlen : i<(S.array .vector).length) :
    ∃ T,Runs (storageBound Reg Arr m) decodeBody S 3 T ∧ T.Bounded m ∧
      T.scalar .decodeValue=v/n^(i+1) ∧
      T.array .vector=(S.array .vector).set i (digit n v i) := by
  have hvalid : ValidAtoms m decodeAtoms S := by
    simp only [decodeAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,
      Store.setScalar,Store.setArray,Function.update_apply]
    simp only [hn,hv,hi,reduceCtorEq,if_true,if_false]
    exact ⟨⟨by decide,hpos⟩,trivial,hlen,trivial,trivial,trivial,trivial⟩
  obtain ⟨run,hT⟩ := atoms_runs hS decodeAtoms hvalid
  refine ⟨applyAtoms decodeAtoms S,run,hT,?_,?_⟩
  · simp only [applyAtoms,decodeAtoms,List.foldl_cons,List.foldl_nil,Atom.apply,
      Store.setScalar,Store.setArray,Function.update_apply,reduceCtorEq,if_true,if_false,hv,hn,
      Nat.div_div_eq_div_mul,pow_succ]
  · simp only [applyAtoms,decodeAtoms,List.foldl_cons,List.foldl_nil,Atom.apply,
      Store.setScalar,Store.setArray,Function.update_apply,reduceCtorEq,if_true,if_false,hv,hn,hi,digit]

private structure DecodeInvariant (n k v m i : ℕ) (S : Store Reg Arr) : Prop where
  bounded : S.Bounded m
  index_eq : S.scalar .coordinate=i
  remaining_eq : S.scalar .coordinateTodo=k-i
  one_eq : S.scalar .one=1
  base_eq : S.scalar .n=n
  value_eq : S.scalar .decodeValue=v/n^i
  length_eq : (S.array .vector).length=k
  digits_eq : ∀ j < i, read (S.array .vector) j=digit n v j

theorem decodeLoop_runs (S : Store Reg Arr) (m n k v : ℕ)
    (hS : S.Bounded m) (hn : S.scalar .n=n) (hpos : 0<n)
    (hk : S.scalar .arity=k) (hv : S.scalar .decodeValue=v)
    (hone : S.scalar .one=1) (hlen : (S.array .vector).length=k) :
    ∃ t≤6*k+3,∃ T,
      Runs (storageBound Reg Arr m) (loop .coordinate .coordinateTodo .arity decodeBody) S t T ∧
      T.Bounded m ∧ T.array .vector=vectorWord n k v := by
  have hkbound : k≤m := by simpa [hk] using hS.1 .arity
  let I := DecodeInvariant n k v m
  have hcopy : (S.setScalar .coordinateTodo (S.scalar .arity)).Bounded m := hS.setScalar _ (hS.1 _)
  have hstart : I 0 ((S.setScalar .coordinateTodo (S.scalar .arity)).setScalar .coordinate 0) := by
    refine ⟨hcopy.setScalar _ (Nat.zero_le _),?_,?_,?_,?_,?_,?_,?_⟩
    · simp
    · simp [hk]
    · simp [hone]
    · simp [hn]
    · simp [hv]
    · simpa using hlen
    · intro j hj; omega
  have hcontrol : ∀ i≤k,∀ T,I i T →
      T.scalar .coordinate=i ∧ T.scalar .coordinateTodo=k-i ∧ T.scalar .one=1 ∧
        T.size≤storageBound Reg Arr m := by
    intro i hi T hT
    exact ⟨hT.index_eq,hT.remaining_eq,hT.one_eq,Store.size_le_of_bounded hT.bounded⟩
  have hstep : ∀ i<k,∀ T,I i T →
      ∃ t≤3,∃ U,Runs (storageBound Reg Arr m) decodeBody T t U ∧
        U.scalar .coordinate=i ∧ U.scalar .coordinateTodo=k-i ∧ U.scalar .one=1 ∧
        (U.setScalar .coordinate (i+1)).size≤storageBound Reg Arr m ∧
        I (i+1) (advance .coordinate .coordinateTodo U) := by
    intro i hi T hT
    obtain ⟨U,run,hU,hval,harray⟩ := decodeBody_runs T m n v i hT.bounded hT.base_eq hpos
      hT.value_eq hT.index_eq (by simpa [hT.length_eq] using hi)
    have frame (r : Reg) (h₁ : r≠.quotient) (h₂ : r≠.digit) (h₃ : r≠.decodeValue) :
        U.scalar r=T.scalar r := by
      apply run.scalar_eq_of_not_mem
      simp [decodeBody,atoms,decodeAtoms,NatArrayLanguage.sequence,Program.scalarWrites,Atom.scalarWrites,h₁,h₂,h₃]
    have hui : U.scalar .coordinate=i := (frame _ (by decide) (by decide) (by decide)).trans hT.index_eq
    have hur : U.scalar .coordinateTodo=k-i :=
      (frame _ (by decide) (by decide) (by decide)).trans hT.remaining_eq
    have huone : U.scalar .one=1 := (frame _ (by decide) (by decide) (by decide)).trans hT.one_eq
    have hun : U.scalar .n=n := (frame _ (by decide) (by decide) (by decide)).trans hT.base_eq
    have hmid := hU.setScalar Reg.coordinate (show i+1≤m by omega)
    refine ⟨3,le_rfl,U,run,hui,hur,huone,Store.size_le_of_bounded hmid,?_⟩
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [advance,hui] using hmid.setScalar Reg.coordinateTodo (show U.scalar .coordinateTodo-1≤m by rw [hur]; omega)
    · simp [advance,hui]
    · simp [advance,hur]; omega
    · simpa [advance] using huone
    · simpa [advance] using hun
    · simpa [advance] using hval
    · simpa [advance,harray] using hT.length_eq
    · intro j hj
      change read (U.array .vector) j=digit n v j
      rw [harray]
      by_cases hji : j=i
      · subst j
        simp [IndexedRefinement.read,List.getElem?_set,hT.length_eq,hi]
      · have hlt : j < i := by omega
        simpa [IndexedRefinement.read,List.getElem?_set,hji,Ne.symm hji] using hT.digits_eq j hlt
  obtain ⟨t,ht,T,run,hT⟩ := countedLoop_runs (storageBound Reg Arr m)
    .coordinate .coordinateTodo .arity .one decodeBody k 3 I S
    (Store.size_le_of_bounded hS) (Store.size_le_of_bounded hcopy) hstart hcontrol
    (by decide) (by decide) hstep
  refine ⟨t,by omega,T,run,hT.bounded,?_⟩
  apply List.ext_getElem
  · simpa using hT.length_eq
  · intro i hi hi'
    have hr := hT.digits_eq i (by simpa [hT.length_eq] using hi)
    simpa [IndexedRefinement.read,vectorWord,List.getElem?_eq_getElem,hi] using hr

theorem decodeVector_runs (S : Store Reg Arr) (m n k v : ℕ)
    (hS : S.Bounded m) (hn : S.scalar .n=n) (hpos : 0<n)
    (hk : S.scalar .arity=k) (hv : S.scalar .value=v)
    (hone : S.scalar .one=1) (hlen : (S.array .vector).length=k) :
    ∃ t≤6*k+4,∃ T,Runs (storageBound Reg Arr m) decodeVector S t T ∧
      T.Bounded m ∧ T.array .vector=vectorWord n k v := by
  let A := S.setScalar Reg.decodeValue v
  have hA : A.Bounded m := hS.setScalar _ (by simpa [hv] using hS.1 .value)
  have first : Runs (storageBound Reg Arr m) (atom (.copy .decodeValue .value)) S 1 A := by
    simpa [A,atom,Atom.apply,hv] using atom_runs hS (.copy .decodeValue .value) trivial trivial
  obtain ⟨t,ht,T,rest,hT,hvec⟩ := decodeLoop_runs A m n k v hA
    (by simp [A,hn]) hpos (by simp [A,hk]) (by simp [A]) (by simp [A,hone]) (by simpa [A] using hlen)
  refine ⟨1+(t+0),by omega,T,?_,hT,hvec⟩
  exact Runs.seq first (Runs.seq rest (Runs.skip rest.end_bound))

end GroupWL.MachinePrograms.IndexedWL
