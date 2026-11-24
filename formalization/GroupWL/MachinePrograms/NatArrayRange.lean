import GroupWL.MachinePrograms.NatArrayFrames
import GroupWL.MachinePrograms.NatArrayCountedLoops

/-! Materialize an ascending interval of numeric state indices. -/
namespace GroupWL.MachinePrograms.NatArrayRange
open NatArrayLanguage
abbrev Reg := Fin 7
abbrev Arr := Unit
abbrev Code := Program Reg Arr

def word (n offset : ℕ) : List ℕ := List.ofFn (fun i : Fin n => offset+i.val)

def bodyAtoms : List (Atom Reg Arr) := [.binary .add 5 1 2,.write () 2 5]
def body : Code := atoms bodyAtoms

theorem body_runs (S : Store Reg Arr) (B n offset i : ℕ) (hS : S.Bounded B)
    (ho : S.scalar 1=offset) (hi : S.scalar 2=i) (hlen : (S.array ()).length=n)
    (hil : i<n) (hroom : offset+n≤B) :
    ∃ T,Runs (storageBound Reg Arr B) body S 2 T ∧ T.Bounded B ∧
      T.array ()=(S.array ()).set i (offset+i) := by
  have hv : ValidAtoms B bodyAtoms S := by
    simp [bodyAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,ho,hi,hlen,hil,show offset+i≤B by omega]
  obtain ⟨run,hT⟩ := atoms_runs hS bodyAtoms hv
  exact ⟨_,run,hT,by simp [applyAtoms,bodyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,ho,hi]⟩

private structure Invariant (n offset B i : ℕ) (S : Store Reg Arr) : Prop where
  bounded : S.Bounded B
  offset_eq : S.scalar 1=offset
  index_eq : S.scalar 2=i
  todo_eq : S.scalar 3=n-i
  one_eq : S.scalar 4=1
  length_eq : (S.array ()).length=n
  values_eq : ∀ j < i,(S.array ())[j]?.getD 0=offset+j

def fill : Code := countedLoop 2 3 0 4 body

theorem fill_runs (S : Store Reg Arr) (B n offset : ℕ) (hS : S.Bounded B)
    (hn : S.scalar 0=n) (ho : S.scalar 1=offset) (hone : S.scalar 4=1)
    (hlen : (S.array ()).length=n) (hroom : offset+n≤B) :
    ∃ t≤5*n+3,∃ T,Runs (storageBound Reg Arr B) fill S t T ∧ T.Bounded B ∧
      T.array ()=word n offset := by
  let I := Invariant n offset B
  have hcopy : (S.setScalar 3 (S.scalar 0)).Bounded B := hS.setScalar _ (hS.1 _)
  have hstart : I 0 ((S.setScalar 3 (S.scalar 0)).setScalar 2 0) := by
    refine ⟨hcopy.setScalar _ (Nat.zero_le _),?_,?_,?_,?_,hlen,?_⟩
    · simp [ho]
    · simp
    · simp [hn]
    · simp [hone]
    · intro j hj; omega
  have control : ∀ i≤n,∀ U,I i U → U.scalar 2=i ∧ U.scalar 3=n-i ∧ U.scalar 4=1 ∧
      U.size≤storageBound Reg Arr B := by
    intro i hi U hU
    exact ⟨hU.index_eq,hU.todo_eq,hU.one_eq,Store.size_le_of_bounded hU.bounded⟩
  have step : ∀ i<n,∀ U,I i U → ∃ t≤2,∃ V,Runs (storageBound Reg Arr B) body U t V ∧
      V.scalar 2=i ∧ V.scalar 3=n-i ∧ V.scalar 4=1 ∧
      (V.setScalar 2 (i+1)).size≤storageBound Reg Arr B ∧ I (i+1) (advance 2 3 V) := by
    intro i hi U hU
    obtain ⟨V,run,hV,harray⟩ := body_runs U B n offset i hU.bounded hU.offset_eq hU.index_eq
      hU.length_eq hi hroom
    have frames (r : Reg) (hr : r≠5) : V.scalar r=U.scalar r := run.scalar_eq_of_not_mem r (by
      simp [body,atoms,bodyAtoms,NatArrayLanguage.sequence,Program.scalarWrites,Atom.scalarWrites,hr])
    have hvi : V.scalar 2=i := (frames _ (by decide)).trans hU.index_eq
    have hvr : V.scalar 3=n-i := (frames _ (by decide)).trans hU.todo_eq
    have hvone : V.scalar 4=1 := (frames _ (by decide)).trans hU.one_eq
    have hmid := hV.setScalar 2 (show i+1≤B by omega)
    refine ⟨2,le_rfl,V,run,hvi,hvr,hvone,Store.size_le_of_bounded hmid,?_⟩
    refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [advance,hvi] using hmid.setScalar 3 (show V.scalar 3-1≤B by rw [hvr]; omega)
    · simpa [advance] using (frames _ (by decide)).trans hU.offset_eq
    · simp [advance,hvi]
    · simp [advance,hvr]; omega
    · simpa [advance] using hvone
    · simpa [advance,harray] using hU.length_eq
    · intro j hj
      change (V.array ())[j]?.getD 0=offset+j
      rw [harray]
      by_cases hji : j=i
      · subst j; simp [hU.length_eq,hi]
      · have hjl : j < i := by omega
        simpa [List.getElem?_set,hji,Ne.symm hji] using hU.values_eq j hjl
  obtain ⟨t,ht,T,run,hT⟩ := countedLoop_runs (storageBound Reg Arr B) 2 3 0 4 body n 2 I S
    (Store.size_le_of_bounded hS) (Store.size_le_of_bounded hcopy) hstart control
    (by decide) (by decide) step
  refine ⟨t,by omega,T,run,hT.bounded,?_⟩
  apply List.ext_getElem
  · simpa [word] using hT.length_eq
  · intro j hj hj'
    have hh := hT.values_eq j (by simpa [hT.length_eq] using hj)
    simpa only [List.getElem?_eq_getElem hj,Option.getD_some,word,List.getElem_ofFn] using hh

def prelude : List (Atom Reg Arr) := [.const 4 1,.const 6 0,.allocate () 0 6]
def generate : Code := .seq (atoms prelude) fill

theorem generate_runs (S : Store Reg Arr) (B n offset : ℕ) (hS : S.Bounded B)
    (hn : S.scalar 0=n) (ho : S.scalar 1=offset) (hroom : offset+n≤B) (h1 : 1≤B) :
    ∃ t≤5*n+6,∃ T,Runs (storageBound Reg Arr B) generate S t T ∧ T.Bounded B ∧
      T.array ()=word n offset := by
  have valid : ValidAtoms B prelude S := by simp [prelude,ValidAtoms,Atom.Valid,Atom.SmallResult,h1]
  obtain ⟨init,hU⟩ := atoms_runs hS prelude valid
  let U := applyAtoms prelude S
  obtain ⟨t,ht,T,run,hT,hword⟩ := fill_runs U B n offset hU
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar,Store.setArray,hn])
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar,Store.setArray,ho])
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar,Store.setArray])
    (by simp [U,applyAtoms,prelude,Atom.apply,Store.setScalar,Store.setArray,hn]) hroom
  exact ⟨3+t,by omega,T,Runs.seq init run,hT,hword⟩

end GroupWL.MachinePrograms.NatArrayRange
