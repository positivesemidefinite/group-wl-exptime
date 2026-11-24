import GroupWL.MachinePrograms.GeneratorSearch
import GroupWL.MachinePrograms.NatArrayPowers
import GroupWL.NumericGroupGenerators
import GroupWL.MachinePrograms.GroupInitial

/-! Initialize the generator search, compute its exact tuple bound, and
materialize the chosen tuple in the decoder's output array. -/
namespace GroupWL.MachinePrograms.GeneratorChoice
open NatArrayLanguage
abbrev Reg := GeneratorSearch.Reg
abbrev Arr := GeneratorSearch.Arr
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false

def decoderReg (r : IndexedWL.Reg) : Reg := .inl (.inl r)
def decoderArr (a : IndexedWL.Arr) : Arr := .inl (.inl a)
def seedReg (r : GeneratorMask.Reg) : Reg := .inl (IndexedGeneratorTest.sourceReg r)
def closureReg (r : GroupSaturation.Reg) : Reg := .inl (IndexedGeneratorTest.closureReg r)
def closureArr (a : GroupSaturation.Arr) : Arr := .inl (IndexedGeneratorTest.closureArr a)

def powerRegs : Fin 5 ↪ Reg :=
  ⟨![decoderReg .n,decoderReg .arity,.inr .limit,.inr .todo,.inr .one],by decide⟩

def prepare : List (Atom Reg Arr) := [
  .const (decoderReg .one) 1,.const (decoderReg .zero) 0,
  .copy (seedReg .order) (decoderReg .n),.copy (closureReg .order) (decoderReg .n),
  .allocate (decoderArr .vector) (decoderReg .arity) (decoderReg .zero)]

def decode : Code := (IndexedWL.decodeVector.map Sum.inl Sum.inl).map Sum.inl Sum.inl

def choose : Code := sequence [atoms prepare,power powerRegs,GeneratorSearch.search,
  .atom (.copy (decoderReg .value) (.inr .result)),decode]

theorem choose_runs {n k : ℕ} (S : State) (M : ℕ) (e : Fin n)
    (op : Fin n → Fin n → Fin n) (table : List ℕ)
    (hb : S.Bounded M) (hn : S.scalar (decoderReg .n)=n) (hk : S.scalar (decoderReg .arity)=k)
    (he : S.scalar (seedReg .identity)=e.val) (ht : S.array (closureArr .table)=table)
    (hlen : table.length=n*n)
    (hread : ∀i : Fin (n*n),table[i.val]?.getD 0=(op (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2).val)
    (hroom : n*n≤M) (hpow : n^k≤M) :
    ∃t≤n^k*(10*n^3+13*n+11*k+35)+9*k+20,∃T,Runs (storageBound Reg Arr M) choose S t T ∧
      T.Bounded M ∧ GeneratorSearch.Ready n k e table T.left ∧
      T.scalar (.inr .found)=(if (NatArrayPredicateSearch.hit (GeneratorSearch.Accepts (k:=k) e op) (n^k)).isSome then 1 else 0) ∧
      T.scalar (.inr .result)=(NatArrayPredicateSearch.hit (GeneratorSearch.Accepts (k:=k) e op) (n^k)).getD 0 ∧
      T.array (decoderArr .vector)=IndexedRefinement.vectorWord n k
        ((NatArrayPredicateSearch.hit (GeneratorSearch.Accepts (k:=k) e op) (n^k)).getD 0) ∧
      T.scalar (.inr .limit)=n^k := by
  have hnpos : 0<n := by have := e.isLt; omega
  have h1 : 1≤M := (one_le_pow₀ hnpos).trans hpow
  have valid : ValidAtoms M prepare S := by
    simp only [prepare,ValidAtoms,Atom.Valid,Atom.SmallResult]
    exact ⟨trivial,h1,trivial,Nat.zero_le _,trivial,trivial,trivial,trivial,trivial,trivial,trivial⟩
  obtain ⟨rp,hP⟩ := atoms_runs hb prepare valid
  let P := applyAtoms prepare S
  have hnP : P.scalar (decoderReg .n)=n := by
    simp [P,prepare,applyAtoms,Atom.apply,Store.setScalar,Store.setArray,decoderReg,decoderArr,seedReg,closureReg,
      IndexedGeneratorTest.sourceReg,IndexedGeneratorTest.closureReg] at hn ⊢
    exact hn
  have hkP : P.scalar (decoderReg .arity)=k := by
    rw [rp.scalar_eq_of_not_mem _ (by decide)]; exact hk
  have readyP : GeneratorSearch.Ready n k e table P.left := by
    constructor
    · exact hnP
    · exact hkP
    all_goals simp [P,prepare,applyAtoms,Atom.apply,Store.setScalar,Store.setArray,Store.left,
      decoderReg,decoderArr,seedReg,closureReg,closureArr,IndexedGeneratorTest.sourceReg,
      IndexedGeneratorTest.closureReg,IndexedGeneratorTest.closureArr] at hn hk he ht ⊢
    all_goals assumption
  obtain ⟨Q,rq,hQ,hlimit⟩ := power_runs powerRegs P n k M hP hnpos
    (by simpa [powerRegs] using hnP) (by simpa [powerRegs] using hkP) hpow
  have readyQ : GeneratorSearch.Ready n k e table Q.left := by
    rcases readyP with ⟨r₀,r₁,r₂,r₃,r₄,r₅,r₆,r₇⟩
    constructor
    · rw [show Q.left.scalar (.inl .n)=P.left.scalar (.inl .n) from rq.scalar_eq_of_not_mem _ (by decide)]; exact r₀
    · rw [show Q.left.scalar (.inl .arity)=P.left.scalar (.inl .arity) from rq.scalar_eq_of_not_mem _ (by decide)]; exact r₁
    · rw [show Q.left.scalar (.inl .one)=P.left.scalar (.inl .one) from rq.scalar_eq_of_not_mem _ (by decide)]; exact r₂
    · rw [show Q.left.array (.inl .vector)=P.left.array (.inl .vector) from rq.array_eq_of_not_mem _ (by decide)]; exact r₃
    · rw [show Q.left.scalar (IndexedGeneratorTest.sourceReg .order)=P.left.scalar (IndexedGeneratorTest.sourceReg .order) from rq.scalar_eq_of_not_mem _ (by decide)]; exact r₄
    · rw [show Q.left.scalar (IndexedGeneratorTest.sourceReg .identity)=P.left.scalar (IndexedGeneratorTest.sourceReg .identity) from rq.scalar_eq_of_not_mem _ (by decide)]; exact r₅
    · rw [show Q.left.scalar (IndexedGeneratorTest.closureReg .order)=P.left.scalar (IndexedGeneratorTest.closureReg .order) from rq.scalar_eq_of_not_mem _ (by decide)]; exact r₆
    · rw [show Q.left.array (IndexedGeneratorTest.closureArr .table)=P.left.array (IndexedGeneratorTest.closureArr .table) from rq.array_eq_of_not_mem _ (by decide)]; exact r₇
  obtain ⟨ts,hts,U,rs,hU,readyU,hfound,hresult⟩ := GeneratorSearch.search_runs Q M e op table hQ readyQ
    (by simpa [powerRegs] using hlimit) hlen hread hroom
  let V := (Atom.copy (decoderReg .value) (.inr .result)).apply U
  have hV : V.Bounded M := Atom.apply_bounded hU _ trivial
  have rv := atom_runs hU (.copy (decoderReg .value) (.inr .result)) trivial trivial
  obtain ⟨td,htd,W,rd,hW,hvector⟩ := IndexedWL.decodeVector_runs V.left.left M n k
    (U.scalar (.inr .result)) hV.left.left
    (by simpa [V,Atom.apply,decoderReg,Store.left] using readyU.base) hnpos
    (by simpa [V,Atom.apply,decoderReg,Store.left] using readyU.arity)
    (by simp [V,Atom.apply,decoderReg,Store.left])
    (by simpa [V,Atom.apply,decoderReg,Store.left] using readyU.one)
    (by simpa [V,Atom.apply,decoderReg,Store.left] using readyU.vector)
  let T := (W.join V.left.right).join V.right
  have rd' : Runs (storageBound Reg Arr M) decode V td T := (rd.left_bounded hV.left).left_bounded hV
  have hT : T.Bounded M := (hW.join hV.left.right).join hV.right
  have tailRun : Runs (storageBound Reg Arr M) (.seq (.atom (.copy (decoderReg .value) (.inr .result))) decode) U (1+td) T := .seq rv rd'
  refine ⟨5+((3*k+4)+(ts+(1+(td+0)))),by omega,T,
    .seq rp (.seq rq (.seq rs (.seq rv (.seq rd' (.skip rd'.end_bound))))),hT,?_,?_,?_,?_,?_⟩
  · rcases readyU with ⟨r₀,r₁,r₂,r₃,r₄,r₅,r₆,r₇⟩
    constructor
    · rw [show T.left.scalar (.inl .n)=U.left.scalar (.inl .n) from tailRun.scalar_eq_of_not_mem (decoderReg .n) (by decide)]; exact r₀
    · rw [show T.left.scalar (.inl .arity)=U.left.scalar (.inl .arity) from tailRun.scalar_eq_of_not_mem (decoderReg .arity) (by decide)]; exact r₁
    · rw [show T.left.scalar (.inl .one)=U.left.scalar (.inl .one) from tailRun.scalar_eq_of_not_mem (decoderReg .one) (by decide)]; exact r₂
    · change (W.array .vector).length=k
      simp [hvector]
    · rw [show T.left.scalar (IndexedGeneratorTest.sourceReg .order)=U.left.scalar (IndexedGeneratorTest.sourceReg .order) from tailRun.scalar_eq_of_not_mem (seedReg .order) (by decide)]; exact r₄
    · rw [show T.left.scalar (IndexedGeneratorTest.sourceReg .identity)=U.left.scalar (IndexedGeneratorTest.sourceReg .identity) from tailRun.scalar_eq_of_not_mem (seedReg .identity) (by decide)]; exact r₅
    · rw [show T.left.scalar (IndexedGeneratorTest.closureReg .order)=U.left.scalar (IndexedGeneratorTest.closureReg .order) from tailRun.scalar_eq_of_not_mem (closureReg .order) (by decide)]; exact r₆
    · rw [show T.left.array (IndexedGeneratorTest.closureArr .table)=U.left.array (IndexedGeneratorTest.closureArr .table) from tailRun.array_eq_of_not_mem (closureArr .table) (by decide)]; exact r₇
  · rw [tailRun.scalar_eq_of_not_mem _ (by decide)]; exact hfound
  · rw [tailRun.scalar_eq_of_not_mem _ (by decide)]; exact hresult
  · change W.array .vector=_
    rw [hvector,hresult]
  · rw [tailRun.scalar_eq_of_not_mem _ (by decide),rs.scalar_eq_of_not_mem _ (by decide)]
    simpa [powerRegs] using hlimit

theorem choose_numeric_runs {p D : ℕ} [Fact p.Prime] (g : Group (Fin (p^D)))
    (S : State) (M : ℕ) (hb : S.Bounded M)
    (hn : S.scalar (decoderReg .n)=p^D) (hk : S.scalar (decoderReg .arity)=D)
    (he : S.scalar (seedReg .identity)=(NumericGroupGenerators.identity g).val)
    (ht : S.array (closureArr .table)=GroupInitial.tableWord (NumericGroupGenerators.operation g))
    (hroom : (p^D)*(p^D)≤M) (hpow : (p^D)^D≤M) :
    ∃t≤(p^D)^D*(10*(p^D)^3+13*(p^D)+11*D+35)+9*D+20,∃T,
      Runs (storageBound Reg Arr M) choose S t T ∧ T.Bounded M ∧
      GeneratorSearch.Ready (p^D) D (NumericGroupGenerators.identity g)
        (GroupInitial.tableWord (NumericGroupGenerators.operation g)) T.left ∧
      T.scalar (.inr .found)=1 ∧ T.scalar (.inr .result)=(NumericGroupGenerators.index g).val ∧
      T.array (decoderArr .vector)=GroupInitial.tupleWord (NumericGroupGenerators.generators g) ∧
      T.scalar (.inr .limit)=(p^D)^D := by
  have hr (i : Fin ((p^D)*(p^D))) :
      (GroupInitial.tableWord (NumericGroupGenerators.operation g))[i.val]?.getD 0=
        (NumericGroupGenerators.operation g (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2).val := by
    simp [GroupInitial.tableWord,i.isLt]
  obtain ⟨t,hc,T,run,hT,ready,hfound,hresult,hvector,hlimit⟩ := choose_runs S M
    (NumericGroupGenerators.identity g) (NumericGroupGenerators.operation g)
    (GroupInitial.tableWord (NumericGroupGenerators.operation g)) hb hn hk he ht
    (GroupInitial.tableWord_length _) hr hroom hpow
  obtain ⟨i,hi,hh,hgood⟩ := NumericGroupGenerators.first_exists g
  refine ⟨t,hc,T,run,hT,ready,?_,hresult,?_,hlimit⟩
  · change T.scalar (.inr .found)=(1:ℕ)
    change T.scalar (.inr .found)=(if (NatArrayPredicateSearch.hit (NumericGroupGenerators.predicate g) ((p^D)^D)).isSome then 1 else 0) at hfound
    simpa [hh] using hfound
  · exact hvector

end GroupWL.MachinePrograms.GeneratorChoice
