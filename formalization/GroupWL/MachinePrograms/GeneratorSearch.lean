import GroupWL.MachinePrograms.IndexedGeneratorTest
import GroupWL.MachinePrograms.NatArrayPredicateLoop

/-! Actual search through all numeric tuples, using the compiled finite-group
closure test at every index. The candidate domain has size n^k. -/
namespace GroupWL.MachinePrograms.GeneratorSearch
open NatArrayLanguage
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

abbrev Reg := NatArrayPredicateSearch.Reg IndexedGeneratorTest.Reg
abbrev Arr := NatArrayPredicateSearch.Arr IndexedGeneratorTest.Arr
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

open IndexedGeneratorTest in
structure Ready (n k : ℕ) (e : Fin n) (table : List ℕ) (S : IndexedGeneratorTest.State) : Prop where
  base : S.scalar (.inl .n)=n
  arity : S.scalar (.inl .arity)=k
  one : S.scalar (.inl .one)=1
  vector : (S.array (.inl .vector)).length=k
  seedOrder : S.scalar (sourceReg .order)=n
  identity : S.scalar (sourceReg .identity)=e.val
  closureOrder : S.scalar (closureReg .order)=n
  table_eq : S.array (closureArr .table)=table

def Accepts {n k : ℕ} (e : Fin n) (op : Fin n → Fin n → Fin n) (i : ℕ) : Prop :=
  if hi : i<n^k then GroupSaturation.closureSet op
    (insert e (Finset.univ.image (finFunctionFinEquiv.symm (⟨i,hi⟩ : Fin (n^k))))) n=Finset.univ else False
instance {n k : ℕ} (e : Fin n) (op : Fin n → Fin n → Fin n) : DecidablePred (Accepts (k:=k) e op) :=
  fun i => by unfold Accepts; infer_instance

def search : Code := NatArrayPredicateSearch.search IndexedGeneratorTest.test
  (.inl .value) IndexedGeneratorTest.resultReg

open IndexedGeneratorTest in
theorem ready_setValue {n k : ℕ} {e : Fin n} {table : List ℕ} {S : IndexedGeneratorTest.State}
    (h : Ready n k e table S) (i : ℕ) : Ready n k e table (S.setScalar (.inl .value) i) := by
  rcases h with ⟨hn,hk,h1,hv,hseed,he,hclosure,ht⟩
  constructor <;> simp_all [sourceReg,closureReg]

open IndexedGeneratorTest in
theorem test_ready {n k M : ℕ} (e : Fin n) (op : Fin n → Fin n → Fin n) (table : List ℕ)
    (hlen : table.length=n*n)
    (hread : ∀i : Fin (n*n),table[i.val]?.getD 0=(op (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2).val)
    (hroom : n*n≤M) (S : IndexedGeneratorTest.State) (i : ℕ)
    (hb : S.Bounded M) (hready : Ready n k e table S) (hi : S.scalar (.inl .value)=i) (hiLt : i<n^k) :
    ∃t≤10*n^3+13*n+11*k+26,∃T,Runs (storageBound IndexedGeneratorTest.Reg IndexedGeneratorTest.Arr M)
      IndexedGeneratorTest.test S t T ∧ T.Bounded M ∧ Ready n k e table T ∧
      (T.scalar resultReg=1 ↔ Accepts (k:=k) e op i) := by
  obtain ⟨t,ht,T,run,hT,hvec,ho⟩ := IndexedGeneratorTest.test_runs S n k M ⟨i,hiLt⟩ e op hb
    hready.base hready.arity hi hready.one hready.vector hready.seedOrder hready.identity
    hready.closureOrder (by simpa [hready.table_eq] using hlen)
    (by simpa [hready.table_eq] using hread) hroom
  refine ⟨t,ht,T,run,hT,?_,?_⟩
  · exact ⟨(scalarFrame run _ (by decide)).trans hready.base,
      (scalarFrame run _ (by decide)).trans hready.arity,
      (scalarFrame run _ (by decide)).trans hready.one,hvec,
      (scalarFrame run _ (by decide)).trans hready.seedOrder,
      (scalarFrame run _ (by decide)).trans hready.identity,
      (scalarFrame run _ (by decide)).trans hready.closureOrder,
      (tableFrame run).trans hready.table_eq⟩
  · simpa [Accepts,hiLt] using ho

theorem search_runs {n k : ℕ} (S : State) (M : ℕ) (e : Fin n)
    (op : Fin n → Fin n → Fin n) (table : List ℕ)
    (hb : S.Bounded M) (hready : Ready n k e table S.left)
    (hlimit : S.scalar (.inr .limit)=n^k)
    (hlen : table.length=n*n)
    (hread : ∀i : Fin (n*n),table[i.val]?.getD 0=(op (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2).val)
    (hroom : n*n≤M) :
    ∃t≤n^k*(10*n^3+13*n+11*k+35)+6,∃T,Runs (storageBound Reg Arr M) search S t T ∧
      T.Bounded M ∧ Ready n k e table T.left ∧
      T.scalar (.inr .found)=(if (NatArrayPredicateSearch.hit (Accepts (k:=k) e op) (n^k)).isSome then 1 else 0) ∧
      T.scalar (.inr .result)=(NatArrayPredicateSearch.hit (Accepts (k:=k) e op) (n^k)).getD 0 := by
  have hM : 1≤M := by have := e.isLt; nlinarith
  obtain ⟨t,ht,T,run,hT,hreadyT,hf,hr⟩ := NatArrayPredicateSearch.search_runs
    IndexedGeneratorTest.test (.inl .value) IndexedGeneratorTest.resultReg
    (Ready n k e table) (Accepts (k:=k) e op) S M (n^k) (10*n^3+13*n+11*k+26) hb hM hready
    (fun U i h => ready_setValue h i) (test_ready e op table hlen hread hroom) hlimit
  exact ⟨t,by omega,T,run,hT,hreadyT,hf,hr⟩

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

theorem accepts_iff {n k : ℕ} (e : Fin n ≃ G) (op : Fin n → Fin n → Fin n)
    (he : ∀x y,e (op x y)=e x*e y) (i : Fin (n^k)) :
    Accepts (k:=k) (e.symm 1) op i.val ↔ Refinement.Generates (e ∘ finFunctionFinEquiv.symm i) := by
  simpa [Accepts,i.isLt] using GeneratorTest.closure_full_iff e op he (finFunctionFinEquiv.symm i)

theorem search_generators {n k : ℕ} (S : State) (M : ℕ) (e : Fin n ≃ G)
    (op : Fin n → Fin n → Fin n) (he : ∀x y,e (op x y)=e x*e y) (table : List ℕ)
    (hgen : ∃a : Fin k → G,Refinement.Generates a)
    (hb : S.Bounded M) (hready : Ready n k (e.symm 1) table S.left)
    (hlimit : S.scalar (.inr .limit)=n^k) (hlen : table.length=n*n)
    (hread : ∀i : Fin (n*n),table[i.val]?.getD 0=(op (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2).val)
    (hroom : n*n≤M) :
    ∃t≤n^k*(10*n^3+13*n+11*k+35)+6,∃T,Runs (storageBound Reg Arr M) search S t T ∧
      T.Bounded M ∧ Ready n k (e.symm 1) table T.left ∧ T.scalar (.inr .found)=1 ∧
      ∃hi : T.scalar (.inr .result)<n^k,
        Refinement.Generates (e ∘ finFunctionFinEquiv.symm (⟨T.scalar (.inr .result),hi⟩ : Fin (n^k))) := by
  have hex : ∃i<n^k,Accepts (k:=k) (e.symm 1) op i := by
    obtain ⟨a,ha⟩ := hgen
    let i : Fin (n^k) := finFunctionFinEquiv (e.symm ∘ a)
    refine ⟨i.val,i.isLt,(accepts_iff e op he i).mpr ?_⟩
    simpa [i,Function.comp_def] using ha
  obtain ⟨i,hi,hh,hp⟩ := NatArrayPredicateSearch.hit_exists _ (n^k) hex
  obtain ⟨t,ht,T,run,hT,hreadyT,hf,hr⟩ := search_runs S M (e.symm 1) op table hb hready hlimit hlen hread hroom
  have hresult : T.scalar (.inr .result)=i := by simpa [hh] using hr
  refine ⟨t,ht,T,run,hT,hreadyT,by simpa [hh] using hf,by omega,?_⟩
  simpa [hresult] using (accepts_iff e op he (⟨i,hi⟩ : Fin (n^k))).mp hp

end GroupWL.MachinePrograms.GeneratorSearch
