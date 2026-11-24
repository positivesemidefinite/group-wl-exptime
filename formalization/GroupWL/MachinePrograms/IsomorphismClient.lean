import GroupWL.MachinePrograms.GroupIsomorphismSearch
import GroupWL.MachinePrograms.ProductGroupTable
import GroupWL.MachinePrograms.NatArrayPowers

/-! Initialize isomorphism search directly from two multiplication tables
and a source generating tuple. -/
namespace GroupWL.MachinePrograms.IsomorphismClient
open NatArrayLanguage
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

abbrev Reg := ProductGroupTable.Reg ⊕ GroupIsomorphismSearch.Reg
abbrev Arr := ProductGroupTable.Arr ⊕ GroupIsomorphismSearch.Arr
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr
instance : DecidableEq Reg := inferInstance
instance : DecidableEq Arr := inferInstance
instance : Fintype Reg := inferInstance
instance : Fintype Arr := inferInstance

def innerReg (r : IndexedImageTest.Reg) : Reg := .inr (.inl r)
def innerArr (a : IndexedImageTest.Arr) : Arr := .inr (.inl a)
def decoderReg (r : IndexedWL.Reg) : Reg := innerReg (.inl r)
def decoderArr (a : IndexedWL.Arr) : Arr := innerArr (.inl a)
def groupReg (r : GroupImageTest.Reg) : Reg := innerReg (.inr r)
def groupArr (a : GroupImageTest.Arr) : Arr := innerArr (.inr a)
def expansionReg (r : PairedImageExpansion.Reg) : Reg := groupReg (.inl (.inr r))
def expansionArr (a : PairedImageExpansion.Arr) : Arr := groupArr (.inl (.inr a))
def identityReg : Reg := expansionReg (PairedImageExpansion.seedReg .identity)
def identityReg' : Reg := expansionReg (PairedImageExpansion.imageReg .identity)
def sourceTuple : Arr := innerArr IndexedImageTest.sourceTuple
def resultReg : Reg := .inr (.inr .found)

def prepare : List (Atom Reg Arr) := [
  .copy (decoderReg .n) (.inl 1),.const (decoderReg .one) 1,.const (decoderReg .zero) 0,
  .allocate (decoderArr .vector) (decoderReg .arity) (decoderReg .zero),
  .copy (groupReg (.inl (.inl .cols))) (.inl 1),
  .binary .mul (expansionReg (PairedImageExpansion.seedReg .order)) (.inl 0) (.inl 1),
  .binary .mul identityReg identityReg (.inl 1),.binary .add identityReg identityReg identityReg',
  .copy (expansionReg (PairedImageExpansion.closureReg .order)) (expansionReg (PairedImageExpansion.seedReg .order)),
  .copyArray (expansionArr (PairedImageExpansion.closureArray .table)) (.inl 2),
  .copy (expansionReg (PairedImageExpansion.imageReg .rows)) (.inl 0),
  .copy (expansionReg (PairedImageExpansion.imageReg .cols)) (.inl 1),
  .copy (groupReg (.inr .sourceOrder)) (.inl 0),.copy (groupReg (.inr .targetOrder)) (.inl 1),
  .copyArray (groupArr (.inr .source)) (.inl 0),.copyArray (groupArr (.inr .target)) (.inl 1)]
def powerRegisters : Fin 5 ↪ Reg :=
  ⟨![decoderReg .n,decoderReg .arity,.inr (.inr .limit),.inr (.inr .todo),.inr (.inr .one)],by decide⟩
def compare : Code := sequence [ProductGroupTable.generate.map Sum.inl Sum.inl,atoms prepare,
  power powerRegisters,GroupIsomorphismSearch.search.map Sum.inr Sum.inr]

theorem compare_runs {n m k : ℕ} (S : State) (M : ℕ)
    (op : Fin n→Fin n→Fin n) (op' : Fin m→Fin m→Fin m)
    (identity : Fin n) (identity' : Fin m) (a : Fin k→Fin n)
    (hb : S.Bounded M) (hn : S.scalar (.inl 0)=n) (hm : S.scalar (.inl 1)=m)
    (hk : S.scalar (decoderReg .arity)=k)
    (hi : S.scalar identityReg=identity.val) (hi' : S.scalar identityReg'=identity'.val)
    (hs : S.array (.inl 0)=GroupInitial.tableWord op) (ht : S.array (.inl 1)=GroupInitial.tableWord op')
    (ha : S.array sourceTuple=GroupInitial.tupleWord a)
    (hroom : (n*m)*(n*m)≤M) (hpow : m^k≤M) :
    ∃t≤m^k*(10*(n*m)^3+8*(n*m)+19*k+n*(9*m+13)+19*n*n+49)+15*((n*m)*(n*m))+3*k+34,∃T,
      Runs (storageBound Reg Arr M) compare S t T ∧ T.Bounded M ∧
      T.scalar resultReg=(if (NatArrayPredicateSearch.hit
        (IndexedImageTest.Accepts op op' identity identity' a) (m^k)).isSome then 1 else 0) := by
  have hpos : 0<n*m := Nat.mul_pos (Nat.zero_lt_of_lt identity.isLt) (Nat.zero_lt_of_lt identity'.isLt)
  have hN : n*m≤M := by nlinarith
  have h1 : 1≤M := by nlinarith
  obtain ⟨t,htime,U,product,hU,ho⟩ := ProductGroupTable.generate_runs op op' S.left M hb.left hn hm hs ht hpos hroom
  let V := U.join S.right
  have hV : V.Bounded M := hU.join hb.right
  have hnV : V.scalar (.inl 0)=n := (product.scalar_eq_of_not_mem 0 (by decide)).trans hn
  have hmV : V.scalar (.inl 1)=m := (product.scalar_eq_of_not_mem 1 (by decide)).trans hm
  have hkV : V.scalar (decoderReg .arity)=k := hk
  have hiV : V.scalar identityReg=identity.val := hi
  have hiV' : V.scalar identityReg'=identity'.val := hi'
  have hsV : V.array (.inl 0)=GroupInitial.tableWord op := (product.array_eq_of_not_mem 0 (by decide)).trans hs
  have htV : V.array (.inl 1)=GroupInitial.tableWord op' := (product.array_eq_of_not_mem 1 (by decide)).trans ht
  have haV : V.array sourceTuple=GroupInitial.tupleWord a := ha
  have hmul : identity.val*m≤M := by nlinarith [identity.isLt]
  have hadd : identity.val*m+identity'.val≤M := by nlinarith [identity.isLt,identity'.isLt]
  have hv : ValidAtoms M prepare V := by
    simp [prepare,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,Store.setArray,innerReg,innerArr,decoderReg,decoderArr,groupReg,groupArr,
      expansionReg,expansionArr,identityReg,identityReg',PairedImageExpansion.seedReg,
      PairedImageExpansion.closureReg,PairedImageExpansion.imageReg,PairedImageExpansion.closureArray]
      at hiV hiV' hkV ⊢
    simp [hnV,hmV,hiV,hiV',hN,hmul,hadd,h1]
  obtain ⟨prep,hW⟩ := atoms_runs hV prepare hv
  let W := applyAtoms prepare V
  have ready : IndexedImageTest.Ready op op' identity identity' a W.right.left := by
    refine ⟨?_,?_,?_,?_,⟨⟨?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_⟩,?_⟩
    all_goals simp [W,applyAtoms,prepare,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,
      innerReg,innerArr,decoderReg,decoderArr,groupReg,groupArr,expansionReg,expansionArr,
      identityReg,identityReg',Store.right,Store.left,PairedImageExpansion.seedReg,
      PairedImageExpansion.closureReg,PairedImageExpansion.closureArray,PairedImageExpansion.imageReg,
      IndexedImageTest.sourceTuple]
    all_goals first
      | exact hmV
      | exact hnV
      | exact ho
      | exact hsV
      | exact htV
      | simpa [decoderReg,innerReg] using hkV
      | simpa [sourceTuple,innerArr,IndexedImageTest.sourceTuple,GroupInitial.tupleWord] using haV
      | simpa [identityReg,identityReg',expansionReg,groupReg,innerReg,
          PairedImageExpansion.seedReg,PairedImageExpansion.imageReg] using hiV'
      | simpa [finProdFinEquiv,Nat.add_comm,Nat.mul_comm,hnV,hmV,
          identityReg,identityReg',expansionReg,groupReg,innerReg,
          PairedImageExpansion.seedReg,PairedImageExpansion.imageReg] using congrArg₂ (fun x y => x*m+y) hiV hiV'
  obtain ⟨Q,powerRun,hQ,hlimit⟩ := power_runs powerRegisters W m k M hW
    (Nat.zero_lt_of_lt identity'.isLt) (by simpa [powerRegisters,decoderReg,innerReg,Store.right,Store.left] using ready.base)
    (by simpa [powerRegisters,decoderReg,innerReg,Store.right,Store.left] using ready.arity) hpow
  have hinner : Q.right.left=W.right.left := by
    apply Store.ext
    · intro r
      exact powerRun.scalar_eq_of_not_mem (.inr (.inl r))
        ((by decide : ∀r:IndexedImageTest.Reg,(Sum.inr (Sum.inl r) : Reg)∉(power powerRegisters : Code).scalarWrites) r)
    · intro ar
      exact powerRun.array_eq_of_not_mem (.inr (.inl ar))
        ((by decide : ∀ar:IndexedImageTest.Arr,(Sum.inr (Sum.inl ar) : Arr)∉(power powerRegisters : Code).arrayWrites) ar)
  obtain ⟨u,hu,X,search,hX,hreadyX,hout⟩ := GroupIsomorphismSearch.search_runs Q.right M op op' identity identity' a hQ.right
    (by rw [hinner]; exact ready) (by simpa [powerRegisters,Store.right] using hlimit) hroom
  have searched := search.right_bounded hQ
  refine ⟨t+(16+((3*k+4)+(u+0))),by omega,Q.left.join X,
    .seq (product.left_bounded hb) (.seq prep (.seq powerRun (.seq searched (.skip searched.end_bound)))),hQ.left.join hX,?_⟩
  exact hout

variable {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H]

theorem compare_correct {n m k : ℕ} (eG : Fin n≃G) (eH : Fin m≃H)
    (op : Fin n→Fin n→Fin n) (op' : Fin m→Fin m→Fin m)
    (hop : ∀x y,eG (op x y)=eG x*eG y) (hop' : ∀x y,eH (op' x y)=eH x*eH y)
    (identity : Fin n) (identity' : Fin m) (hid : eG identity=1) (hid' : eH identity'=1)
    (a : Fin k→Fin n) (haGen : Refinement.Generates (eG ∘ a)) (hnm : n=m)
    (S : State) (M : ℕ) (hb : S.Bounded M) (hn : S.scalar (.inl 0)=n) (hm : S.scalar (.inl 1)=m)
    (hk : S.scalar (decoderReg .arity)=k)
    (hi : S.scalar identityReg=identity.val) (hi' : S.scalar identityReg'=identity'.val)
    (hs : S.array (.inl 0)=GroupInitial.tableWord op) (ht : S.array (.inl 1)=GroupInitial.tableWord op')
    (ha : S.array sourceTuple=GroupInitial.tupleWord a)
    (hroom : (n*m)*(n*m)≤M) (hpow : m^k≤M) :
    ∃t≤m^k*(10*(n*m)^3+8*(n*m)+19*k+n*(9*m+13)+19*n*n+49)+15*((n*m)*(n*m))+3*k+34,∃T,
      Runs (storageBound Reg Arr M) compare S t T ∧ T.Bounded M ∧ T.scalar resultReg≤1 ∧
      (T.scalar resultReg=1 ↔ Nonempty (G≃*H)) := by
  obtain ⟨t,htime,T,run,hT,hf⟩ := compare_runs S M op op' identity identity' a hb hn hm hk hi hi' hs ht ha hroom hpow
  refine ⟨t,htime,T,run,hT,by rw [hf]; split_ifs <;> omega,?_⟩
  rw [hf]
  have hc := (NatArrayPredicateSearch.hit_isSome_iff (IndexedImageTest.Accepts op op' identity identity' a) (m^k)).trans
    ((NumericGroupImages.exists_index_iff op op' identity identity' a).trans
      (NumericGroupImages.exists_valid_iff eG eH op op' hop hop' identity identity' hid hid' a haGen hnm))
  cases h : (NatArrayPredicateSearch.hit (IndexedImageTest.Accepts op op' identity identity' a) (m^k)).isSome <;>
    simpa [h] using hc

end GroupWL.MachinePrograms.IsomorphismClient
