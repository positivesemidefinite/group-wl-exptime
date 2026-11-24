import GroupWL.NumericImageIsomorphism
import GroupWL.MachinePrograms.NatArrayPredicateLoop

/-! Finite generator-image enumeration with a concrete subgroup/table test
at every index. The enumerated domain has only m^k entries. -/
namespace GroupWL.MachinePrograms.GroupIsomorphismSearch
open NatArrayLanguage
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

abbrev Reg := NatArrayPredicateSearch.Reg IndexedImageTest.Reg
abbrev Arr := NatArrayPredicateSearch.Arr IndexedImageTest.Arr
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr
instance : DecidableEq Reg := inferInstance
instance : DecidableEq Arr := inferInstance
instance : Fintype Reg := inferInstance
instance : Fintype Arr := inferInstance

def search : Code := NatArrayPredicateSearch.search IndexedImageTest.test
  (.inl .value) IndexedImageTest.resultReg

theorem search_runs {n m k : ℕ} (S : State) (M : ℕ)
    (op : Fin n→Fin n→Fin n) (op' : Fin m→Fin m→Fin m)
    (identity : Fin n) (identity' : Fin m) (a : Fin k→Fin n)
    (hb : S.Bounded M) (hready : IndexedImageTest.Ready op op' identity identity' a S.left)
    (hlimit : S.scalar (.inr .limit)=m^k) (hroom : (n*m)*(n*m)≤M) :
    ∃t≤m^k*(10*(n*m)^3+8*(n*m)+19*k+n*(9*m+13)+19*n*n+49)+6,∃T,
      Runs (storageBound Reg Arr M) search S t T ∧ T.Bounded M ∧
      IndexedImageTest.Ready op op' identity identity' a T.left ∧
      T.scalar (.inr .found)=(if (NatArrayPredicateSearch.hit
        (IndexedImageTest.Accepts op op' identity identity' a) (m^k)).isSome then 1 else 0) := by
  have hM : 1≤M := by
    have hn := identity.isLt
    have hm := identity'.isLt
    have hp : 0<n*m := Nat.mul_pos (by omega) (by omega)
    nlinarith
  obtain ⟨t,ht,T,run,hT,hreadyT,hf,hr⟩ := NatArrayPredicateSearch.search_runs
    IndexedImageTest.test (.inl .value) IndexedImageTest.resultReg
    (IndexedImageTest.Ready op op' identity identity' a) (IndexedImageTest.Accepts op op' identity identity' a)
    S M (m^k) (10*(n*m)^3+8*(n*m)+19*k+n*(9*m+13)+19*n*n+40) hb hM hready
    (fun U i h => IndexedImageTest.ready_setValue h i)
    (fun U i hU hready hi hiLt => IndexedImageTest.test_runs U M op op' identity identity' a
      ⟨i,hiLt⟩ hU hready hi hroom) hlimit
  exact ⟨t,by omega,T,run,hT,hreadyT,hf⟩

variable {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H]

theorem search_correct {n m k : ℕ} (eG : Fin n≃G) (eH : Fin m≃H)
    (op : Fin n→Fin n→Fin n) (op' : Fin m→Fin m→Fin m)
    (hop : ∀x y,eG (op x y)=eG x*eG y) (hop' : ∀x y,eH (op' x y)=eH x*eH y)
    (identity : Fin n) (identity' : Fin m) (hid : eG identity=1) (hid' : eH identity'=1)
    (a : Fin k→Fin n) (ha : Refinement.Generates (eG ∘ a)) (hnm : n=m)
    (S : State) (M : ℕ) (hb : S.Bounded M)
    (hready : IndexedImageTest.Ready op op' identity identity' a S.left)
    (hlimit : S.scalar (.inr .limit)=m^k) (hroom : (n*m)*(n*m)≤M) :
    ∃t≤m^k*(10*(n*m)^3+8*(n*m)+19*k+n*(9*m+13)+19*n*n+49)+6,∃T,
      Runs (storageBound Reg Arr M) search S t T ∧ T.Bounded M ∧
      IndexedImageTest.Ready op op' identity identity' a T.left ∧
      T.scalar (.inr .found)≤1 ∧ (T.scalar (.inr .found)=1 ↔ Nonempty (G≃*H)) := by
  obtain ⟨t,ht,T,run,hT,hreadyT,hf⟩ := search_runs S M op op' identity identity' a hb hready hlimit hroom
  refine ⟨t,ht,T,run,hT,hreadyT,by rw [hf]; split_ifs <;> omega,?_⟩
  rw [hf]
  have hc := (NatArrayPredicateSearch.hit_isSome_iff (IndexedImageTest.Accepts op op' identity identity' a) (m^k)).trans
    ((NumericGroupImages.exists_index_iff op op' identity identity' a).trans
      (NumericGroupImages.exists_valid_iff eG eH op op' hop hop' identity identity' hid hid' a ha hnm))
  cases h : (NatArrayPredicateSearch.hit (IndexedImageTest.Accepts op op' identity identity' a) (m^k)).isSome <;>
    simpa [h] using hc

end GroupWL.MachinePrograms.GroupIsomorphismSearch
