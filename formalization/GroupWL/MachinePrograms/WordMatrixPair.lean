import GroupWL.MachinePrograms.WordMatrixPrograms

/-! The concrete pair comparator computes the Version-II initial relation. -/
namespace GroupWL.MachinePrograms.WordMatrixPrograms
open NatArrayLanguage
open WordMatrixSemantics
open InitialMatrixPrograms (selectBase selectMul selectTable selectCode pointCode)
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false

variable {G H : Type} [Group G] [Group H] [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H]
variable {n m k : ℕ}

theorem pointTuple_word (e : G≃Fin n) (e' : H≃Fin m) (i : Fin (n^k+m^k)) :
    List.ofFn (fun j : Fin k=>(selectEquiv e e' (decide (n^k ≤ i.val)) (pointTuple e e' i j)).val)=
      IndexedRefinement.vectorWord (selectBase n m (decide (n^k ≤ i.val))) k
        (selectCode (n^k) i.val (decide (n^k ≤ i.val))) := by
  simp only [pointTuple,Function.comp_apply,Equiv.apply_symm_apply]
  rfl

theorem comparePair_runs (e : G≃Fin n) (e' : H≃Fin m)
    (f : Fin n→Fin n→Fin n) (g : Fin m→Fin m→Fin m)
    (hf : ∀x y,e.symm (f x y)=e.symm x*e.symm y)
    (hg : ∀x y,e'.symm (g x y)=e'.symm x*e'.symm y)
    (leftZero : (e 1).val=0) (rightZero : (e' 1).val=0)
    (i j : Fin (n^k+m^k)) (S : State) (B : ℕ) (bounded : S.Bounded B)
    (hn : S.scalar (wl .leftCount)=n) (hm : S.scalar (wl .rightCount)=m)
    (hcut : S.scalar (wl .vectorLimit)=n^k)
    (hi : S.scalar (wl .row)=i.val) (hj : S.scalar (wl .column)=j.val)
    (hk : S.scalar (wl .arity)=k) (hone : S.scalar (wl .one)=1)
    (hlen : (S.array (array .vector)).length=k)
    (ht : S.array (array .fanouts)=GroupInitial.tableWord f)
    (ht' : S.array (array .targets)=GroupInitial.tableWord g)
    (room : (max n m)^4≤B) :
    ∃t≤200*(B+1)^3,∃T,Runs (storageBound Reg Arr B) comparePair S t T ∧ T.Bounded B ∧
      T.scalar (base .result)≤1 ∧ (T.scalar (base .result)=1 ↔ initialEq e e' i j=true) ∧
      (T.array (array .vector)).length=k := by
  have hnpos : 0<n := by have := (e 1).isLt;omega
  have hmpos : 0<m := by have := (e' 1).isLt;omega
  have hmax : 1≤max n m := by omega
  have h1 : 1≤B := (one_le_pow₀ hmax).trans room
  obtain ⟨u,hu,U,load,hU,leftSize,rightSize,leftTable,rightTable,leftTuple,rightTuple,vector⟩ :=
    InitialMatrixPrograms.loadPair_runs S.left B n m k (n^k) i.val j.val bounded.left hn hm hcut hi hj
      hk hone hlen hnpos hmpos h1 _ _ ht ht'
  let V := U.join S.right
  have hV : V.Bounded B := hU.join bounded.right
  let bi := decide (n^k ≤ i.val)
  let bj := decide (n^k ≤ j.val)
  let ei := selectEquiv e e' bi
  let ej := selectEquiv e e' bj
  have hom (b : Bool) : ∀x y,(selectEquiv e e' b).symm (selectMul f g b x y)=
      (selectEquiv e e' b).symm x*(selectEquiv e e' b).symm y := by
    cases b
    · exact hf
    · exact hg
  have zero (b : Bool) : (selectEquiv e e' b 1).val=0 := by
    cases b
    · exact leftZero
    · exact rightZero
  have leftData : V.array (data .leftTuple)=List.ofFn (fun x : Fin k=>(ei (pointTuple e e' i x)).val) := by
    rw [pointTuple_word]
    exact leftTuple
  have rightData : V.array (data .rightTuple)=List.ofFn (fun x : Fin k=>(ej (pointTuple e e' j x)).val) := by
    rw [pointTuple_word]
    exact rightTuple
  have pairRoom : (selectBase n m bi*selectBase n m bj)*(selectBase n m bi*selectBase n m bj)≤B := by
    have hi : selectBase n m bi≤max n m := by cases bi <;> simp [selectBase]
    have hj : selectBase n m bj≤max n m := by cases bj <;> simp [selectBase]
    calc
      _ ≤ (max n m*max n m)*(max n m*max n m) := by gcongr
      _ = (max n m)^4 := by ring
      _ ≤ B := room
  have leftTable' : V.array (data .leftTable)=GroupInitial.tableWord (selectMul f g bi) :=
    leftTable.trans (InitialMatrixPrograms.selectMul_tableWord f g bi).symm
  have rightTable' : V.array (data .rightTable)=GroupInitial.tableWord (selectMul f g bj) :=
    rightTable.trans (InitialMatrixPrograms.selectMul_tableWord f g bj).symm
  obtain ⟨t,htime,T,compare,hT,valid,result⟩ := compareLoaded_runs ei ej (selectMul f g bi) (selectMul f g bj)
    (hom bi) (hom bj) (zero bi) (zero bj) (pointTuple e e' i) (pointTuple e e' j) V B hV
    leftSize rightSize leftTable' rightTable' leftData rightData pairRoom
  have hkB : k≤B := by simpa only [hk] using bounded.1 (wl .arity)
  have selectPositive (b : Bool) : 0<selectBase n m b := by
    cases b
    · exact hnpos
    · exact hmpos
  have pairPositive : 0<selectBase n m bi*selectBase n m bj :=
    Nat.mul_pos (selectPositive bi) (selectPositive bj)
  have pairBound : selectBase n m bi*selectBase n m bj≤B := by nlinarith
  have squareBound := Nat.pow_le_pow_left pairBound 2
  have cubeBound := Nat.pow_le_pow_left pairBound 3
  refine ⟨u+t,by nlinarith,T,.seq (load.left_bounded bounded) compare,hT,valid,result,?_⟩
  exact congrArg List.length (compare.array_eq_of_not_mem (array .vector) (by decide +kernel)) |>.trans vector

end GroupWL.MachinePrograms.WordMatrixPrograms
