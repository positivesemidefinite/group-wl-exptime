import GroupWL.MachinePrograms.PrefixSums

/-! Stable array compaction by Boolean flags, with an actual bounded scan. -/
namespace GroupWL.MachinePrograms.SelectArray
open NatArrayLanguage
set_option maxHeartbeats 2000000

inductive Reg where
  | length | index | todo | one | zero | selected | count | flag | value
  deriving DecidableEq,Fintype
inductive Arr where | flags | values | output
  deriving DecidableEq,Fintype
abbrev State := Store Reg Arr
abbrev Code := NatArrayLanguage.Program Reg Arr

def selectedPrefix (flags values : List ℕ) : ℕ → List ℕ
  | 0 => []
  | i+1 => selectedPrefix flags values i ++
      if flags[i]?.getD 0=0 then [] else [values[i]?.getD 0]

theorem selectedPrefix_length (flags values : List ℕ) (binary : ∀x∈flags,x≤1) (i : ℕ) :
    (selectedPrefix flags values i).length=FilterRanks.count flags i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have h := FilterRanks.read_le_one binary i
    simp only [selectedPrefix,List.length_append,FilterRanks.count,ih]
    split_ifs with hz
    · simp [hz]
    · have h1 : flags[i]?.getD 0=1 := by omega
      simp [h1]

theorem set_padding (xs : List ℕ) (k v : ℕ) (positive : 0<k) :
    (xs++List.replicate k 0).set xs.length v=
      (xs++[v])++List.replicate (k-1) 0 := by
  induction xs with
  | nil => cases k <;> simp_all [List.replicate_succ]
  | cons x xs ih => simpa [List.set_cons_succ,List.cons_append] using congrArg (List.cons x) ih

def chosenAtoms : List (Atom Reg Arr) := [
  .read .value .values .index,.write .output .count .value,.binary .add .count .count .one]
def cell : Code := .seq (.atom (.read .flag .flags .index))
  (.branch .flag (atoms chosenAtoms) .skip)
def program : Code := .seq (atoms [
  .const .one 1,.const .zero 0,.arrayLength .length .flags,
  .allocate .output .selected .zero,.const .count 0])
  (countedLoop .index .todo .length .one cell)

theorem cell_runs (S : State) (M i : ℕ) (bounded : S.Bounded M)
    (index : S.scalar .index=i) (one : S.scalar .one=1)
    (length : (S.array .values).length=(S.array .flags).length)
    (valid : i<(S.array .flags).length) (binary : ∀x∈S.array .flags,x≤1)
    (count : S.scalar .count=FilterRanks.count (S.array .flags) i)
    (output : S.array .output=selectedPrefix (S.array .flags) (S.array .values) i ++
      List.replicate (FilterRanks.count (S.array .flags) (S.array .flags).length-
        FilterRanks.count (S.array .flags) i) 0) :
    ∃t≤5,∃U,Runs (storageBound Reg Arr M) cell S t U ∧ U.Bounded M ∧
      U.scalar .count=FilterRanks.count (S.array .flags) (i+1) ∧
      U.array .output=selectedPrefix (S.array .flags) (S.array .values) (i+1) ++
        List.replicate (FilterRanks.count (S.array .flags) (S.array .flags).length-
          FilterRanks.count (S.array .flags) (i+1)) 0 := by
  have read := atom_runs bounded (Atom.read Reg.flag Arr.flags Reg.index) (by simpa [Atom.Valid,index] using valid) trivial
  let V := (Atom.read Reg.flag Arr.flags Reg.index).apply S
  have hV : V.Bounded M := Atom.apply_bounded bounded _ trivial
  have val : V.scalar .flag=(S.array .flags)[i]?.getD 0 := by simp [V,Atom.apply,index]
  by_cases hz : (S.array .flags)[i]?.getD 0=0
  · have hv : V.scalar .flag=0 := val.trans hz
    refine ⟨2,by omega,V,.seq read (.branch_zero hv (.skip (Store.size_le_of_bounded hV))),hV,?_,?_⟩
    · simp [V,Atom.apply,Store.setScalar,count,FilterRanks.count,hz]
    · simpa [selectedPrefix,FilterRanks.count,hz] using output
  · have hb := FilterRanks.read_le_one binary i
    have h1 : (S.array .flags)[i]?.getD 0=1 := by omega
    have hm := FilterRanks.count_mono (S.array .flags) (show i+1≤(S.array .flags).length by omega)
    have hc : FilterRanks.count (S.array .flags) i<FilterRanks.count (S.array .flags) (S.array .flags).length := by
      simpa [FilterRanks.count,h1] using hm
    have hn := FilterRanks.count_le binary (S.array .flags).length
    have hl := bounded.2.1 Arr.flags
    have ha : ValidAtoms M chosenAtoms V := by
      simp [chosenAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
        Store.setScalar,V,index,count,one,output,selectedPrefix_length _ _ binary]
      exact ⟨by omega,by omega,by omega⟩
    obtain ⟨run,hU⟩ := atoms_runs hV chosenAtoms ha
    refine ⟨5,le_rfl,applyAtoms chosenAtoms V,.seq read (.branch_nonzero (by rw [val,h1]; decide) run),hU,?_,?_⟩
    · simp [chosenAtoms,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,V,count,one,FilterRanks.count,h1]
    · have he := set_padding (selectedPrefix (S.array .flags) (S.array .values) i)
        (FilterRanks.count (S.array .flags) (S.array .flags).length-FilterRanks.count (S.array .flags) i)
        ((S.array .values)[i]?.getD 0) (by omega)
      rw [selectedPrefix_length _ _ binary] at he
      simp only [selectedPrefix,hz,↓reduceIte,FilterRanks.count,h1]
      simpa [chosenAtoms,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,V,index,count,one,output,Nat.sub_sub] using he

structure Invariant (bits entries : List ℕ) (M i : ℕ) (S : State) : Prop where
  bounded : S.Bounded M
  flags : S.array .flags=bits
  values : S.array .values=entries
  length : S.scalar .length=bits.length
  index : S.scalar .index=i
  todo : S.scalar .todo=bits.length-i
  one : S.scalar .one=1
  count : S.scalar .count=FilterRanks.count bits i
  output : S.array .output=selectedPrefix bits entries i ++
    List.replicate (FilterRanks.count bits bits.length-FilterRanks.count bits i) 0


theorem loop_runs (S : State) (M : ℕ) (bounded : S.Bounded M)
    (one : S.scalar .one=1) (length : S.scalar .length=(S.array .flags).length)
    (values : (S.array .values).length=(S.array .flags).length)
    (binary : ∀x∈S.array .flags,x≤1) (zero : S.scalar .count=0)
    (output : S.array .output=List.replicate (FilterRanks.count (S.array .flags) (S.array .flags).length) 0) :
    ∃t≤8*(S.array .flags).length+3,∃U,
      Runs (storageBound Reg Arr M) (countedLoop .index .todo .length .one cell) S t U ∧
      U.Bounded M ∧ U.array .output=selectedPrefix (S.array .flags) (S.array .values) (S.array .flags).length ∧
      U.scalar .count=FilterRanks.count (S.array .flags) (S.array .flags).length := by
  let S₀ := S.setScalar .todo (S.scalar .length)
  let S₁ := S₀.setScalar .index 0
  have h₀ : S₀.Bounded M := bounded.setScalar _ (bounded.1 .length)
  have h₁ : S₁.Bounded M := h₀.setScalar _ (Nat.zero_le _)
  let I := Invariant (S.array .flags) (S.array .values) M
  have start : I 0 S₁ := by
    refine ⟨h₁,rfl,rfl,?_,?_,?_,?_,?_,?_⟩
    · simpa [S₁,S₀] using length
    · simp [S₁]
    · simp [S₁,S₀,length]
    · simpa [S₁,S₀] using one
    · simpa [S₁,S₀,FilterRanks.count] using zero
    · simpa [S₁,S₀,FilterRanks.count,selectedPrefix] using output
  have control : ∀i≤(S.array .flags).length,∀T,I i T →
      T.scalar .index=i ∧ T.scalar .todo=(S.array .flags).length-i ∧ T.scalar .one=1 ∧
      T.size≤storageBound Reg Arr M := by
    intro i hi T hT
    exact ⟨hT.index,hT.todo,hT.one,Store.size_le_of_bounded hT.bounded⟩
  have body : ∀i<(S.array .flags).length,∀T,I i T →
      ∃t≤5,∃U,Runs (storageBound Reg Arr M) cell T t U ∧
        U.scalar .index=i ∧ U.scalar .todo=(S.array .flags).length-i ∧ U.scalar .one=1 ∧
        (U.setScalar .index (i+1)).size≤storageBound Reg Arr M ∧
        I (i+1) (advance .index .todo U) := by
    intro i hi T hT
    obtain ⟨t,ht,U,run,hU,hcount,hout⟩ := cell_runs T M i hT.bounded hT.index hT.one
      (by rw [hT.values,hT.flags]; exact values) (by rwa [hT.flags])
      (by rwa [hT.flags]) (by rw [hT.flags]; exact hT.count)
      (by rw [hT.flags,hT.values]; exact hT.output)
    simp only [hT.flags,hT.values] at hcount hout
    have hx : U.scalar .index=i := (run.scalar_eq_of_not_mem .index (by decide)).trans hT.index
    have ht' : U.scalar .todo=(S.array .flags).length-i := (run.scalar_eq_of_not_mem .todo (by decide)).trans hT.todo
    have ho : U.scalar .one=1 := (run.scalar_eq_of_not_mem .one (by decide)).trans hT.one
    have hiM : i+1≤M := le_trans (by omega) (bounded.2.1 .flags)
    have hmid := hU.setScalar Reg.index hiM
    have hfinal : (advance .index .todo U).Bounded M := by
      simpa only [advance,hx] using hmid.setScalar Reg.todo ((Nat.sub_le _ _).trans (hU.1 .todo))
    refine ⟨t,ht,U,run,hx,ht',ho,Store.size_le_of_bounded hmid,hfinal,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · exact (run.array_eq_of_not_mem .flags (by decide)).trans hT.flags
    · exact (run.array_eq_of_not_mem .values (by decide)).trans hT.values
    · simpa [advance,Store.setScalar] using (run.scalar_eq_of_not_mem .length (by decide)).trans hT.length
    · simp [advance,hx]
    · simp [advance,ht',Nat.sub_sub]
    · simpa [advance,Store.setScalar] using ho
    · simpa [advance,Store.setScalar] using hcount
    · exact hout
  obtain ⟨t,ht,U,run,hU⟩ := countedLoop_runs (storageBound Reg Arr M)
    Reg.index Reg.todo Reg.length Reg.one cell (S.array .flags).length 5 I S
    (Store.size_le_of_bounded bounded) (Store.size_le_of_bounded h₀) start control
    (by decide) (by decide) body
  refine ⟨t,by omega,U,run,hU.bounded,?_,hU.count⟩
  simpa using hU.output

theorem program_runs (S : State) (M : ℕ) (bounded : S.Bounded M) (room : 1≤M)
    (values : (S.array .values).length=(S.array .flags).length)
    (binary : ∀x∈S.array .flags,x≤1)
    (selected : S.scalar .selected=FilterRanks.count (S.array .flags) (S.array .flags).length) :
    ∃t≤8*(S.array .flags).length+8,∃U,
      Runs (storageBound Reg Arr M) program S t U ∧ U.Bounded M ∧
      U.array .output=selectedPrefix (S.array .flags) (S.array .values) (S.array .flags).length ∧
      U.scalar .count=S.scalar .selected := by
  let pre : List (Atom Reg Arr) := [.const .one 1,.const .zero 0,.arrayLength .length .flags,
    .allocate .output .selected .zero,.const .count 0]
  have valid : ValidAtoms M pre S := by simp [pre,ValidAtoms,Atom.Valid,Atom.SmallResult,room]
  obtain ⟨pr,hV⟩ := atoms_runs bounded pre valid
  let V := applyAtoms pre S
  have vf : V.array .flags=S.array .flags := rfl
  have vv : V.array .values=S.array .values := rfl
  obtain ⟨t,ht,U,run,hU,out,hc⟩ := loop_runs V M hV
    (by simp [V,pre,applyAtoms,Atom.apply,Store.setScalar,Store.setArray])
    (by simp [V,pre,applyAtoms,Atom.apply,Store.setScalar,Store.setArray])
    values binary
    (by simp [V,pre,applyAtoms,Atom.apply,Store.setScalar,Store.setArray])
    (by simp [V,pre,applyAtoms,Atom.apply,Store.setScalar,Store.setArray,selected])
  simp only [vf,vv] at ht out hc
  exact ⟨5+t,by omega,U,.seq pr run,hU,out,hc.trans selected.symm⟩

end GroupWL.MachinePrograms.SelectArray
